/*
 * Copyright (C) 2007 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <linux/input.h>
#include <stdio.h>
#include <dirent.h>
#include <stdlib.h>
#include <string.h>
#include <sys/reboot.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <termios.h> 

#include "bootloader.h"
#include "commands.h"
#include "common.h"
#include "cutils/properties.h"
#include "firmware.h"
#include "install.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "roots.h"

static const struct option OPTIONS[] = {
  { "send_intent", required_argument, NULL, 's' },
  { "update_package", required_argument, NULL, 'u' },
  { "wipe_data", no_argument, NULL, 'w' },
  { "wipe_cache", no_argument, NULL, 'c' },
};

static const char *COMMAND_FILE = "CACHE:recovery/command";
static const char *INTENT_FILE = "CACHE:recovery/intent";
static const char *LOG_FILE = "CACHE:recovery/log";
static const char *SDCARD_PACKAGE_FILE = "SDCARD:update.zip";
static const char *SDCARD_PATH = "SDCARD:";
static const char *THEMES_PATH = "THEMES:";
#define SDCARD_PATH_LENGTH 20
#define THEMES_PATH_LENGTH 20
static const char *TEMPORARY_LOG_FILE = "/sdcard/recovery.log";

/*
 * The recovery tool communicates with the main system through /cache files.
 *   /cache/recovery/command - INPUT - command line for tool, one arg per line
 *   /cache/recovery/log - OUTPUT - combined log file from recovery run(s)
 *   /cache/recovery/intent - OUTPUT - intent that was passed in
 *
 * The arguments which may be supplied in the recovery.command file:
 *   --send_intent=anystring - write the text out to recovery.intent
 *   --update_package=root:path - verify install an OTA package file
 *   --wipe_data - erase user data (and cache), then reboot
 *   --wipe_cache - wipe cache (but not user data), then reboot
 *
 * After completing, we remove /cache/recovery/command and reboot.
 * Arguments may also be supplied in the bootloader control block (BCB).
 * These important scenarios must be safely restartable at any point:
 *
 * FACTORY RESET
 * 1. user selects "factory reset"
 * 2. main system writes "--wipe_data" to /cache/recovery/command
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--wipe_data"
 *    -- after this, rebooting will restart the erase --
 * 5. erase_root() reformats /data
 * 6. erase_root() reformats /cache
 * 7. finish_recovery() erases BCB
 *    -- after this, rebooting will restart the main system --
 * 8. main() calls reboot() to boot main system
 *
 * OTA INSTALL
 * 1. main system downloads OTA package to /cache/some-filename.zip
 * 2. main system writes "--update_package=CACHE:some-filename.zip"
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--update_package=..."
 *    -- after this, rebooting will attempt to reinstall the update --
 * 5. install_package() attempts to install the update
 *    NOTE: the package install must itself be restartable from any point
 * 6. finish_recovery() erases BCB
 *    -- after this, rebooting will (try to) restart the main system --
 * 7. ** if install failed **
 *    7a. prompt_and_wait() shows an error icon and waits for the user
 *    7b; the user reboots (pulling the battery, etc) into the main system
 * 8. main() calls maybe_install_firmware_update()
 *    ** if the update contained radio/hboot firmware **:
 *    8a. m_i_f_u() writes BCB with "boot-recovery" and "--wipe_cache"
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8b. m_i_f_u() writes firmware image into raw cache partition
 *    8c. m_i_f_u() writes BCB with "update-radio/hboot" and "--wipe_cache"
 *        -- after this, rebooting will attempt to reinstall firmware --
 *    8d. bootloader tries to flash firmware
 *    8e. bootloader writes BCB with "boot-recovery" (keeping "--wipe_cache")
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8f. erase_root() reformats /cache
 *    8g. finish_recovery() erases BCB
 *        -- after this, rebooting will (try to) restart the main system --
 * 9. main() calls reboot() to boot main system
 */

static const int MAX_ARG_LENGTH = 4096;
static const int MAX_ARGS = 100;

static int do_reboot = 1;


// drakaz : binary location
#define NANDROID_BIN "/tmp/RECTOOLS/nandroid-mobile.sh"
#define MKE2FS_BIN "/tmp/RECTOOLS/mke2fs"
#define E2FSCK_BIN "/tmp/RECTOOLS/e2fsck"
#define SDTOOLS "/tmp/RECTOOLS/sdtools.sh"
#define FIX_PERMS_BIN "/tmp/RECTOOLS/fix_permissions.sh"
#define BACKUP_DATA_BIN "/tmp/RECTOOLS/backupdata.sh"

// Pour emulateur..
//#define SYSTEME_PART "/dev/block/mtdblock0"
//#define DATA_PART "/dev/block/mtdblock1"

// drakaz : define galaxy partitions
#define SYSTEME_PART "/dev/block/mtdblock1"
#define DATA_PART "/dev/block/mmcblk0p1"


// open a file given in root:path format, mounting partitions as necessary
static FILE*
fopen_root_path(const char *root_path, const char *mode) {
    if (ensure_root_path_mounted(root_path) != 0) {
        LOGE("Can't mount %s\n", root_path);
        return NULL;
    }

    char path[PATH_MAX] = "";
    if (translate_root_path(root_path, path, sizeof(path)) == NULL) {
        LOGE("Bad path %s\n", root_path);
        return NULL;
    }

    // When writing, try to create the containing directory, if necessary.
    // Use generous permissions, the system (init.rc) will reset them.
    if (strchr("wa", mode[0])) dirCreateHierarchy(path, 0777, NULL, 1);

    FILE *fp = fopen(path, mode);
    return fp;
}

// close a file, log an error if the error indicator is set
static void
check_and_fclose(FILE *fp, const char *name) {
    fflush(fp);
    if (ferror(fp)) LOGE("Error in %s\n(%s)\n", name, strerror(errno));
    fclose(fp);
}

// command line args come from, in decreasing precedence:
//   - the actual command line
//   - the bootloader control block (one per line, after "recovery")
//   - the contents of COMMAND_FILE (one per line)
static void
get_args(int *argc, char ***argv) {
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    get_bootloader_message(&boot);  // this may fail, leaving a zeroed structure

    if (boot.command[0] != 0 && boot.command[0] != 255) {
        LOGI("Boot command: %.*s\n", sizeof(boot.command), boot.command);
    }

    if (boot.status[0] != 0 && boot.status[0] != 255) {
        LOGI("Boot status: %.*s\n", sizeof(boot.status), boot.status);
    }

    // --- if arguments weren't supplied, look in the bootloader control block
    if (*argc <= 1) {
        boot.recovery[sizeof(boot.recovery) - 1] = '\0';  // Ensure termination
        const char *arg = strtok(boot.recovery, "\n");
        if (arg != NULL && !strcmp(arg, "recovery")) {
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = strdup(arg);
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if ((arg = strtok(NULL, "\n")) == NULL) break;
                (*argv)[*argc] = strdup(arg);
            }
            LOGI("Got arguments from boot message\n");
        } else if (boot.recovery[0] != 0 && boot.recovery[0] != 255) {
            LOGE("Bad boot message\n\"%.20s\"\n", boot.recovery);
        }
    }

    // --- if that doesn't work, try the command file
    if (*argc <= 1) {
        FILE *fp = fopen_root_path(COMMAND_FILE, "r");
        if (fp != NULL) {
            char *argv0 = (*argv)[0];
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = argv0;  // use the same program name

            char buf[MAX_ARG_LENGTH];
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if (!fgets(buf, sizeof(buf), fp)) break;
                (*argv)[*argc] = strdup(strtok(buf, "\r\n"));  // Strip newline.
            }

            check_and_fclose(fp, COMMAND_FILE);
            LOGI("Got arguments from %s\n", COMMAND_FILE);
        }
    }

    // --> write the arguments we have back into the bootloader control block
    // always boot into recovery after this (until finish_recovery() is called)
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));
    int i;
    for (i = 1; i < *argc; ++i) {
        strlcat(boot.recovery, (*argv)[i], sizeof(boot.recovery));
        strlcat(boot.recovery, "\n", sizeof(boot.recovery));
    }
    set_bootloader_message(&boot);
}


// clear the recovery command and prepare to boot a (hopefully working) system,
// copy our log file to cache as well (for the system to read), and
// record any intent we were asked to communicate back to the system.
// this function is idempotent: call it as many times as you like.
static void
finish_recovery(const char *send_intent)
{
    // By this point, we're ready to return to the main system...
    if (send_intent != NULL) {
        FILE *fp = fopen_root_path(INTENT_FILE, "w");
        if (fp == NULL) {
            LOGE("Can't open %s\n", INTENT_FILE);
        } else {
            fputs(send_intent, fp);
            check_and_fclose(fp, INTENT_FILE);
        }
    }

    // Copy logs to cache so the system can find out what happened.
    FILE *log = fopen_root_path(LOG_FILE, "a");
    if (log == NULL) {
        LOGE("Can't open %s\n", LOG_FILE);
    } else {
        FILE *tmplog = fopen(TEMPORARY_LOG_FILE, "r");
        if (tmplog == NULL) {
            LOGE("Can't open %s\n", TEMPORARY_LOG_FILE);
        } else {
            static long tmplog_offset = 0;
            fseek(tmplog, tmplog_offset, SEEK_SET);  // Since last write
            char buf[4096];
            while (fgets(buf, sizeof(buf), tmplog)) fputs(buf, log);
            tmplog_offset = ftell(tmplog);
            check_and_fclose(tmplog, TEMPORARY_LOG_FILE);
        }
        check_and_fclose(log, LOG_FILE);
    }

    // Reset the bootloader message to revert to a normal main system boot.
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    set_bootloader_message(&boot);

    // Remove the command file, so recovery won't repeat indefinitely.
    char path[PATH_MAX] = "";
    if (ensure_root_path_mounted(COMMAND_FILE) != 0 ||
        translate_root_path(COMMAND_FILE, path, sizeof(path)) == NULL ||
        (unlink(path) && errno != ENOENT)) {
        LOGW("Can't unlink %s\n", COMMAND_FILE);
    }

    sync();  // For good measure.
}

#define TEST_AMEND 0
#if TEST_AMEND
static void
test_amend()
{
    extern int test_symtab(void);
    extern int test_cmd_fn(void);
    int ret;
    LOGD("Testing symtab...\n");
    ret = test_symtab();
    LOGD("  returned %d\n", ret);
    LOGD("Testing cmd_fn...\n");
    ret = test_cmd_fn();
    LOGD("  returned %d\n", ret);
}
#endif  // TEST_AMEND

static int
erase_root(const char *root)
{
    ui_set_background(BACKGROUND_ICON_INSTALLING);
    ui_show_indeterminate_progress();
    ui_print("Formatting %s...\n", root);
    return format_root_device(root);
}

static void
choose_update_file()
{
    static char* headers[] = { "Choose update ZIP file",
                               "",
                               "Use up/down to highlight;",
                               "OK to select",
                               "",
                               NULL };

    char path[PATH_MAX] = "";
    DIR *dir;
    struct dirent *de;
    char **files;
    int total = 0;
    int i;

    if (ensure_root_path_mounted(SDCARD_PATH) != 0) {
        LOGE("Can't mount %s\n", SDCARD_PATH);
        return;
    }

    if (translate_root_path(SDCARD_PATH, path, sizeof(path)) == NULL) {
        LOGE("Bad path %s", path);
        return;
    }

    dir = opendir(path);
    if (dir == NULL) {
        LOGE("Couldn't open directory %s", path);
        return;
    }

    /* count how many files we're looking at */
    while ((de = readdir(dir)) != NULL) {
        char *extension = strrchr(de->d_name, '.');
        if (extension == NULL || de->d_name[0] == '.') {
            continue;
        } else if (!strcasecmp(extension, ".zip")) {
            total++;
        }
    }

    /* allocate the array for the file list menu */
    files = (char **) malloc((total + 1) * sizeof(*files));
    files[total] = NULL;

    /* set it up for the second pass */
    rewinddir(dir);

    /* put the names in the array for the menu */
    i = 0;
    while ((de = readdir(dir)) != NULL) {
        char *extension = strrchr(de->d_name, '.');
        if (extension == NULL || de->d_name[0] == '.') {
            continue;
        } else if (!strcasecmp(extension, ".zip")) {
            files[i] = (char *) malloc(SDCARD_PATH_LENGTH + strlen(de->d_name) + 1);
            strcpy(files[i], SDCARD_PATH);
            strcat(files[i], de->d_name);
            i++;
        }
    }

    /* close directory handle */
    if (closedir(dir) < 0) {
        LOGE("Failure closing directory %s", path);
        goto out;
    }

    ui_start_menu(headers, files);
    int selected = 0;
    int chosen_item = -1;

    finish_recovery(NULL);
    ui_reset_progress();
    for (;;) {
        int key = ui_wait_key();
        int visible = ui_text_visible();

        if (key == KEY_DREAM_BACK) {
            break;
        } else if ((key == KEY_DOWN || key == KEY_VOLUMEDOWN) && visible) {
            ++selected;
            selected = ui_menu_select(selected);
        } else if ((key == KEY_UP || key == KEY_VOLUMEUP) && visible) {
            --selected;
            selected = ui_menu_select(selected);
        } else if ((key == BTN_MOUSE || key == KEY_I7500_CENTER) && visible) {
            chosen_item = selected;
        }

        if (chosen_item >= 0) {
            // turn off the menu, letting ui_print() to scroll output
            // on the screen.
            ui_end_menu();

            ui_print("\n-- Installing new image!");
            ui_print("\n-- Press HOME to confirm, or");
            ui_print("\n-- any other key to abort\n\n");
            int confirm_apply = ui_wait_key();
            if (confirm_apply == KEY_DREAM_HOME) {
                ui_print("\nInstalling from sdcard...\n");
                int status = install_package(files[chosen_item]);
                if (status != INSTALL_SUCCESS) {
                    ui_set_background(BACKGROUND_ICON_ERROR);
                    ui_print("Installation failed\n");
                } else if (!ui_text_visible()) {
                    break;  // reboot if logs aren't visible
                } else {
                    if (firmware_update_pending()) {
                        ui_print("\nReboot\n"
                                 "to complete installation\n");
                    } else {
                        ui_print("\nInstall from sdcard complete\n");
                    }
                }
            } else {
                ui_print("\nInstallation failed");
            }
            if (!ui_text_visible()) break;
            break;
        }
    }

out:

    for (i = 0; i < total; i++) {
        free(files[i]);
    }
    free(files);
}

static void
choose_theme_file()
{
    static char* headers[] = { "Choose theme ZIP file",
                               "",
                               "Use up/down to highlight;",
                               "click OK to select.",
                               "",
                               NULL };

// Mount system partition
    ui_print("\nRemounting system partition in rw..");
    pid_t pidtheme1 = fork();
    if (pidtheme1 == 0) {
	char *argstheme1[] = { "mount", "/system", NULL };
	execv("/sbin/busybox", argstheme1);
        fprintf(stderr, "Can't mount %s\n(%s)\n", SYSTEME_PART, strerror(errno));
        _exit(-1);
    }
    int statustheme1;
    while (waitpid(pidtheme1, &statustheme1, WNOHANG) == 0) {
    ui_print(".");
    sleep(1);
    }
                            
// Remount system partition in rw
    pid_t pidtheme2 = fork();
    if (pidtheme2 == 0) {
	char *argstheme2[] = { "mount", "-o", "remount,rw", SYSTEME_PART, "/system", NULL };
	execv("/sbin/busybox", argstheme2);
        fprintf(stderr, "Can't remount %s\n(%s) in rw\n", SYSTEME_PART, strerror(errno));
        _exit(-1);
    }
    int statustheme2;
    while (waitpid(pidtheme2, &statustheme2, WNOHANG) == 0) {
    	ui_print(".");
    	sleep(1);
    }
    ui_print("OK\n");

    char path[PATH_MAX] = "";
    DIR *dir;
    struct dirent *de;
    char **files;
    int total = 0;
    int i;

    if (ensure_root_path_mounted(THEMES_PATH) != 0) {
        LOGE("Can't mount %s\n", THEMES_PATH);
        return;
    }

    if (translate_root_path(THEMES_PATH, path, sizeof(path)) == NULL) {
        LOGE("Bad path %s", path);
        return;
    }

    dir = opendir(path);
    if (dir == NULL) {
        LOGE("Couldn't open directory %s", path);
        return;
    }

    /* count how many files we're looking at */
    while ((de = readdir(dir)) != NULL) {
        char *extension = strrchr(de->d_name, '.');
        if (extension == NULL || de->d_name[0] == '.') {
            continue;
        } else if (!strcasecmp(extension, ".zip")) {
            total++;
        }
    }

    /* allocate the array for the file list menu */
    files = (char **) malloc((total + 1) * sizeof(*files));
    files[total] = NULL;

    /* set it up for the second pass */
    rewinddir(dir);

    /* put the names in the array for the menu */
    i = 0;
    while ((de = readdir(dir)) != NULL) {
        char *extension = strrchr(de->d_name, '.');
        if (extension == NULL || de->d_name[0] == '.') {
            continue;
        } else if (!strcasecmp(extension, ".zip")) {
            files[i] = (char *) malloc(THEMES_PATH_LENGTH + strlen(de->d_name) + 1);
            strcpy(files[i], THEMES_PATH);
            strcat(files[i], de->d_name);
            i++;
        }
    }

    /* close directory handle */
    if (closedir(dir) < 0) {
        LOGE("Failure closing directory %s", path);
        goto out;
    }

    ui_start_menu(headers, files);
    int selected = 0;
    int chosen_item = -1;

    finish_recovery(NULL);
    ui_reset_progress();
    for (;;) {
        int key = ui_wait_key();
        int visible = ui_text_visible();

        if (key == KEY_DREAM_BACK) {
            break;
        } else if ((key == KEY_DOWN || key == KEY_VOLUMEDOWN) && visible) {
            ++selected;
            selected = ui_menu_select(selected);
        } else if ((key == KEY_UP || key == KEY_VOLUMEUP) && visible) {
            --selected;
            selected = ui_menu_select(selected);
        } else if ((key == BTN_MOUSE || key == KEY_I7500_CENTER) && visible) {
            chosen_item = selected;
        }

        if (chosen_item >= 0) {
            // turn off the menu, letting ui_print() to scroll output
            // on the screen.
            ui_end_menu();

            ui_print("\n-- Installing new theme!");
            ui_print("\n-- Press HOME to confirm, or");
            ui_print("\n-- any other key to abort..");
            int confirm_apply = ui_wait_key();
            if (confirm_apply == KEY_DREAM_HOME) {
                ui_print("\n-- Install new theme from sdcard...\n");
                int status = install_package(files[chosen_item]);
                if (status != INSTALL_SUCCESS) {
                    ui_set_background(BACKGROUND_ICON_ERROR);
                    ui_print("Installation aborted.\n");
                } else if (!ui_text_visible()) {
                    break;  // reboot if logs aren't visible
                } else {
                    if (firmware_update_pending()) {
                        ui_print("\nReboot via menu\n"
                                 "to complete installation.\n");
                    } else {
                        ui_print("\nInstall new theme from sdcard complete.\n");
                    }
                }
            } else {
                ui_print("\nInstallation aborted.\n");
            }
            if (!ui_text_visible()) break;
            break;
        }
    }

out:

    for (i = 0; i < total; i++) {
        free(files[i]);
    }
    free(files);
}

static void
prompt_and_wait()
{
// drakaz : new headers
    static char* headers[] = { "Android system recovery " EXPAND(RECOVERY_API_VERSION),
			"     --- Galaxy Version ---",
                        "",
                        NULL };

// drakaz : add news functions
// these constants correspond to elements of the items[] list.
#define ITEM_REBOOT        0
#define ITEM_APPLY_SDCARD  1
#define ITEM_APPLY_UPDATE  2
#define ITEM_APPLY_THEME   3
#define ITEM_GRESTORE	   4
#define UMS_ON	   	   5
#define UMS_OFF		   6
//#define ITEM_BACKUP_DATA   7
//#define ITEM_RESTORE_DATA  8
#define ITEM_NANDROID      7
#define ITEM_RESTORE       8
#define ITEM_SU_ON	   9
#define ITEM_SU_OFF	   10
#define ITEM_WIPE_DATA     11
#define ITEM_FSCK          12
#define ITEM_SD_SWAP_ON    13
#define ITEM_SD_SWAP_OFF   14
#define FIX_PERMS	   15
#define ITEM_DELETE	   16
#define CONVERT_DATA_EXT4  17





// drakaz : delete console access because of non existent keyboard on galaxy
    static char* items[] = { "Reboot system now",
                             "Apply sdcard:update.zip",
                             "Apply any zip from sd",
			     "Apply a theme from sd",
			     "Restore G.Apps",
			     "Mount SD(s) on PC",
			     "Umount SD(s) from PC",
//			     "Backup market+sms/mms db",
//			     "Restore market+sms/mms db",
                             "Nandroid backup",
                             "Restore latest backup",
			     "Enable root (su)",
	                     "Disable root (su)",
			     "Wipe data/factory reset",
			     "Check ext3 filesystem on /data",
			     "Format ext. SD : swap+fat32",
                             "Format ext. SD : fat32",
			     "Fix packages permissions",
//			     "Delete oldest backup",
                             NULL };

    ui_start_menu(headers, items);
    int selected = 0;
    int chosen_item = -1;

    finish_recovery(NULL);
    ui_reset_progress();
    for (;;) {
        int key = ui_wait_key();
        int alt = ui_key_pressed(KEY_LEFTALT) || ui_key_pressed(KEY_RIGHTALT);
        int visible = ui_text_visible();

        if (key == KEY_DREAM_BACK && ui_key_pressed(KEY_DREAM_HOME)) {
            // Wait for the keys to be released, to avoid triggering
            // special boot modes (like coming back into recovery!).
            while (ui_key_pressed(KEY_DREAM_BACK) ||
                   ui_key_pressed(KEY_DREAM_HOME)) {
                usleep(1000);
            }
            chosen_item = ITEM_REBOOT;
        } else if (alt && key == KEY_W) {
            chosen_item = ITEM_WIPE_DATA;
        } else if (alt && key == KEY_S) {
            chosen_item = ITEM_APPLY_SDCARD;
        } else if (alt && key == KEY_A) {
            chosen_item = ITEM_APPLY_UPDATE;
        } else if (alt && key == KEY_B) {
            chosen_item = ITEM_NANDROID;
        } else if (alt && key == KEY_R) {
            chosen_item = ITEM_RESTORE;
        } else if ((key == KEY_DOWN || key == KEY_VOLUMEDOWN) && visible) {
            ++selected;
            selected = ui_menu_select(selected);
        } else if ((key == KEY_UP || key == KEY_VOLUMEUP) && visible) {
            --selected;
            selected = ui_menu_select(selected);
        } else if ((key == BTN_MOUSE || key == KEY_I7500_CENTER) && visible) {
            chosen_item = selected;
        } 

        if (chosen_item >= 0) {
            // turn off the menu, letting ui_print() to scroll output
            // on the screen.
            ui_end_menu();

            switch (chosen_item) {
                case ITEM_REBOOT:
                    return;

// Apply sdcard update.zip
		case ITEM_APPLY_SDCARD:
                    ui_print("\n-- Installing new image!");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort..");
                    int confirm_apply = ui_wait_key();
                    if (confirm_apply == KEY_DREAM_HOME) {
                        ui_print("\n-- Install from sdcard...\n");
                        int status = install_package(SDCARD_PACKAGE_FILE);
                        if (status != INSTALL_SUCCESS) {
                            ui_set_background(BACKGROUND_ICON_ERROR);
                            ui_print("Installation aborted.\n");
                        } else if (!ui_text_visible()) {
                            return;  // reboot if logs aren't visible
                        } else {

                            if (firmware_update_pending()) {
                                ui_print("\nReboot via menu\n"
                                            "to complete installation.\n");
                            } else {
                                ui_print("\nInstall from sdcard complete.\n");
                            }
                        }
                    } else {
                        ui_print("\nInstallation aborted.\n");
                    }
                    if (!ui_text_visible()) return;
                    break;

// Apply any update from SD
                case ITEM_APPLY_UPDATE:
                    choose_update_file();
                    break;

// Apply any theme from SD
                case ITEM_APPLY_THEME:
                    choose_theme_file();
                    break;


// drakaz : launch the shell script which restore Google applications and library from official Galaxy update
// This script must be updated at each official update and new rom because of signature/md5
		case ITEM_GRESTORE:
		    ui_print("\n-- Restoring Google apps");
		    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort..");
 		    int confirm_grestore = ui_wait_key();
                    if (confirm_grestore == KEY_DREAM_HOME) {
 		    	ui_print("\n-- Restore started...\n");
			pid_t pidf = fork();
                    if (pidf == 0) {
			char *args[] = { "/sbin/sh", "/tmp/RECTOOLS/gfiles.sh", "oneinall", NULL };
			execv("/sbin/sh", args);
                        fprintf(stderr, "Unable to start the restore script\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status;
                    while (waitpid(pidf, &fsck_status, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
		    sync();
		    if (!WIFEXITED(fsck_status) || (WEXITSTATUS(fsck_status) != 0)) {		  		
			ui_print("\nRestore aborted : see /sdcard/recovery.log\n");
                    } else {
                        ui_print("\nRestore completed\n");
                    }

		    sync();

                    if (!ui_text_visible()) {
			return;
		    }
	            }
		    break;

// drakaz : mount internal and external SD as mass storage device in recovery mode
		    case UMS_ON:
                        ui_print("\nMounting SD(s)...");
                        
			   FILE *umsdonfile;
			   umsdonfile = fopen("/sys/devices/platform/usb_mass_storage/lun0/file","w"); 
			   fprintf(umsdonfile,"%s"," "); 
			   fclose(umsdonfile);
			   FILE *umsdonfile2;
			   umsdonfile2 = fopen("/sys/devices/platform/usb_mass_storage/lun1/file","w"); 
			   fprintf(umsdonfile2,"%s"," "); 
			   fclose(umsdonfile2);
				
			   sleep(5);

			   FILE *intsdfile;
			   intsdfile = fopen("/sys/devices/platform/usb_mass_storage/lun0/file","w"); 
			   fprintf(intsdfile,"%s","/dev/block/mmcblk0p2"); 
			   fclose(intsdfile);
			   FILE *intsdfile2;
			   intsdfile2 = fopen("/sys/devices/platform/usb_mass_storage/lun1/file","w"); 
			   fprintf(intsdfile2,"%s","/dev/block/mmcblk1"); 
			   fclose(intsdfile2);
			   

                           ui_print("SD(s) mounted !\n\n");
                    if (!ui_text_visible()) return;
                    break;	

// drakaz : umount internal and external SD
		case UMS_OFF:
                        ui_print("\nUnmounting SD(s)...");
		          
                           FILE *umsdfile;
			   umsdfile = fopen("/sys/devices/platform/usb_mass_storage/lun0/file","w"); 
			   fprintf(umsdfile,"%s"," "); 
			   fclose(umsdfile);
			   FILE *umsdfile2;
			   umsdfile2 = fopen("/sys/devices/platform/usb_mass_storage/lun1/file","w"); 
			   fprintf(umsdfile2,"%s"," "); 
			   fclose(umsdfile2);
                           ui_print("SD(s) unmounted !\n\n");

                    if (!ui_text_visible()) return;
                    break;	

// drakaz : launch data backup script
/*	    	case ITEM_BACKUP_DATA:
                    if (ensure_root_path_mounted("SDCARD:") != 0) {
                        ui_print("\nCan't mount sdcard\n");
                    } else {
                        ui_print("\nPerforming app data backup");
                        pid_t pid = fork();
                        if (pid == 0) {
                            char *args[] = {"/sbin/sh", BACKUP_DATA_BIN, "backup", NULL};
                            execv("/sbin/sh", args);
                            fprintf(stderr, "E:Can't run %s\n(%s)\n", NANDROID_BIN, strerror(errno));
                            _exit(-1);
                        }

                        int status;

                        while (waitpid(pid, &status, WNOHANG) == 0) {
                            ui_print(".");
                            sleep(1);
                        }
                        ui_print("\n");

                        if (!WIFEXITED(status) || (WEXITSTATUS(status) != 0)) {
                             ui_print("\nError running data backup. Backup not performed.\n\n");
                        } else {
                             ui_print("\nBackup complete!\n\n");
                        }
                    }
                    break;

// drakaz : launch data restore script
	    	case ITEM_RESTORE_DATA:
                    if (ensure_root_path_mounted("SDCARD:") != 0) {
                        ui_print("\nCan't mount sdcard\n");
                    } else {
                        ui_print("\nPerforming app data restore");
                        pid_t pid = fork();
                        if (pid == 0) {
                            char *args[] = {"/sbin/sh", BACKUP_DATA_BIN, "restore", NULL};
                            execv("/sbin/sh", args);
                            fprintf(stderr, "E:Can't run %s\n(%s)\n", BACKUP_DATA_BIN, strerror(errno));
                            _exit(-1);
                        }

                        int status;

                        while (waitpid(pid, &status, WNOHANG) == 0) {
                            ui_print(".");
                            sleep(1);
                        }
                        ui_print("\n");

                        if (!WIFEXITED(status) || (WEXITSTATUS(status) != 0)) {
                             ui_print("\nError restoring data.\n\n");
                        } else {
                             ui_print("\nRestore complete!\n\n");
                        }
                    }
                    break;
*/
// drakaz : launch Galaxy's modified Nandroid backup script with backup option
	    	case ITEM_NANDROID:
                    if (ensure_root_path_mounted("SDCARD:") != 0) {
                        ui_print("\nCan't mount sdcard\n");
                    } else {
                        ui_print("\nPerforming backup");
                        pid_t pid = fork();
                        if (pid == 0) {
                            char *args[] = {"/sbin/sh", NANDROID_BIN, "-b", NULL};
                            execv("/sbin/sh", args);
                            fprintf(stderr, "E:Can't run %s\n(%s)\n", BACKUP_DATA_BIN, strerror(errno));
                            _exit(-1);
                        }

                        int status;

                        while (waitpid(pid, &status, WNOHANG) == 0) {
                            ui_print(".");
                            sleep(1);
                        }
                        ui_print("\n");

                        if (!WIFEXITED(status) || (WEXITSTATUS(status) != 0)) {
                             ui_print("\nError running nandroid backup. Backup not performed.\n\n");
                        } else {
                             ui_print("\nBackup complete!\n\n");
                        }
                    }
                    break;

// drakaz : launch Galaxy's modified Nandroid backup script with restore option
                case ITEM_RESTORE:
                    ui_print("\n-- Restore latest Nandroid backup");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_restore = ui_wait_key();
                    if (confirm_restore == KEY_DREAM_HOME) {
                        ui_print("\n");
                        if (ensure_root_path_mounted("SDCARD:") != 0) {
                            ui_print("\nCan't mount sdcard, aborting.\n");
                        } else {
                            ui_print("\nRestoring latest backup");
                            pid_t pid = fork();
                            if (pid == 0) {
                                char *args[] = {"/sbin/sh", NANDROID_BIN, "--restore", "--defaultinput", NULL};
                                execv("/sbin/sh", args);
                                fprintf(stderr, "Can't run %s\n(%s)\n", NANDROID_BIN, strerror(errno));
                                _exit(-1);
                            }

                            int status3;

                            while (waitpid(pid, &status3, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            } 
                            ui_print("\n");

                            if (!WIFEXITED(status3) || (WEXITSTATUS(status3) != 0)) {
                                ui_print("\nError performing restore!  Try running 'nandroid-mobile.sh --restore' from console.\n\n");
                            } else {
                                ui_print("\nRestore complete!\n\n");
                            }
                        }
                    } else {
                        ui_print("\nRestore complete!\n\n");
                    }
                    if (!ui_text_visible()) return;
                    break;
		    
		    
// drakaz : launch Galaxy's modified Nandroid backup script with delete option. Nandroid will delete the oldest backup in it's backup dir
		case ITEM_DELETE:
                    ui_print("\n-- Delete oldest Nandroid backup");
		    ui_print("\n-- BE CARREFULL, If there remains only one backup, this will delete it !");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_delete = ui_wait_key();
                    if (confirm_delete == KEY_DREAM_HOME) {
                        ui_print("\n");
                        if (ensure_root_path_mounted("SDCARD:") != 0) {
                            ui_print("\nCan't mount sdcard, aborting.\n");
                        } else {
                            ui_print("\nDeleting oldest backup");
                            pid_t pid = fork();
                            if (pid == 0) {
                                char *args[] = {"/sbin/sh", NANDROID_BIN ,"-d", "--defaultinput", NULL};
                                execv("/sbin/sh", args);
                                fprintf(stderr, "Can't run %s\n(%s)\n", NANDROID_BIN, strerror(errno));
                                _exit(-1);
                            }
                            int status3;

                            while (waitpid(pid, &status3, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
                            ui_print("\n");

                            if (!WIFEXITED(status3) || (WEXITSTATUS(status3) != 0)) {
                                ui_print("\nError performing restore!  Try running 'nandroid-mobile.sh --delete' from console.\n\n");
                            } else {
                                ui_print("\nDelete complete!\n\n");
                            }
                        }
                    } else {
                        ui_print("\nDelete complete!\n\n");
                    }
                    if (!ui_text_visible()) return;
                    break;

// drakaz : Add su-root on current rom
		case ITEM_SU_ON:
                    ui_print("\n-- Enable su-root on current rom");
		    ui_print("\n-- Custom rom have already su-root");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_su_on = ui_wait_key();
                    if (confirm_su_on == KEY_DREAM_HOME) {
                        ui_print("\nEnabling su..");

		// Mount system partition
			pid_t pidpre1 = fork();
                            if (pidpre1 == 0) {
				char *argspre1[] = { "mount", "/system", NULL };
				execv("/sbin/busybox", argspre1);
                                fprintf(stderr, "Can't mount %s\n(%s)\n", SYSTEME_PART, strerror(errno));
                                _exit(-1);
                            }
                            int status3pre1;
                            while (waitpid(pidpre1, &status3pre1, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
                            
		// Remount system partition in rw
			pid_t pid = fork();
                            if (pid == 0) {
				char *args[] = { "mount", "-o", "remount,rw", SYSTEME_PART, "/system", NULL };
				execv("/sbin/busybox", args);
                                fprintf(stderr, "Can't remount %s\n(%s) in rw\n", SYSTEME_PART, strerror(errno));
                                _exit(-1);
                            }
                            int status3;
                            while (waitpid(pid, &status3, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Copy su binary to /system/bin/
			pid_t pid2 = fork();
                            if (pid2 == 0) {
				char *args2[] = { "cp", "/tmp/RECTOOLS/su", "/system/bin/su", NULL };
				execv("/sbin/busybox", args2);
                                fprintf(stderr, "Can't cp : %s\n(%s)\n", "/tmp/RECTOOLS/su to /system/bin/su : ", strerror(errno));
                                _exit(-1);
                            }
                            int status32;
                            while (waitpid(pid2, &status32, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
		// Copy su binary to /system/xbin/ from compatibility
			pid_t pid3 = fork();
                            if (pid3 == 0) {
				char *args3[] = { "cp", "/tmp/RECTOOLS/su", "/system/xbin/su", NULL };
				execv("/sbin/busybox", args3);
                                fprintf(stderr, "Can't cp : %s\n(%s)\n", "/tmp/RECTOOLS/su to /system/xbin/su : ", strerror(errno));
                                _exit(-1);
                            }
                            int status33;
                            while (waitpid(pid3, &status33, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Chmod /system/bin/su
			pid_t pid4 = fork();
                            if (pid4 == 0) {
				char *args4[] = { "chmod", "4755", "/system/bin/su", NULL };
				execv("/sbin/busybox", args4);
                                fprintf(stderr, "Can't chmod : %s\n(%s)\n", "/system/bin/su : ", strerror(errno));
                                _exit(-1);
                            }
                            int status34;
                            while (waitpid(pid4, &status34, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
		// Chmod /system/xbin/su
			pid_t pid5 = fork();
                            if (pid5 == 0) {
				char *args5[] = { "chmod", "4755", "/system/xbin/su", NULL };
				execv("/sbin/busybox", args5);
                                fprintf(stderr, "Can't chmod : %s\n(%s)\n", "/system/xbin/su : ", strerror(errno));
                                _exit(-1);
                            }
                            int status35;
                            while (waitpid(pid5, &status35, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Copy Superuser apk to /system/app
			pid_t pid6 = fork();
                            if (pid6 == 0) {
				char *args6[] = { "cp", "/tmp/RECTOOLS/Superuser.apk", "/system/app/Superuser.apk", NULL };
				execv("/sbin/busybox", args6);
                                fprintf(stderr, "Can't cp %s\n(%s)\n", "/tmp/RECTOOLS/Superuser.apk to /system/app/Superuser.apk", strerror(errno));
                                _exit(-1);
                            }
                            int status36;
                            while (waitpid(pid6, &status36, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Remount system partition in ro
			pid_t pid7 = fork();
                            if (pid7 == 0) {
				char *args7[] = { "mount", "-o", "remount,ro", SYSTEME_PART, "/system", NULL };
				execv("/sbin/busybox", args7);
                                fprintf(stderr, "Can't remount %s\n(%s)\n", SYSTEME_PART, strerror(errno));
                                _exit(-1);
                            }
                            int status37;
                            while (waitpid(pid7, &status37, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

                            ui_print("\n");

                            if (!WIFEXITED(status3) || (WEXITSTATUS(status3) != 0) || !WIFEXITED(status32) || (WEXITSTATUS(status32) != 0) || !WIFEXITED(status33) || (WEXITSTATUS(status33) != 0) || !WIFEXITED(status34) || (WEXITSTATUS(status34) != 0) || !WIFEXITED(status35) || (WEXITSTATUS(status35) != 0) || !WIFEXITED(status36) || (WEXITSTATUS(status36) != 0)) {
                                ui_print("\nError enabling su !\n\n");
                            } else {
                                ui_print("\nSu is now enabled !\n\n");
                            }
                    } else {
                        ui_print("\nOperation complete!\n\n");
                    }
                    if (!ui_text_visible()) return;
                    break;

// drakaz : remove su-root on current rom
		case ITEM_SU_OFF:
                    ui_print("\n-- Disable su-root on current rom");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_su_off = ui_wait_key();
                    if (confirm_su_off == KEY_DREAM_HOME) {
                        ui_print("\n");
                        ui_print("Disabling su..");

		// Mount system partition
			pid_t pidpre1 = fork();
                            if (pidpre1 == 0) {
				char *argspre1[] = { "mount", "/system", NULL };
				execv("/sbin/busybox", argspre1);
                                fprintf(stderr, "Can't mount : %s\n(%s)\n", SYSTEME_PART, strerror(errno));
                                _exit(-1);
                            }
                            int status3pre1;
                            while (waitpid(pidpre1, &status3pre1, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Remount system partition in rw
                            pid_t pid = fork();
                            if (pid == 0) { 
				char *args[] = { "mount", "-o", "remount,rw", SYSTEME_PART, "/system", NULL };
				execv("/sbin/busybox", args);
                                fprintf(stderr, "Can't remount : %s\n(%s) in rw\n", SYSTEME_PART, strerror(errno));
                                _exit(-1);
                            }
                            int status3;
                            while (waitpid(pid, &status3, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Delete /system/bin/su
                            pid_t pid2 = fork();
                            if (pid2 == 0) {
				char *args2[] = { "rm", "/system/bin/su", NULL};
				execv("/sbin/busybox", args2);
                                fprintf(stderr, "Can't delete : %s\n(%s)\n", "/system/bin/su :", strerror(errno));
                                _exit(-1);
                            }
                            int status32;
                            while (waitpid(pid2, &status32, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }


		// Delete /system/xbin/su
                            pid_t pid3 = fork();
                            if (pid3 == 0) {
				char *args3[] = { "rm", "/system/xbin/su", NULL};
				execv("/sbin/busybox", args3);
                                fprintf(stderr, "Can't delete : %s\n(%s)\n", "/system/xbin/su :", strerror(errno));
                                _exit(-1);
                            }
                            int status33;
                            while (waitpid(pid3, &status33, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Delete /system/app/Superuser.apk
                            pid_t pid4 = fork();
                            if (pid4 == 0) {
				char *args4[] = { "rm", "/system/app/Superuser.apk", NULL};
				execv("/sbin/busybox", args4);
                                fprintf(stderr, "Can't delete : %s\n(%s)\n", "/system/app/Superuser.apk :", strerror(errno));
                                _exit(-1);
                            }
                            int status34;
                            while (waitpid(pid4, &status34, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

		// Remount system partition in ro
			pid_t pid5 = fork();
                            if (pid5 == 0) {
				char *args5[] = { "mount", "-o", "remount,ro", SYSTEME_PART, "/system", NULL };
				execv("/sbin/busybox", args5);
                                fprintf(stderr, "Can't remount %s\n(%s)\n", SYSTEME_PART, strerror(errno));
                                _exit(-1);
                            }
                            int status35;
                            while (waitpid(pid5, &status35, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
                            ui_print("\n");

                            if (!WIFEXITED(status3) || (WEXITSTATUS(status3) != 0) || !WIFEXITED(status32) || (WEXITSTATUS(status32) != 0) || !WIFEXITED(status33) || (WEXITSTATUS(status33) != 0) || !WIFEXITED(status34) || (WEXITSTATUS(status34) != 0)) {
                                ui_print("\nError disabling su !\n\n");
                            } else {
                                ui_print("\nSu is now disabled !\n\n");
                            }
                    } else {
                        ui_print("\nOperation complete!\n\n");
                    }
                    if (!ui_text_visible()) return;
                    break;	
		    

// drakaz : modification of wipe for Galaxy
      case ITEM_WIPE_DATA:
                    ui_print("\n-- This will ERASE your data!");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort..");
                    int confirm_wipe = ui_wait_key();
                    if (confirm_wipe == KEY_DREAM_HOME) {
                        ui_print("\n-- Wiping data...\n");
                        erase_root("CACHE:");
// drakaz : first wipe galaxy internal data with erase_root
			erase_root("INTERNAL:");
			ui_print("\nWiping internal data...\n");

// drakaz : second, delete with simple rm to be sure of the correct deletion
// Galaxy nand are capricious

// Mount /data partition
 		    pid_t pidf = fork();
                    if (pidf == 0) {
			char *args[] = { "mount", "-rw", "/data", NULL };
			execv("/sbin/busybox", args);
                        fprintf(stderr, "Unable to mount /data. Already mounted ?\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status;
                    while (waitpid(pidf, &fsck_status, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }

// Delete all data in /data
 		    pid_t pidf2 = fork();
                    if (pidf2 == 0) {
			char *args2[] = {"/system/bin/rm", "-rf", "/data/", NULL};
			execv("/system/bin/rm", args2);
                        fprintf(stderr, "Unable to format /data\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status2;
                    while (waitpid(pidf2, &fsck_status2, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }

		    sync();
// Sync
		    pid_t pidf3 = fork();
                    if (pidf3 == 0) {
			char *args3[] = {"sync", NULL};
			execv("sync", args3);
                        fprintf(stderr, "Unable to sync /data\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status3;
                    while (waitpid(pidf3, &fsck_status3, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }

// Umount data partition

		    pid_t pidf4 = fork();
                    if (pidf4 == 0) {
			char *args4[] = { "umount", "/data", NULL };
			execv("/sbin/busybox", args4);
                        fprintf(stderr, "Unable to umount /data. Already mounted ?\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status4;
                    while (waitpid(pidf4, &fsck_status4, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
		 

		    sync();
		    ui_print("\nData wipe complete, rebooting in recovery mode...\n");
		    sleep(5);
// Reboot
		    pid_t pidf5 = fork();
                    if (pidf5 == 0) {
			char *args5[] = { "/sbin/reboot", "recovery", NULL };
			execv("/sbin/reboot", args5);
                        fprintf(stderr, "Unable to reboot ?!\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status5;
                    while (waitpid(pidf5, &fsck_status5, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
                    if (!ui_text_visible()) {
			return;
		    }
		    }
                    break;


// drakaz : fsck on ext3 filesystem on /data    
	    case ITEM_FSCK:
                    ui_print("Checking ext3 /data filesystem");

// Umount /data partition
 		    pid_t pidf = fork();
                    if (pidf == 0) {
			char *args[] = { "/sbin/busybox", "umount", "/data", NULL };
			execv("/sbin/busybox", args);
                        fprintf(stderr, "Unable to umount /data\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status;
                    while (waitpid(pidf, &fsck_status, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }

// Start fsck
                    pid_t pidf2 = fork();
                    if (pidf2 == 0) {
                        char *args2[] = {E2FSCK_BIN, "-y", DATA_PART, NULL };
                        execv(E2FSCK_BIN, args2);
                        fprintf(stderr, "Unable to execute e2fsck!\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }

                    int fsck_status2;

                    while (waitpid(pidf2, &fsck_status2, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }

// Remount /data partition
   		    pid_t pidf3 = fork();
                    if (pidf3 == 0) {
			char *args3[] = { "/sbin/busybox", "mount", DATA_PART, "/data", NULL };
			execv("/sbin/busybox", args3);
                        fprintf(stderr, "Unable to mount /data\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status3;
                    while (waitpid(pidf3, &fsck_status3, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
                    ui_print("\n");

                    if (!WIFEXITED(fsck_status2) || (WEXITSTATUS(fsck_status2) != 0)) {
                        ui_print("\nError checking filesystem! Run e2fsck manually from console.\n\n");
                    } else {
                        ui_print("\nFilesystem checked and repaired.\n\n");
                    }
                    break;
		    
		    
// drakaz : ext4 convertion/checking. Convert and sync 3 time to avoid nand refresh pb
		case CONVERT_DATA_EXT4:
		    ui_print("\n-- Be carreful, ext4dev can only");
                    ui_print("\n-- be used with custom rom.");
                    ui_print("\n-- !! Wipe to reformat in ext3 !!");
		    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort..");
 		    int confirm_ext4 = ui_wait_key();
                    if (confirm_ext4 == KEY_DREAM_HOME) {
 		    	ui_print("\n-- Converting /data to ext4...\n");
			pid_t pidf = fork();
                    if (pidf == 0) {
			char *args[] = { "/sbin/sh", "/tmp/RECTOOLS/toext4", NULL };
			execv("/sbin/sh", args);
                        fprintf(stderr, "Unable to mount /data. Already mounted ?\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status;
                    while (waitpid(pidf, &fsck_status, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
		    sync();
		    
		    pid_t pidf2 = fork();	
   		    if (pidf2 == 0) {
			char *args2[] = { "/sbin/sh", "/tmp/RECTOOLS/toext4", NULL };
			execv("/sbin/sh", args2);
                        fprintf(stderr, "Unable to mount /data. Already mounted ?\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status2;
                    while (waitpid(pidf2, &fsck_status2, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
		    sync();

		    pid_t pidf3 = fork();	
   		    if (pidf3 == 0) {
			char *args3[] = { "/sbin/sh", "/tmp/RECTOOLS/toext4", NULL };
			execv("/sbin/sh", args3);
                        fprintf(stderr, "Unable to mount /data. Already mounted ?\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status3;
                    while (waitpid(pidf3, &fsck_status3, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }
		    sync();
			
			ui_print("\nConvertion complete, now rebooting and return in recovery mode...\n");
                    } else {
                        ui_print("\nConvertion aborted.\n");
                    }

		    sync();
		    ui_print("\nRebooting in recovery mode...\n");
		    sleep(5);

		    pid_t pidcreboot = fork();
                    if (pidcreboot == 0) {
			char *argscreboot[] = { "/sbin/reboot", "recovery", NULL };
			execv("/sbin/reboot", argscreboot);
                        fprintf(stderr, "Unable to mount /data. Already mounted ?\n(%s)\n", strerror(errno));
                        _exit(-1);
                    }
                    int fsck_status_c_reboot;
                    while (waitpid(pidcreboot, &fsck_status_c_reboot, WNOHANG) == 0) {
                        ui_print(".");
                        sleep(1);
                    }

                    if (!ui_text_visible()) {
			return;
		    }
		    break;

		    
// drakaz : swap support on external SD by reformatting it in two partition (32mb swap and remaining in fat32)
		case ITEM_SD_SWAP_ON:
                    ui_print("\n-- Format SD 32Mb swap and remaining in fat32");
		    ui_print("\n-- BE CARREFULL, THIS WILL ERASE ALL THE DATA ON EXTERNAL SDCARD");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_swap_on = ui_wait_key();
                    if (confirm_swap_on == KEY_DREAM_HOME) {
			    ui_print("\n");
                            ui_print("Formatting SD..");
			    pid_t pid3 = fork();
                            if (pid3 == 0) {
				char *args3[] = { "/sbin/sh", SDTOOLS, "-s", NULL };
				execv("/sbin/sh", args3);
				fprintf(stderr, "Can't split %s\n(%s)\n", "external SD :", strerror(errno));
                                _exit(-1);
                            }

                            int status32;
                            while (waitpid(pid3, &status32, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
		        
                            ui_print("\n");

                            if (!WIFEXITED(status32) || (WEXITSTATUS(status32) != 0)) {
                                ui_print("\nError formatting external SD !\n\n");
                            } else {
                                ui_print("\nExternal SD is now splited (fat32+swap) !\n\n");	
                            }
                    } else {
                        ui_print("\nOperation complete!\n\n");
                    }
                    if (!ui_text_visible()) return;
                    break;



// drakaz : remove swap on external SD by reformatting it in only one fat32 partition
		case ITEM_SD_SWAP_OFF:
                    ui_print("\n-- Format external SD in fat32");
		    ui_print("\n-- BE CARREFULL, THIS WILL ERASE ALL THE DATA ON EXTERNAL SDCARD");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_swap_off = ui_wait_key();
                    if (confirm_swap_off == KEY_DREAM_HOME) {
                        ui_print("\n");
                            ui_print("\nFormatting internal SDCARD..");

		            // Formattage de la SD interne 
			    pid_t pid3 = fork();
                            if (pid3 == 0) {
				char *args3[] = { "/sbin/sh", SDTOOLS, "-c", NULL };
				execv("/sbin/sh", args3);
				fprintf(stderr, "Can't restore %s\n(%s)\n", "external SD :", strerror(errno));
                                _exit(-1);
                            }

                            int status32;
                            while (waitpid(pid3, &status32, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }
		        
                            ui_print("\n");

                            if (!WIFEXITED(status32) || (WEXITSTATUS(status32) != 0)) {
                                ui_print("\nError formatting external SD !\n\n");
                            } else {
                                ui_print("\nExternal SD is now restored (fat32) !\n\n");	
                            }
                    } else {
                        ui_print("\nOperation complete!\n\n");
                    }
                   break;



// drakaz : launch script which fix package permissions
		case FIX_PERMS:
                    ui_print("\n-- Fix permissions on /data");
		    ui_print("\n-- Usefull after an upgrade");
                    ui_print("\n-- Press HOME to confirm, or");
                    ui_print("\n-- any other key to abort.");
                    int confirm_fix = ui_wait_key();
                    if (confirm_fix == KEY_DREAM_HOME) {
                        ui_print("\n");
                        ui_print("Fixing permissions...");
                            pid_t pid = fork();
                            if (pid == 0) { 
				char *args[] = { "/sbin/sh", FIX_PERMS_BIN, NULL };
				execv("/sbin/sh", args);
                                fprintf(stderr, "Can't fix permissions %s\n(%s)\n", "", strerror(errno));
                                _exit(-1);
                            }
                            int status;
                            while (waitpid(pid, &status, WNOHANG) == 0) {
                                ui_print(".");
                                sleep(1);
                            }

                            ui_print("\n");

                            if (!WIFEXITED(status) || (WEXITSTATUS(status) != 0)) {
                                ui_print("\nError fixing permissions !\n\n");
                            } else {
                                ui_print("\nPermissions fixed !\n\n");
                            }
                    } else {
                        ui_print("\nOperation complete!\n\n");
                    }
                    if (!ui_text_visible()) return;
                    break;
            }
            // if we didn't return from this function to reboot, show
            // the menu again.
            ui_start_menu(headers, items);
            selected = 0;
            chosen_item = -1;

            finish_recovery(NULL);
            ui_reset_progress();

            // throw away keys pressed while the command was running,
            // so user doesn't accidentally trigger menu items.
            ui_clear_key_queue();
        }
    }
}

static void
print_property(const char *key, const char *name, void *cookie)
{
    fprintf(stderr, "%s=%s\n", key, name);
}

int
main(int argc, char **argv)
{
    time_t start = time(NULL);

    // If these fail, there's not really anywhere to complain...
    freopen(TEMPORARY_LOG_FILE, "a", stdout); setbuf(stdout, NULL);
    freopen(TEMPORARY_LOG_FILE, "a", stderr); setbuf(stderr, NULL);
    fprintf(stderr, "Starting recovery on %s", ctime(&start));

    tcflow(STDIN_FILENO, TCOOFF);
    
    char prop_value[PROPERTY_VALUE_MAX];
    property_get("ro.modversion", &prop_value, "not set");




// Create themes dir

    pid_t pidtheme = fork();
    if (pidtheme == 0) {
	char *argstheme[] = { "mkdir", "/sdcard/themes", NULL };
	execv("/sbin/busybox", argstheme);
        fprintf(stderr, "Can't mkdir /sdcard/themes\n(%s)\n", strerror(errno));
        _exit(-1);
    }
    int statustheme;
    while (waitpid(pidtheme, &statustheme, WNOHANG) == 0) {
    	ui_print(".");
    	sleep(1);
    }


    ui_init();
    ui_print("Build: ");
    ui_print(prop_value);
    ui_print("\nBy drakaz\n");
    get_args(&argc, &argv);

    int previous_runs = 0;
    const char *send_intent = NULL;
    const char *update_package = NULL;
    int wipe_data = 0, wipe_cache = 0;

    int arg;
    while ((arg = getopt_long(argc, argv, "", OPTIONS, NULL)) != -1) {
        switch (arg) {
        case 'p': previous_runs = atoi(optarg); break;
        case 's': send_intent = optarg; break;
        case 'u': update_package = optarg; break;
        case 'w': wipe_data = wipe_cache = 1; break;
        case 'c': wipe_cache = 1; break;
        case '?':
            LOGE("Invalid command argument\n");
            continue;
        }
    }

    fprintf(stderr, "Command:");
    for (arg = 0; arg < argc; arg++) {
        fprintf(stderr, " \"%s\"", argv[arg]);
    }
    fprintf(stderr, "\n\n");

    property_list(print_property, NULL);
    fprintf(stderr, "\n");

#if TEST_AMEND
    test_amend();
#endif

    RecoveryCommandContext ctx = { NULL };
    if (register_update_commands(&ctx)) {
        LOGE("Can't install update commands\n");
    }

    int status = INSTALL_SUCCESS;

    if (update_package != NULL) {
        status = install_package(update_package);
        if (status != INSTALL_SUCCESS) ui_print("Installation aborted.\n");
    } else if (wipe_data || wipe_cache) {
        if (wipe_data && erase_root("DATA:")) status = INSTALL_ERROR;
        if (wipe_cache && erase_root("CACHE:")) status = INSTALL_ERROR;
        if (status != INSTALL_SUCCESS) ui_print("Data wipe failed.\n");
    } else {
        status = INSTALL_ERROR;  // No command specified
    }

    if (status != INSTALL_SUCCESS) ui_set_background(BACKGROUND_ICON_ERROR);
    if (status != INSTALL_SUCCESS || ui_text_visible()) prompt_and_wait();

    // If there is a radio image pending, reboot now to install it.
    maybe_install_firmware_update(send_intent);

    // Otherwise, get ready to boot the main system...
    finish_recovery(send_intent);
    sync();
    if (do_reboot)
    {
    	ui_print("Rebooting...\n");
    	reboot(RB_AUTOBOOT);
	}
	
	tcflush(STDIN_FILENO, TCIOFLUSH);	
	tcflow(STDIN_FILENO, TCOON);
	
    return EXIT_SUCCESS;
}
