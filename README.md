# 📱 **CyAndroCel: Advanced Android Automation Library**

<!-- PROJECT LOGO -->
<br />
<div align="center">
  <a href="https://github.com/hansalemaos/cyandrocel">
    <img src="https://github.com/hansalemaos/cyandrocel/blob/main/logo.png?raw=true" alt="Logo" width="400" height="400">
  </a>

  <h3 align="center">Python / Cython Automation for Android Emulators</h3>

  <p align="center">
    Android automations without ADB - directly on emulators
  </p>
</div>


## About The Project

**CyAndroCel** is a powerful [**Python**](https://www.python.org/) library designed for advanced Android automation. For performance reasons, it’s primarily written in [**C++**](https://cplusplus.com/) and [**Cython**](https://cython.readthedocs.io/), providing multiple backends for interacting with UI elements, handling input events, and efficiently extracting screen data.

**CyAndroCel** is designed to run on non-rooted devices and depends on [**ADB**](https://developer.android.com/tools/adb). If you need a version that runs directly and independently on an emulator or rooted device without relying on ADB, check outt [**CyAndroEmu**](https://github.com/hansalemaos/cyandroemu)

---

## 🚀 **Why Choose CyAndroCel?**


- **Low-Level Performance:**
  Thanks to its C++ core, CyAndroCel achieves unparalleled speed and efficiency, even in resource-intensive environments.

- **Multi-Backend Support:**
  Choose from various parsers and input methods tailored to different Android environments (real devices, emulators, custom ROMs) without needing root.

- **Seamless Emulator Integration:**
  Designed to work flawlessly with any Android Device.

- **Linux/Windows support**
  Run your automation scripts on both Windows and Linux.


---

## Getting Started

### Installation

#### Before installing, ensure you have a C++20 compiler installed ([MSVC on Windows](https://visualstudio.microsoft.com/de/vs/features/cplusplus/) / [GCC on Linux](https://www.gnu.org/)), run

#### `pip install cyandrocel`

The library will be compiled the first time you import it.

After compilation, four parsers will be downloaded and built using [Zig's C++ compiler](https://ziglang.org/):


[**Uiautomator2 Parser**](https://github.com/hansalemaos/uiautomator2tocsv)


[**Uiautomator Classic Parser**](https://github.com/hansalemaos/uiautomator_dump_to_csv)


[**Fragment Parser**](https://github.com/hansalemaos/android_fragment_parser)


[**Tesseract Parser**](https://github.com/hansalemaos/tesseract_hocr_to_csv)


***
***


## Writing Python scripts

CyAndroCel is primarily written in [C++](https://cplusplus.com/)  (4 out of 5 parsers) and [Cython](https://cython.readthedocs.io/) (1 parser and the Python interface), but all automation is handled using the Python class CyAndroCel.

***

### The Constructor

#### May Look Intimidating, but It’s Easy to Understand

```py
CyAndroCel:
    str adb_exe,
    str device_id,
    int subprocess_timeout = 30,
    bint add_input_tap = True,
    str input_cmd_tap = "input tap",
    str input_cmd_text = "input text",
    str input_cmd_swipe= "input swipe",
    int screen_height = 2400,
    int screen_width = 1080,
    str sh_exe = "sh",
    str su_exe = "su",
    str path_exe_tesseract = "tesseract",
    object tesseract_args = ("-l", "por+eng", "--oem", "3"),
    int tesseract_word_group_limit=20,
    bint tesseract_delete_tmp_files=True,
    str ui2_download_link1="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator-test_with_hidden_elements.apk",
    str ui2_download_link2="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator_with_hidden_elements.apk",
    str adb_keyboard_link = "https://github.com/hansalemaos/ADBKeyBoard/raw/refs/heads/master/ADBKeyboard.apk",
    object valid_adb_keyboards = ("com.android.adbkeyboard/.AdbIME", "com.github.uiautomator/.AdbKeyboard",),
    object kwargs=None,
```


### Each constructor argument explained

***

#### `adb_exe : str`

Path to the ADB executable.
On Windows systems, paths for adb_exe and path_exe_tesseract are shortened using get_short_path_name.

#### `device_id : str`

Unique identifier for the target Android device.
use `adb devices` to get the serial number

#### `subprocess_timeout : int, optional`

Timeout in seconds for subprocess calls (default 30).

#### `add_input_tap : bint, optional`

If True, enable input tap functionality (default True).

#### `input_cmd_tap : str, optional`

Command used to simulate tap events (default "input tap").

#### `input_cmd_text : str, optional`

Command used to simulate text input (default "input text").

#### `input_cmd_swipe : str, optional`

Command used to simulate text swipe (default "input swipe").

#### `screen_height : int, optional`

Expected screen height in pixels (default 2400).

#### `screen_width : int, optional`

Expected screen width in pixels (default 1080).

#### `sh_exe : str, optional`

Shell executable to use (default "sh").

#### `su_exe : str, optional`

Superuser command to use (default "su").
Some predefined shell commands require `su`, but the core functionality of the library — parsing screen elements and interacting with them — does not require `su`.

#### `path_exe_tesseract : str, optional`

Path to the Tesseract executable (default "tesseract").
On Windows systems, paths for adb_exe and path_exe_tesseract are shortened using get_short_path_name.

#### `tesseract_args : tuple or list, optional`

Arguments for Tesseract OCR (default ("-l", "por+eng", "--oem", "3")).

#### `tesseract_word_group_limit : int, optional`

Limit in pixel for grouping words in OCR output (default 20).

#### `tesseract_delete_tmp_files : bint, optional`

Whether to delete temporary OCR files after processing (default True).

#### `ui2_download_link1 : str, optional`

URL for the first UIAutomator2 APK download.

(default  "https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator-test_with_hidden_elements.apk")

I forked the Uiautomator2 project and modified it to include non-visible objects in the parsed data. This enhancement lets you, for example, read notifications without having to open the swipe-down menu.

#### `ui2_download_link2 : str, optional`

URL for the second UIAutomator2 APK download.

(default  "https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator_with_hidden_elements.apk")

I forked the Uiautomator2 project and modified it to include non-visible objects in the parsed data. This enhancement lets you, for example, read notifications without having to open the swipe-down menu.

#### `adb_keyboard_link : str, optional`

Backup APK from the [ADBKeyboard project](https://github.com/senzhk/ADBKeyBoard). It allows sending Unicode characters but may not work on all devices. In most cases, there’s no need to modify it.


URL for downloading the ADB keyboard APK.

(default  "https://github.com/hansalemaos/ADBKeyBoard/raw/refs/heads/master/ADBKeyboard.apk")


#### `valid_adb_keyboards : tuple|list, optional`

A tuple|list containing valid ADB keyboard identifiers.

(default  ("com.android.adbkeyboard/.AdbIME", "com.github.uiautomator/.AdbKeyboard"))


#### `kwargs : dict, optional`

Additional keyword arguments for subprocess execution.

(default None)



***
***


## Creating an instance

```py
from cyandrocel import CyAndroCel
import shutil


adb_exe = shutil.which("adb")
device_id = "YOUR DEVICE ID HERE"
cyandro = CyAndroCel(
    adb_exe=adb_exe,
    device_id=device_id,
    subprocess_timeout=30,
    add_input_tap=True,
    input_cmd_tap="input tap",
    input_cmd_text="input text",
    screen_height=2400,
    screen_width=1080,
    sh_exe="sh",
    su_exe="su",
    path_exe_tesseract="tesseract",
    tesseract_args=("-l", "por+eng", "--oem", "3"),
    tesseract_word_group_limit=20,
    tesseract_delete_tmp_files=True,
    ui2_download_link1="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator-test_with_hidden_elements.apk",
    ui2_download_link2="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator_with_hidden_elements.apk",
    adb_keyboard_link="https://github.com/hansalemaos/ADBKeyBoard/raw/refs/heads/master/ADBKeyboard.apk",
    valid_adb_keyboards=(
        "com.android.adbkeyboard/.AdbIME",
        "com.github.uiautomator/.AdbKeyboard",
    ),
    kwargs=None,
)
```
***

## Automation - it's all about pandas DataFrames

Most automation tools implement their own logic for finding elements, which often looks like this:

`self.find(text="Some text").children[0].click()`

That looks beautiful and very Pythonic, but most of the time, it’s just unreliable — mainly when the attributes and positions of objects vary, or when the objects aren’t loaded on the screen yet.

Instead of bothering you with my own "great" ideas, I decided to rely on battle-tested solutions: [pandas DataFrames](https://pandas.pydata.org/).

**With DataFrames, you can leverage powerful features like:**

* Fast sorting algorithms
* All kinds of comparisons
* Regular expressions (regex)
* Custom filter functions

If you know how to work with pandas DataFrames, you basically already know everything you need to automate whatever you want.
If not, you can learn everything from the official documentation: https://pandas.pydata.org/docs/
That’s where I got 95% of my pandas knowledge from.

***

### Pretty Print


The default `__repr__` and `__str__` functions in pandas are not ideal for displaying DataFrames, which is why they’ve been monkey-patched to ensure the entire DataFrame is pretty-printed.

```py
df = cyandro.get_df_uiautomator2(with_screenshot=True)
print(df)
```

Now, when you print the DataFrame, you’ll see the complete content neatly formatted, making it easier to analyze UI elements.
For a line-break-free experience, I recommend using the [VTM terminal](https://github.com/directvt/vtm)

***

#### Example of a pandas DataFrame in the VTM terminal

[![Video 1](https://img.youtube.com/vi/e-lqgiDWDNQ/0.jpg)](https://www.youtube.com/watch?v=e-lqgiDWDNQ)

***

#### Getting screenshots of each element

In the example above, the elements are very easy to locate. However, this is not always the case.
You might want to see a screenshot of each element to write your script faster. In this case, you can use the following command on the device:

```py
df.bb_save_screenshots_as_png("/sdcard/uiautomator2screenshots")
```

The screenshot filenames correspond to the location of the elements in the DataFrame.
For example, if you want to locate the third element (index 2), simply run:

```py
df.iloc[2]
```
This will extract the element’s information, allowing you to build your pandas query from there.


***
***

#### Python Code


```py
from cyandrocel import CyAndroCel
import shutil


adb_exe = shutil.which("adb")
device_id = "xxxx" # use adb devices -l
screen_width, screen_height = CyAndroCel.get_resolution_of_screen(
    adb_exe=adb_exe, device_id=device_id
)
print(screen_width, screen_height)

cyandro = CyAndroCel(
    adb_exe=adb_exe,
    device_id=device_id,
    subprocess_timeout=30,
    add_input_tap=True,
    input_cmd_tap="input tap",
    input_cmd_text="input text",
    input_cmd_swipe="input swipe",
    screen_height=screen_height,
    screen_width=screen_width,
    sh_exe="sh",
    su_exe="su",
    path_exe_tesseract="tesseract",
    tesseract_args=("-l", "por+eng", "--oem", "3"),
    tesseract_word_group_limit=20,
    tesseract_delete_tmp_files=True,
    ui2_download_link1="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator-test_with_hidden_elements.apk",
    ui2_download_link2="https://github.com/hansalemaos/uiautomator2tocsv/raw/refs/heads/main/app-uiautomator_with_hidden_elements.apk",
    adb_keyboard_link="https://github.com/hansalemaos/ADBKeyBoard/raw/refs/heads/master/ADBKeyboard.apk",
    valid_adb_keyboards=(
        "com.android.adbkeyboard/.AdbIME",
        "com.github.uiautomator/.AdbKeyboard",
    ),
    kwargs=None,
)

# disables the uiautomator2 server automatically if it is activated
df2 = cyandro.get_df_uiautomator_classic(with_screenshot=True)
print(df2)

# make sure that tesseract is installed
# choco install tesseract
# or https://tesseract-ocr.github.io/
df1 = cyandro.get_df_tesseract()
print(df1)
# levenshtein search afterwards
df1 = df1.d_fm_damerau_levenshtein_distance_2ways(
    ["YouTube : Musicas Gospel"], "aa_text", "aa_searchfortext"
).sort_values(by=["damerau_levenshtein_distance_2ways_match"], ascending=False)

# fragment parser
df3 = cyandro.get_df_fragments(with_screenshot=True)
print(df3)

# window parser
df4 = cyandro.get_df_window_dump(with_screenshot=True)
print(df4)


# call cyandro.download_and_install_uiautomator2_apks() to download and install the apks first
# first parse with uiautomator2 takes around 5 seconds to activate the server

df5 = cyandro.get_df_uiautomator2(with_screenshot=True)
print(df5)

# clicking on a button - same system for all parsers
# df5.loc[df5.aa_text == "Spotify"].aa_input_tap.iloc[0]()

naturaltext = cyandro.get_cmd_send_text_natural("Hallo")
shell = cyandro.open_shell()

# sends unicode, may not work with every device
# Supported letters are:
# á, é, í, ó, ú, ý, Á, É, Í, Ó, Ú, Ý, ç, Ç, â, ê, î, ô, û, Â, Ê, Î, Ô, Û, ã, ñ, õ, Ã, Ñ, Õ, ß, ẞ, ä, ë, ï, ö, ü, ÿ, Ä, Ë, Ï, Ö, Ü, Ÿ, à, è, ì, ò, ù, À, È, Ì, Ò, Ù
acaotext = cyandro.get_cmd_send_text_unicode_natural("Ação")
acaotext()

# creates a new column "black_color" with the color search results
df5.bb_search_for_colors([[0, 0, 0], [255, 255, 255]], result_column="black_color")



```
#### Check out [CyAndoEmu](https://github.com/hansalemaos/cyandroemu) for more detailed examples - the API is the same (except for the aditional root functionality that cyandroemu has)

## The Backends

***

### [Uiautomator2 Backend](https://github.com/hansalemaos/uiautomator2tocsv/tree/d5022bd0bb5864ba3b36cfb9c444f6557c2381c8)

| **Advantages ✅**                               | **Disadvantages ❌**                                      |
|------------------------------------------------|----------------------------------------------------------|
| Very fast parsing                              | Blocks other parsers like the Logcat parser and traditional UIAutomator |
| Never fails due to excessive screen movement (unlike UIAutomator) | Requires APKs to be installed                              |
| Includes both element text and description     | The server needs to run in the background                 |
| Great for web scraping and interacting with web elements | Automation might be detected when used with installed apps |
| Runs on any device                           | Useless with specific engines like the Unreal Engine                 |
| Finds also hidden items                           | -                |

***

### [Tesseract Backend](https://github.com/hansalemaos/screencap2tesseract2csv)

| **Advantages ✅**                                              | **Disadvantages ❌**                                           |
|---------------------------------------------------------------|----------------------------------------------------------------|
| Detects (in theory) all text on the screen                    | Higher CPU usage compared to other parsers                     |
| Works with Unreal Engine and Roblox games                     | May produce inaccurate results (mostly resolved by fast C++-implemented Levenshtein distance calculation) |
| Can categorize elements (image, text, line, etc.)             | Requires additional downloads                                 |
| Undetectable                                                  | Needs a screenshot to function                                |
| Can be used alongside any other parser                        | —                                                              |

***

### [Fragment Parser Backend](https://github.com/hansalemaos/android_fragment_parser)

| **Advantages ✅**                                              | **Disadvantages ❌**                                           |
|---------------------------------------------------------------|----------------------------------------------------------------|
| The fastest of all parsers                                    | Results don’t include the element’s text                       |
| Very low CPU usage                                            | Sometimes misses elements that UIAutomator-based parsers can detect |
| Can be used alongside any other parser                        | —                                                              |
| Provides useful additional information that other parsers don’t have | —                                                              |
| Can find elements that UIAutomator-based parsers can’t detect | —                                                              |
| Undetectable                                                  | —                                                              |
| Highly reliable—never fails                                  | —                                                              |


***

### [UIAutomator Classic Backend](https://github.com/hansalemaos/uiautomator_dump_to_csv)

| **Advantages ✅**                                              | **Disadvantages ❌**                                           |
|---------------------------------------------------------------|----------------------------------------------------------------|
| Includes both element text and description                    | Higher CPU usage compared to UIAutomator2                      |
| Undetectable                                                  | May fail (idle state error) if there’s too much activity on the screen |
| Can be used alongside any other parser (except UIAutomator2)  | —                                                              |

***

### Window Dump Backend

| **Advantages ✅**                                              | **Disadvantages ❌**                                           |
|---------------------------------------------------------------|----------------------------------------------------------------|
| Very fast parser                                              | Results don’t include the element’s text                       |
| Very low CPU usage                                            | Doesn’t work everywhere (e.g., the start page of the launcher) |
| Can be used alongside any other parser                        | —                                                              |
| Provides lots of additional information that other parsers don’t have | —                                                              |
| Can find elements that UIAutomator-based parsers can’t detect | —                                                              |
| Undetectable                                                  | —                                                              |

***

## Color Search

### If you decide to add a screenshot to your DataFrame, you can perform a very fast color search (uses fast C++ vectors and structs for the results internally).

```py

# Pass RGB colors and the name of the column
df.bb_search_for_colors([[255, 255, 255], [0, 0, 0]], result_column="white_and_black")

# An new column will be added
df.white_and_black

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
iloc | index   | white_and_black                                                                                                                                                                                                                                                                                           |
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
0    | 0       | [{'x': 140, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 141, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 142, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 143, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 144, 'y': 65, 'count': 20 |
1    | 1       | [{'x': 140, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 141, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 142, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 143, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 144, 'y': 65, 'count': 20 |
2    | 2       | [{'x': 140, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 141, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 142, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 143, 'y': 65, 'count': 20148, 'r': 255, 'g': 255, 'b': 255}, {'x': 144, 'y': 65, 'count': 20 |
3    | 3       | [{'x': 128, 'y': 100, 'count': 4811, 'r': 255, 'g': 255, 'b': 255}, {'x': 129, 'y': 100, 'count': 4811, 'r': 255, 'g': 255, 'b': 255}, {'x': 130, 'y': 100, 'count': 4811, 'r': 255, 'g': 255, 'b': 255}, {'x': 131, 'y': 100, 'count': 4811, 'r': 255, 'g': 255, 'b': 255}, {'x': 132, 'y': 100, 'count': 4 |
4    | 4       | [{'x': 128, 'y': 100, 'count': 665, 'r': 255, 'g': 255, 'b': 255}, {'x': 129, 'y': 100, 'count': 665, 'r': 255, 'g': 255, 'b': 255}, {'x': 130, 'y': 100, 'count': 665, 'r': 255, 'g': 255, 'b': 255}, {'x': 131, 'y': 100, 'count': 665, 'r': 255, 'g': 255, 'b': 255}, {'x': 132, 'y': 100, 'count': 665,  |
5    | 5       | [{'x': 248, 'y': 100, 'count': 1717, 'r': 255, 'g': 255, 'b': 255}, {'x': 249, 'y': 100, 'count': 1717, 'r': 255, 'g': 255, 'b': 255}, {'x': 250, 'y': 100, 'count': 1717, 'r': 255, 'g': 255, 'b': 255}, {'x': 251, 'y': 100, 'count': 1717, 'r': 255, 'g': 255, 'b': 255}, {'x': 252, 'y': 100, 'count': 1 |
6    | 6       | [{'x': 470, 'y': 100, 'count': 830, 'r': 255, 'g': 255, 'b': 255}, {'x': 471, 'y': 100, 'count': 830, 'r': 255, 'g': 255, 'b': 255}, {'x': 472, 'y': 100, 'count': 830, 'r': 255, 'g': 255, 'b': 255}, {'x': 473, 'y': 100, 'count': 830, 'r': 255, 'g': 255, 'b': 255}, {'x': 474, 'y': 100, 'count': 830,  |
7    | 7       | [{'x': 117, 'y': 412, 'count': 311, 'r': 255, 'g': 255, 'b': 255}, {'x': 118, 'y': 412, 'count': 311, 'r': 255, 'g': 255, 'b': 255}, {'x': 119, 'y': 412, 'count': 311, 'r': 255, 'g': 255, 'b': 255}, {'x': 118, 'y': 413, 'count': 311, 'r': 255, 'g': 255, 'b': 255}, {'x': 119, 'y': 413, 'count': 311,  |
8    | 8       | [{'x': 339, 'y': 412, 'count': 402, 'r': 255, 'g': 255, 'b': 255}, {'x': 340, 'y': 412, 'count': 402, 'r': 255, 'g': 255, 'b': 255}, {'x': 341, 'y': 412, 'count': 402, 'r': 255, 'g': 255, 'b': 255}, {'x': 340, 'y': 413, 'count': 402, 'r': 255, 'g': 255, 'b': 255}, {'x': 341, 'y': 413, 'count': 402,  |
9    | 9       | [{'x': 568, 'y': 497, 'count': 62, 'r': 255, 'g': 255, 'b': 255}, {'x': 569, 'y': 497, 'count': 62, 'r': 255, 'g': 255, 'b': 255}, {'x': 580, 'y': 497, 'count': 62, 'r': 255, 'g': 255, 'b': 255}, {'x': 589, 'y': 497, 'count': 62, 'r': 255, 'g': 255, 'b': 255}, {'x': 597, 'y': 497, 'count': 62, 'r':  |
10   | 10      | [{'x': 151, 'y': 729, 'count': 197, 'r': 255, 'g': 255, 'b': 255}, {'x': 152, 'y': 729, 'count': 197, 'r': 255, 'g': 255, 'b': 255}, {'x': 85, 'y': 730, 'count': 197, 'r': 255, 'g': 255, 'b': 255}, {'x': 86, 'y': 730, 'count': 197, 'r': 255, 'g': 255, 'b': 255}, {'x': 149, 'y': 730, 'count': 197, 'r |
11   | 11      | [{'x': 362, 'y': 638, 'count': 627, 'r': 255, 'g': 255, 'b': 255}, {'x': 363, 'y': 638, 'count': 627, 'r': 255, 'g': 255, 'b': 255}, {'x': 364, 'y': 638, 'count': 627, 'r': 255, 'g': 255, 'b': 255}, {'x': 365, 'y': 638, 'count': 627, 'r': 255, 'g': 255, 'b': 255}, {'x': 366, 'y': 638, 'count': 627,  |
12   | 12      | [{'x': 140, 'y': 65, 'count': 17610, 'r': 255, 'g': 255, 'b': 255}, {'x': 141, 'y': 65, 'count': 17610, 'r': 255, 'g': 255, 'b': 255}, {'x': 142, 'y': 65, 'count': 17610, 'r': 255, 'g': 255, 'b': 255}, {'x': 143, 'y': 65, 'count': 17610, 'r': 255, 'g': 255, 'b': 255}, {'x': 144, 'y': 65, 'count': 17 |
13   | 13      | [{'x': 136, 'y': 77, 'count': 100, 'r': 255, 'g': 255, 'b': 255}, {'x': 141, 'y': 77, 'count': 100, 'r': 255, 'g': 255, 'b': 255}, {'x': 142, 'y': 77, 'count': 100, 'r': 255, 'g': 255, 'b': 255}, {'x': 143, 'y': 77, 'count': 100, 'r': 255, 'g': 255, 'b': 255}, {'x': 144, 'y': 77, 'count': 100, 'r':  |
14   | 14      | [{'x': 150, 'y': 65, 'count': 15852, 'r': 255, 'g': 255, 'b': 255}, {'x': 151, 'y': 65, 'count': 15852, 'r': 255, 'g': 255, 'b': 255}, {'x': 152, 'y': 65, 'count': 15852, 'r': 255, 'g': 255, 'b': 255}, {'x': 153, 'y': 65, 'count': 15852, 'r': 255, 'g': 255, 'b': 255}, {'x': 154, 'y': 65, 'count': 15 |
15   | 15      | [{'x': 568, 'y': 77, 'count': 177, 'r': 255, 'g': 255, 'b': 255}, {'x': 569, 'y': 77, 'count': 177, 'r': 255, 'g': 255, 'b': 255}, {'x': 570, 'y': 77, 'count': 177, 'r': 255, 'g': 255, 'b': 255}, {'x': 571, 'y': 77, 'count': 177, 'r': 255, 'g': 255, 'b': 255}, {'x': 572, 'y': 77, 'count': 177, 'r':  |
16   | 16      | []                                                                                                                                                                                                                                                                                                           |
17   | 17      | []                                                                                                                                                                                                                                                                                                           |
18   | 18      | []                                                                                                                                                                                                                                                                                                           |
19   | 19      | [{'x': 344, 'y': 1129, 'count': 250, 'r': 0, 'g': 0, 'b': 0}, {'x': 333, 'y': 1130, 'count': 250, 'r': 0, 'g': 0, 'b': 0}, {'x': 334, 'y': 1130, 'count': 250, 'r': 0, 'g': 0, 'b': 0}, {'x': 331, 'y': 1131, 'count': 250, 'r': 0, 'g': 0, 'b': 0}, {'x': 334, 'y': 1131, 'count': 250, 'r': 0, 'g': 0, 'b' |
20   | 20      | []                                                                                                                                                                                                                                                                                                           |
21   | 21      | [{'x': 599, 'y': 1147, 'count': 1, 'r': 255, 'g': 255, 'b': 255}]                                                                                                                                                                                                                                            |
22   | 22      | []

```


## 🎯 **Input Events Without Element Parsing**

To interact with elements—such as clicking, tapping, scrolling, writing text, or pressing keys—you can create instances of a collection of input classes. The advantage is that these instances are **callable** and can be **reused**, which saves overhead.

Most of these classes are implemented in **Cython** using low-overhead `cdef` classes for maximum performance.


### 📱 Using the System's `input` Command

```py
cmd_input_tap = cyandro.get_cmd_input_tap(100, 100)
cmd_input_tap()
```

***


### ✍️ Using the System's `input` Command (Latin Letters with Accents Normalized)

```py
# Sends the whole text
cmd_send_text = cyandro.get_cmd_send_text("Hi there m'y frönd")
cmd_send_text()

# sends each letter of the text
cmd_send_text_natural = cyandro.get_cmd_send_text_natural("Hi there my frönd")
cmd_send_text_natural()

# sends each letter of the text - unicode - supports á, é, í, ó, ú, ý, Á, É, Í, Ó, Ú, Ý, ç, Ç, â, ê, î, ô, û, Â, Ê, Î, Ô, Û, ã, ñ, õ, Ã, Ñ, Õ, ß, ẞ, ä, ë, ï, ö, ü, ÿ, Ä, Ë, Ï, Ö, Ü, Ÿ, à, è, ì, ò, ù, À, È, Ì, Ò, Ù
# Uses Androids input keycombination - contribs for more letters are welcome!
cmd_send_text_natural_with_unicode = cyandro.get_cmd_send_text_unicode("Hi there my frönd")
cmd_send_text_natural_with_unicode()

cmd_send_text_natural_with_unicode_each_letter = cyandro.get_cmd_send_text_unicode_natural("Hi there my frönd")
cmd_send_text_natural_with_unicode_each_letter()
```

***

### ⌨️ Keycodes (Using the System's input Command)

```py
cyandro.KeyCodes.long_press_KEYCODE_BACKSLASH()
cyandro.KeyCodes.short_press_KEYCODE_BACKSLASH()
```
***

### [🌐 ADBKeyboard - For Unicode Text (Not Supported on Every Device)](https://github.com/senzhk/ADBKeyBoard)
```py
cyandro.adb_keyboard.download_adbkeyboard_apk()
cyandro.adb_keyboard.install_adbkeyboard_apk()
cyandro.adb_keyboard.activate_adb_keyboard()
cyandro.adb_keyboard.send_unicode_text_with_delay(
 text="Hello myç friend",
 delay_range=(0.05, 0.3),
)
cyandro.adb_keyboard.send_unicode_text("Hello myç friend")
cyandro.disable_adb_keyboard()
```

***

## 🖥️ **The Interactive Shell**

Sometimes, you need to do more than just parse and interact with elements on the screen—you need to execute commands directly on the device.
**CyAndroCel** provides an interactive shell that doesn’t rely on either the Python `subprocess` module or Python threads.

This shell is implemented **100% in C++**, runs in **nogil mode**, and offers **excellent reaction times**, making it perfect for high-performance automation tasks.

***

### 🚀 Key Benefits of the Interactive Shell:

1. **Real-Time Interaction:** Fast command execution with immediate feedback.
2. **Root Access Control:** Easily switch between normal and superuser modes.
3. **DataFrame Integration:** Collect system data in a structured format for automation workflows.
4. **Optimized for Performance:** Runs in C++ with nogil mode for high responsiveness.

***

### 🚀 **Starting an Interactive Shell**

### To start a shell, simply use:

#### For a C++ shell:

| **Advantages ✅**                                              | **Disadvantages ❌**                                           |
|---------------------------------------------------------------|----------------------------------------------------------------|
| No-Gil                                                        | Segfaults if there is no ADB connection (Python crashes)                                                             |
| Very low CPU usage                                            | —                                                              |
| The C++ destructor closes the shell                           | —                                                              |
| Uses C++ threads to capture stdout/stderr                     | —                                                              |

```python
myshell = cyandro.open_shell(
    buffer_size=40960,        # The max size of the C++ vector—works like collections.deque (ring buffer)
    exit_command=b"exit",     # The command to exit the shell, required by the C++ destructor.
                              # Executed automatically when 'myshell' goes out of scope.
    print_stdout=False,       # Prints stdout to the screen—useful for debugging purposes
    print_stderr=False,       # Prints stderr to the screen—useful for debugging purposes
    use_py_subproc=False      # Doesn't use Python's subprocess
)

```

#### For a Python shell:

| **Advantages ✅**                                              | **Disadvantages ❌**                                           |
|---------------------------------------------------------------|----------------------------------------------------------------|
| Throws an exception if there is no ADB connection                                                        | Higher CPU usage                                                              |
| —                     | Shell must be closed manually using self.close_py_subproc()                                                            |
| —                     | —                                                              |
| —                     | —                                                              |

```python
myshell = cyandro.open_shell(
    buffer_size=40960,        # ignored
    exit_command=b"exit",     # ignored
    print_stdout=False,       # ignored
    print_stderr=False        # ignored
    use_py_subproc=True,      # uses Python's subprocess
)
# Do some stuff
...
# close the shell manually
myshell.close_py_subproc()

***

## ⚡ **Interacting Directly with the Shell**

Once the interactive shell is running, you can execute commands directly and capture their output effortlessly.

***

### 📋 **Executing Commands**

```python
>>> stdout, stderr = myshell.write_and_wait("ls -lZ")
# stdout and stderr contain the command’s output in bytes.
# Use .decode() to convert the output to a human-readable string.
>>> print(stdout.decode())
total 48
-rw-r--r--  1 root    root    u:object_r:app_data_file:s0                     12264 2025-02-06 20:29 None
drwxr-x--- 16 root    root    u:object_r:app_data_file:s0                      4096 2025-02-04 22:57 cyandrocel
-rw-r--r--  1 root    root    u:object_r:app_data_file:s0                         0 2025-02-02 01:40 pckldf.pkl
-rw-r-----  1 root    root    u:object_r:app_data_file:s0                     17446 2025-02-04 22:51 pyshell.py
drwx------  5 u0_a286 u0_a286 u:object_r:app_data_file:s0:c30,c257,c512,c768   4096 2025-02-01 23:45 tessdata
drwxr-xr-x  5 root    root    u:object_r:app_data_file:s0                      4096 2025-02-02 00:13 tessdata_best
drwxr-xr-x  5 root    root    u:object_r:app_data_file:s0                      4096 2025-02-02 00:11 tessdata_fast
```

***

## Predefined Shell Commands

### The shell comes with a variety of predefined commands to simplify common tasks.

#### These commands follow two naming conventions:

1. get_df_* → Returns data as a pandas DataFrame for easy analysis.
2. sh_* → Executes shell commands and usually returns a tuple[bytes, bytes] containing stdout and stderr,
but not always—some commands may return different structures.

### ✅ Example: Checking the Current User

```py
# This command checks the current user, and the result is returned in byte format (b'root').
>>> myshell.sh_whoami()
b'shell'
```
***

## Important: Some of the commands below may not work due to missing root rights

### ✅ Example: Getting the build props as a pandas DataFrame

```py
>>> buildprops=myshell.get_df_build_props()
>>> print(buildprops)

--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
iloc  | index | aa_file                                            | aa_line   | aa_line_content                                                                                                                                                                                                                                                                                              |
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
0     | 0     | '/data/adb/modules/make_writeable/system.prop'     | 0         | b'# This file will be read by resetprop'                                                                                                                                                                                                                                                                     |
1     | 1     | '/data/adb/modules/make_writeable/system.prop'     | 1         | b'# Example: Change dpi'                                                                                                                                                                                                                                                                                     |
2     | 2     | '/data/adb/modules/make_writeable/system.prop'     | 2         | b'# ro.sf.lcd_density=320'                                                                                                                                                                                                                                                                                   |
3     | 3     | '/data/adb/modules/make_writeable/module.prop'     | 0         | b'id=make_writeable'                                                                                                                                                                                                                                                                                         |
4     | 4     | '/data/adb/modules/make_writeable/module.prop'     | 1         | b'name=Make Writeable'                                                                                                                                                                                                                                                                                       |
5     | 5     | '/data/adb/modules/make_writeable/module.prop'     | 2         | b'version=1.0'                                                                                                                                                                                                                                                                                               |
6     | 6     | '/data/adb/modules/make_writeable/module.prop'     | 3         | b'versionCode=01'                                                                                                                                                                                                                                                                                            |
7     | 7     | '/data/adb/modules/make_writeable/module.prop'     | 4         | b'author=hansalemao'

...

```

## ⚡ **List of Implemented Shell Methods**

CyAndroCel provides a wide range of shell methods to control Android devices efficiently. These methods are optimized for speed and reliability.

## 📦 **Some of the Implemented Shell Methods**


### 🔍 **Check Out the Source Code for More Details**


```py
sh_force_open_app_with_disable(self, package_name, sleep_time, timeout=3)
sh_save_sed_replace(self, file_path, string2replace, replacement, timeout=1000)
sh_svc_enable_wifi(self, timeout=10)
sh_svc_disable_wifi(self, timeout=10)
sh_trim_cache(self, timeout=10)
sh_force_open_app(self, package_name, sleep_time, timeout=3)
sh_get_main_activity(self, package_name, timeout=3)
sh_svc_power_shutdown(self, timeout=3)
sh_svc_power_reboot(self, timeout=3)
sh_dumpsys_dropbox(self, timeout=3)
sh_set_new_launcher(self, package_name, timeout=3)
sh_tar_folder(self, src, dst, timeout=1000000)
sh_extract_tar_zip(self, src_file, dst_folder, timeout=1000000)
sh_get_user_rotation(self, timeout=10)
sh_copy_dir_recursive(self, src, dst, timeout=1000)
sh_backup_file(self, src, timeout=1000)
sh_remove_folder(self, folder, timeout=1000)
sh_get_pid_of_shell(self, int64_t timeout=3)
sh_whoami(self, int64_t timeout=10)
sh_dumpsys_package(self, package, timeout=1000, bint convert_to_dict=True)
sh_get_all_wanted_permissions_from_package(self, package, timeout=1000)
sh_grant_permission(self, package, permission, timeout=10)
sh_grant_permission(self, package, permission, timeout=10)
sh_grant_all_wanted_permissions(self, package, timeout=1000)
sh_revoke_all_wanted_permissions(self, package, timeout=1000)
sh_parse_whole_dumpsys_to_dict(self, timeout=100,convert_to_dict=False)
sh_parse_dumpsys_to_dict(self, subcmd, timeout=100,convert_to_dict=False)
sh_get_available_keyboards(self, timeout=10)
sh_get_active_keyboard(self, timeout=10)
sh_get_all_information_about_all_keyboards(self, timeout=10,convert_to_dict=False)
sh_enable_keyboard(self, keyboard, timeout=10)
sh_disable_keyboard(self, keyboard, timeout=10)
sh_is_keyboard_shown(self, timeout=10)
sh_set_keyboard(self, keyboard, timeout=10)
sh_show_touches(self, timeout=10)
sh_dont_show_touches(self, timeout=10)
sh_show_pointer_location(self, timeout=10)
sh_dont_show_pointer_location(self, timeout=10)
sh_input_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_tap(self, x, y, timeout=10)
sh_clear_file_content(self, file_path, timeout=10)
sh_makedirs(self, folder, timeout=10)
sh_touch(self, file_path, timeout=10)
sh_mv(self, src, dst, timeout=10)
sh_open_accessibility_settings(self, timeout=10)
sh_open_advanced_memory_protection_settings(self, timeout=10)
sh_open_airplane_mode_settings(self, timeout=10)
sh_open_all_apps_notification_settings(self, timeout=10)
sh_open_apn_settings(self, timeout=10)
sh_open_application_details_settings(self, timeout=10)
sh_open_application_development_settings(self, timeout=10)
sh_open_application_settings(self, timeout=10)
sh_open_app_locale_settings(self, timeout=10)
sh_open_app_notification_bubble_settings(self, timeout=10)
sh_open_app_notification_settings(self, timeout=10)
sh_open_app_open_by_default_settings(self, timeout=10)
sh_open_app_search_settings(self, timeout=10)
sh_open_app_usage_settings(self, timeout=10)
sh_open_automatic_zen_rule_settings(self, timeout=10)
sh_open_auto_rotate_settings(self, timeout=10)
sh_open_battery_saver_settings(self, timeout=10)
sh_open_bluetooth_settings(self, timeout=10)
sh_open_captioning_settings(self, timeout=10)
sh_open_cast_settings(self, timeout=10)
sh_open_channel_notification_settings(self, timeout=10)
sh_open_condition_provider_settings(self, timeout=10)
sh_open_data_roaming_settings(self, timeout=10)
sh_open_data_usage_settings(self, timeout=10)
sh_open_date_settings(self, timeout=10)
sh_open_device_info_settings(self, timeout=10)
sh_open_display_settings(self, timeout=10)
sh_open_dream_settings(self, timeout=10)
sh_open_hard_keyboard_settings(self, timeout=10)
sh_open_home_settings(self, timeout=10)
sh_open_ignore_background_data_restrictions_settings(self, timeout=10)
sh_open_ignore_battery_optimization_settings(self, timeout=10)
sh_open_input_method_settings(self, timeout=10)
sh_open_input_method_subtype_settings(self, timeout=10)
sh_open_internal_storage_settings(self, timeout=10)
sh_open_locale_settings(self, timeout=10)
sh_open_location_source_settings(self, timeout=10)
sh_open_manage_all_applications_settings(self, timeout=10)
sh_open_manage_all_sim_profiles_settings(self, timeout=10)
sh_open_manage_applications_settings(self, timeout=10)
sh_open_manage_default_apps_settings(self, timeout=10)
sh_open_manage_supervisor_restricted_setting(self, timeout=10)
sh_open_manage_write_settings(self, timeout=10)
sh_open_memory_card_settings(self, timeout=10)
sh_open_network_operator_settings(self, timeout=10)
sh_open_nfcsharing_settings(self, timeout=10)
sh_open_nfc_payment_settings(self, timeout=10)
sh_open_nfc_settings(self, timeout=10)
sh_open_night_display_settings(self, timeout=10)
sh_open_notification_assistant_settings(self, timeout=10)
sh_open_notification_listener_detail_settings(self, timeout=10)
sh_open_notification_listener_settings(self, timeout=10)
sh_open_notification_policy_access_settings(self, timeout=10)
sh_open_print_settings(self, timeout=10)
sh_open_privacy_settings(self, timeout=10)
sh_open_quick_access_wallet_settings(self, timeout=10)
sh_open_quick_launch_settings(self, timeout=10)
sh_open_regional_preferences_settings(self, timeout=10)
sh_open_satellite_setting(self, timeout=10)
sh_open_search_settings(self, timeout=10)
sh_open_security_settings(self, timeout=10)
sh_open_settings(self, timeout=10)
sh_open_settings(self, timeout=10)
sh_open_sound_settings(self, timeout=10)
sh_open_storage_volume_access_settings(self, timeout=10)
sh_open_sync_settings(self, timeout=10)
sh_open_usage_access_settings(self, timeout=10)
sh_open_user_dictionary_settings(self, timeout=10)
sh_open_voice_input_settings(self, timeout=10)
sh_open_vpn_settings(self, timeout=10)
sh_open_vr_listener_settings(self, timeout=10)
sh_open_webview_settings(self, timeout=10)
sh_open_wifi_ip_settings(self, timeout=10)
sh_open_wifi_settings(self, timeout=10)
sh_open_wireless_settings(self, timeout=10)
sh_open_zen_mode_priority_settings(self, timeout=10)
sh_open_developer_settings(self, timeout=10)
sh_rescan_media_folder(self, folder, timeout=10)
sh_rescan_media_file(self, file_path, timeout=10)
sh_dump_process_memory_to_sdcard(self, pid, timeout=100000)
sh_pm_clear(self, package, timeout=10)
sh_wm_change_size(self, width, height, timeout=10)
sh_wm_reset_size(self, timeout=10)
sh_wm_get_density(self, timeout=10)
sh_wm_change_density(self, density, timeout=10)
sh_wm_reset_density(self, timeout=10)
sh_am_screen_compat_on(self, package, timeout=10)
sh_am_screen_compat_off(self, package, timeout=10)
sh_enable_notifications(self, timeout=10)
sh_disable_notifications(self, timeout=10)
sh_still_image_camera(self, timeout=10)
sh_disable_network_interface(self, nic, timeout=10)
sh_enable_network_interface(self, nic, timeout=10)
sh_get_linux_version(self, timeout=10)
sh_expand_notifications(self, timeout=10)
sh_expand_settings(self, timeout=10)
sh_list_permission_groups(self, timeout=10)
sh_input_dpad_tap(self, x, y, timeout=10)
sh_input_keyboard_tap(self, x, y, timeout=10)
sh_input_mouse_tap(self, x, y, timeout=10)
sh_input_touchpad_tap(self, x, y, timeout=10)
sh_input_gamepad_tap(self, x, y, timeout=10)
sh_input_touchnavigation_tap(self, x, y, timeout=10)
sh_input_joystick_tap(self, x, y, timeout=10)
sh_input_touchscreen_tap(self, x, y, timeout=10)
sh_input_stylus_tap(self, x, y, timeout=10)
sh_input_trackball_tap(self, x, y, timeout=10)
sh_input_dpad_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_dpad_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_dpad_roll(self, x, y, timeout=10)
sh_input_keyboard_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_keyboard_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_keyboard_roll(self, x, y, timeout=10)
sh_input_mouse_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_mouse_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_mouse_roll(self, x, y, timeout=10)
sh_input_touchpad_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_touchpad_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_touchpad_roll(self, x, y, timeout=10)
sh_input_gamepad_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_gamepad_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_gamepad_roll(self, x, y, timeout=10)
sh_input_touchnavigation_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_touchnavigation_roll(self, x, y, timeout=10)
sh_input_joystick_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_joystick_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_joystick_roll(self, x, y, timeout=10)
sh_input_touchscreen_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_touchscreen_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_touchscreen_roll(self, x, y, timeout=10)
sh_input_stylus_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_stylus_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_stylus_roll(self, x, y, timeout=10)
sh_input_trackball_swipe(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_trackball_draganddrop(self, x1, y1, x2, y2, duration, timeout=10)
sh_input_trackball_roll(self, x, y, timeout=10)
sh_open_url(self, url, timeout=10)
sh_get_bios_information(self, timeout=10)
sh_printenv(self, timeout=10)
sh_freeze_proc(self, pid, timeout=10)
sh_unfreeze_proc(self, pid, timeout=10)
sh_show_fragments_on_screen_enable(self, timeout=10)
sh_show_fragments_on_screen_disable(self, timeout=10)
sh_read_write_remount(self, methods, timeout=100)
```

## 📊 Methods That Return Pandas DataFrames

Some shell methods are designed to return data as pandas DataFrames for easy analysis and manipulation.


```py

get_df_files_with_context_printf(self, object folders, int64_t max_depth=1, int64_t timeout=10)
get_df_build_props(self, int64_t timeout=10)
get_df_files_with_ending(self, object folders, object endings, int64_t max_depth=10000, int64_t timeout=10)
get_df_top_procs(self, timeout=1000)
get_df_users(self, start=0, end=2000, timeout=10000)
get_df_groups_of_user(self, start=0, end=2000, timeout=10000)
get_df_netstat_tlnp(self, timeout=100)
get_df_mounts(self, timeout=100)
get_df_ps_el(self, timeout=1000)
get_df_packages(self, timeout=10)
get_df_netstat_connections_of_apps(self, resolve_names=True, timeout=10)
get_df_lsmod(self, timeout=1000)
get_df_lsof(self, timeout=1000000)

```

## Non-Adb shell API

### The methods can be accessed using:

```py
cyandro.Adb.METHOD(...)
```

```py
class Adb
 |  Adb(unicode exefile, unicode device_id, kwargs)
 |
 |      A class to encapsulate Android Debug Bridge (ADB) functionalities.
 |
 |      This class provides methods for interacting with Android devices via ADB commands.
 |      It supports operations such as pushing scripts to the device, setting up TCP port
 |      forwarding/reversal, starting or killing the ADB server, pairing devices, retrieving
 |      connected devices, and uninstalling APKs.
 |
 |      Attributes
 |      ----------
 |      exefile : str
 |          The path to the ADB executable (processed by get_short_path_name for compatibility).
 |      device_id : str
 |          The unique identifier of the target Android device.
 |      kwargs : dict
 |          Additional keyword arguments to pass to subprocess calls.
 |
 |  Methods defined here:
 |
 |  __init__(...)
 |
 |      Initialize an Adb instance.
 |
 |      Parameters
 |      ----------
 |      exefile : str
 |          The path to the ADB executable.
 |      device_id : str
 |          The unique identifier of the target Android device.
 |      kwargs : object
 |          Additional keyword arguments to be used in subprocess calls.
 |
 |
 |  connect(self)
 |              Establish a network connection to the device via ADB.
 |
 |              This method initiates a connection to the device over the network using ADB. It is
 |              typically used after the ADB server has been restarted in TCP mode.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that connects to the specified device.
 |
 |              Notes
 |              -----
 |              The command executed is equivalent to:
 |                  adb connect <device_id>
 |              ensuring that the device is accessible over the network.
 |
 |  forward_tcp_port(self, port_pc, port_device)
 |              Set up forward TCP port forwarding from the device to the host.
 |
 |              Parameters
 |              ----------
 |              port_pc : int
 |                  The TCP port number on the host (PC).
 |              port_device : int
 |                  The TCP port number on the device.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that sets up forward TCP forwarding.
 |
 |  get_all_devices(self)
 |              Retrieve a dictionary of all connected devices.
 |
 |              This method returns a dictionary of devices detected by ADB.
 |
 |              Returns
 |              -------
 |              dict
 |                  A dictionary mapping device identifiers to their details.
 |
 |  get_forwarded_ports(self)
 |              Retrieve a list of forwarded TCP ports on the device.
 |
 |              This method returns the list of port mappings that have been set up for TCP forwarding
 |              from the device to the host.
 |
 |              Returns
 |              -------
 |              list
 |                  A list of forwarded TCP port mappings.
 |
 |  get_reversed_ports(self)
 |              Retrieve a list of reversed TCP ports on the device.
 |
 |              This method returns the list of port mappings that have been set up for reverse TCP
 |              forwarding on the device.
 |
 |              Returns
 |              -------
 |              list
 |                  A list of reversed TCP port mappings.
 |
 |  install_apk(self, path)
 |              Install an APK on the device without forcing an overwrite.
 |
 |              This method installs an APK using the standard ADB installation command without
 |              additional overwrite flags. It assumes the app is not already installed, or that
 |              its presence does not interfere with the installation.
 |
 |              Parameters
 |              ----------
 |              path : str
 |                  The full path to the APK file to be installed.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call executing the ADB installation command.
 |
 |              Notes
 |              -----
 |              The underlying command executed is equivalent to:
 |                  adb -s <device_id> install <processed_path>
 |              where <processed_path> is derived from the provided path.
 |
 |  install_apk_as_test(self, path)
 |              Install an APK on the device in test mode.
 |
 |              This method installs an APK using ADB with the test (-t) flag and grants all runtime
 |              permissions (-g). The provided APK path is processed by get_short_path_name to ensure
 |              compatibility with the operating system (especially on Windows).
 |
 |              Parameters
 |              ----------
 |              path : str
 |                  The full path to the APK file that should be installed on the device.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call which performs the installation. This object
 |                  contains the output and return code from the adb install command.
 |
 |              Notes
 |              -----
 |              The underlying command executed is equivalent to:
 |                  adb -s <device_id> install -g -t <shortened_path>
 |              where:
 |              - The "-g" flag automatically grants all runtime permissions.
 |              - The "-t" flag allows installation of test packages.
 |              - <shortened_path> is obtained by applying get_short_path_name to the provided path.
 |
 |  install_apk_overwrite(self, path)
 |              Install an APK on the device, overwriting any existing installation.
 |
 |              This method installs an APK by forcing an overwrite (typically using the '-r'
 |              flag) so that any previously installed version of the application is replaced.
 |
 |              Parameters
 |              ----------
 |              path : str
 |                  The full path to the APK file that should be installed.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call executing the ADB command for installation.
 |
 |              Notes
 |              -----
 |              The underlying command is equivalent to:
 |                  adb -s <device_id> install -r <processed_path>
 |              where <processed_path> is obtained via get_short_path_name for compatibility.
 |
 |  kill_server(self)
 |              Kill the ADB server.
 |
 |              This method stops the running ADB server.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that kills the ADB server.
 |
 |  pair(self, code)
 |              Pair the device using a provided pairing code.
 |
 |              Parameters
 |              ----------
 |              code : str
 |                  The pairing code used to pair the device.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that pairs the device.
 |
 |  pull_folder(self, src, dst)
 |              Pull a folder from the device to the host machine.
 |
 |              This method downloads the contents of a folder from the Android device to a specified
 |              destination on the host machine.
 |
 |              Parameters
 |              ----------
 |              src : str
 |                  The source folder path on the device.
 |              dst : str
 |                  The destination folder path on the host.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that performs the folder pull operation.
 |
 |              Notes
 |              -----
 |              The internal command is analogous to:
 |                  adb -s <device_id> pull <src> <dst>
 |              ensuring that the folder and its contents are transferred to the host.
 |
 |  push_files_to_folder(self, all_paths, folder_on_device)
 |              Push multiple files from the host to a folder on the device.
 |
 |              This method transfers one or more files specified by their paths on the host machine
 |              to a designated folder on the Android device.
 |
 |              Parameters
 |              ----------
 |              all_paths : list of str
 |                  A list of file paths on the host that should be pushed to the device.
 |              folder_on_device : str
 |                  The destination folder on the device where the files will be placed.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that executes the file push operation.
 |
 |              Notes
 |              -----
 |              This method leverages the adb push command to transfer files, ensuring that each file
 |              is copied to the target folder on the device.
 |
 |  push_files_to_folder_and_rescan_media(self, all_paths, folder_on_device)
 |              Push multiple files to a folder on the device and trigger a media rescan.
 |
 |              This method not only transfers files from the host to a specified folder on the device,
 |              but it also triggers the device's media scanner to update its database, ensuring that
 |              the newly pushed files are recognized by the system.
 |
 |              Parameters
 |              ----------
 |              all_paths : list of str
 |                  A list of file paths on the host that should be transferred.
 |              folder_on_device : str
 |                  The destination folder on the device where the files will be stored.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that performs the push and media rescan.
 |
 |              Notes
 |              -----
 |              The command executed is equivalent to:
 |                  adb push <file> <folder_on_device> && [command to trigger media scan]
 |              This is particularly useful for media files, ensuring they appear in galleries or media players.
 |
 |  push_script_and_start_in_background(self, script)
 |              Push a script to the device and execute it in the background.
 |
 |              The script is first pushed to the device's /sdcard/ directory and then executed
 |              via a shell command. This method facilitates background execution of custom scripts.
 |
 |              Parameters
 |              ----------
 |              script : str
 |                  The content of the script to be pushed and executed.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that starts the script.
 |
 |  reconnect_offline_devices(self)
 |              Reconnect any devices that are currently offline.
 |
 |              This method attempts to re-establish connections to any devices that have been
 |              detected as offline by ADB, thereby restoring communication with those devices.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that attempts to reconnect offline devices.
 |
 |              Notes
 |              -----
 |              The command used internally is analogous to:
 |                  adb reconnect offline
 |              This can be useful in environments where devices frequently lose connection.
 |
 |  restart_as_tcp_5037(self)
 |              Restart the ADB server in TCP mode on port 5037.
 |
 |              This method restarts the ADB server so that it listens for connections over TCP
 |              on port 5037. This is useful for network-based debugging or when USB connectivity
 |              is not feasible.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that restarts the ADB server in TCP mode.
 |
 |              Notes
 |              -----
 |              Internally, this method executes a command similar to:
 |                  adb tcpip 5037
 |              allowing remote connections to the device.
 |
 |  restart_as_usb(self)
 |              Restart the ADB server to use USB mode.
 |
 |              This method reverts the ADB server back to USB mode after it has been started in
 |              TCP mode. It ensures that the device is again connected over USB.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that restarts the ADB server for USB connectivity.
 |
 |              Notes
 |              -----
 |              The underlying command executed is similar to:
 |                  adb usb
 |              which switches the server back to its default USB connection mode.
 |
 |  reverse_tcp_port(self, port_pc, port_device)
 |              Set up reverse TCP port forwarding from the host to the device.
 |
 |              Parameters
 |              ----------
 |              port_pc : int
 |                  The TCP port number on the host (PC).
 |              port_device : int
 |                  The TCP port number on the device.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that sets up reverse TCP forwarding.
 |
 |  start_constant_connect(self)
 |              Start a constant ADB connection process on Windows.
 |
 |              This method initiates a continuous connection process for ADB on Windows platforms.
 |              It first ensures that the adb_connect executable is available by downloading and compiling
 |              it if necessary, and then starts a main process to maintain a persistent connection.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result of the subprocess call that starts the constant connection process.
 |
 |              Raises
 |              ------
 |              NotImplementedError
 |                  If the method is called on a non-Windows system.
 |
 |              Notes
 |              -----
 |              This method is only supported on Windows. The internal steps include:
 |              1. Checking platform compatibility.
 |              2. Downloading and compiling the adb_connect executable if it does not exist.
 |              3. Starting the connection process using mainprocess with the proper executable path.
 |
 |  start_server(self)
 |              Start the ADB server.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that starts the ADB server.
 |
 |  start_server_without_log(self, trunc_each_seconds=60)
 |              Start the ADB server without logging excessive output.
 |
 |              The server is started while simultaneously truncating log output at the specified
 |              interval to prevent large log files.
 |
 |              Parameters
 |              ----------
 |              trunc_each_seconds : int, optional
 |                  The interval (in seconds) at which the log is truncated (default is 60).
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that starts the ADB server.
 |
 |  uninstall_apk(self, package_name)
 |              Uninstall an APK from the device.
 |
 |              Parameters
 |              ----------
 |              package_name : str
 |                  The package name of the APK to uninstall.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that uninstalls the APK.
 |
 |  uninstall_apk_keep_data(self, package_name)
 |              Uninstall an APK from the device while preserving its data.
 |
 |              Parameters
 |              ----------
 |              package_name : str
 |                  The package name of the APK to uninstall.
 |
 |              Returns
 |              -------
 |              subprocess.CompletedProcess
 |                  The result from the subprocess call that uninstalls the APK while keeping data.
 |
```



<!-- ROADMAP -->
## Roadmap

- [ ] Add template matching using https://www.fftw.org/
- [ ] Add more useful commands to the interactive shell
- [ ] Support for Accelerated [Hierarchical Density Clustering in C++](https://github.com/rohanmohapatra/hdbscan-cpp/issues/11)


See the [open issues](https://github.com/hansalemaos/cyandrocel) for a full list of proposed features (and known issues).


## Contributing

Contributions are what make the open source community such an amazing place to learn, inspire, and create. Any contributions you make are **greatly appreciated**.

If you have a suggestion that would make this better, please fork the repo and create a pull request. You can also simply open an issue with the tag "enhancement".
Don't forget to give the project a star! Thanks again!

1. Fork the Project
2. Create your Feature Branch (`git checkout -b feature/AmazingFeature`)
3. Commit your Changes (`git commit -m 'Add some AmazingFeature'`)
4. Push to the Branch (`git push origin feature/AmazingFeature`)
5. Open a Pull Request


## License

Distributed under the MIT License. See `LICENSE` for more information.


## More tutorials

[![Video](https://img.youtube.com/vi/Abo_kqAmRbM/0.jpg)](https://www.youtube.com/watch?v=Abo_kqAmRbM)

[![Video](https://img.youtube.com/vi/J9MEvutzH0g/0.jpg)](https://www.youtube.com/watch?v=J9MEvutzH0g)

[![Video](https://img.youtube.com/vi/V5pvy3-YiCU/0.jpg)](https://www.youtube.com/watch?v=V5pvy3-YiCU)

[![Video](https://img.youtube.com/vi/nf7CdEYUAao/0.jpg)](https://www.youtube.com/watch?v=nf7CdEYUAao)

### Web Scraping of the most protected site there is: https://bet365.com

[![Video](https://img.youtube.com/vi/zaIXmiRgRDQ/0.jpg)](https://www.youtube.com/watch?v=zaIXmiRgRDQ)

[![Video](https://img.youtube.com/vi/gswo-9UhnRw/0.jpg)](https://www.youtube.com/watch?v=gswo-9UhnRw)

[![Video](https://img.youtube.com/vi/TPMopuCqM5s/0.jpg)](https://www.youtube.com/watch?v=TPMopuCqM5s)

[![Video](https://img.youtube.com/vi/6jw1US_OXp8/0.jpg)](https://www.youtube.com/watch?v=6jw1US_OXp8)

[![Video](https://img.youtube.com/vi/B3febrPYBCU/0.jpg)](https://www.youtube.com/watch?v=B3febrPYBCU)

[![Video](https://img.youtube.com/vi/UwzYW8Qkh6E/0.jpg)](https://www.youtube.com/watch?v=UwzYW8Qkh6E)

[![Video](https://img.youtube.com/vi/gbggqeYHuzo/0.jpg)](https://www.youtube.com/watch?v=gbggqeYHuzo)

[![Video](https://img.youtube.com/vi/cqWggXpYTnM/0.jpg)](https://www.youtube.com/watch?v=cqWggXpYTnM)

[![Video](https://img.youtube.com/vi/y476HgwWkA4/0.jpg)](https://www.youtube.com/watch?v=y476HgwWkA4)

[![Video](https://img.youtube.com/vi/NvwuyssvJE0/0.jpg)](https://www.youtube.com/watch?v=NvwuyssvJE0)



## Contact

If you’re interested in private classes with me to learn strategies for automating anything, or if you have an automation project (within legal boundaries!) that you’d like to bring to life, feel free to contact me. I speak German, English, and Portuguese fluently, and Spanish proficiently.

[WhatsApp](https://api.whatsapp.com/send?phone=%205511989782756&text=Question+about+CyAndroCel)

[Discord](https://discord.com/invite/ckhnJ3PxEP)

[Portuguese YouTube Channel](https://www.youtube.com/channel/UC3DeX0cPlJaLSD254T7fpdA)

[English YouTube Channel](https://youtube.com/channel/UCgIfJ0iFUXGfq-G4zkPXGyw)

[GitHub](https://github.com/hansalemaos)

[PIP](https://pypi.org/user/hansalemao)


<!-- MARKDOWN LINKS & IMAGES -->

[product-screenshot]: images/screenshot.png
