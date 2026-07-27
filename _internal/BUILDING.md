# Building DreamCompress v0.4.0

DreamCompress uses PyInstaller to produce self-contained native application
packages.

## Important platform rule

PyInstaller is not a cross-compiler.

Build the Windows package on Windows, the Linux package on Linux, and the
macOS package on macOS. A Windows BAT file cannot directly create genuine
Linux or macOS binaries.

The included GitHub Actions workflow solves this by running the build on three
native hosted runners.

## Requirements

- Python 3.10 or newer; Python 3.12 is recommended for release builds
- Tkinter/Tcl-Tk
- Internet access while installing build requirements
- Pillow
- PyInstaller

The build scripts create an isolated `.venv-build` environment.

## Windows

Double-click:

    BUILD_WINDOWS.bat

Output:

    dist\DreamCompress\DreamCompress.exe
    release\DreamCompress-v0.4.0-Windows.zip

## Linux

Make the script executable if necessary:

    chmod +x build_linux.sh

Build:

    ./build_linux.sh

Output:

    dist/DreamCompress/DreamCompress
    release/DreamCompress-v0.4.0-Linux.tar.gz

On Debian or Ubuntu, install Tkinter with:

    sudo apt install python3-tk

## macOS

Make the script executable:

    chmod +x build_macos.sh

Build:

    ./build_macos.sh

Output:

    dist/DreamCompress.app
    release/DreamCompress-v0.4.0-macOS.zip

The script generates an ICNS icon from the DreamCompress PNG when macOS icon
tools are present.

Public macOS releases may require Apple code signing and notarization.
Unsigned applications can trigger Gatekeeper warnings.

## GitHub Actions

Copy the entire source package to a GitHub repository, including:

    .github/workflows/build-release.yml

Open the repository's Actions page and run `Build DreamCompress`, or push a
tag such as:

    v0.4.0

The workflow builds Windows, Linux, and macOS packages independently and
uploads each release archive as an Actions artifact.

## Why one-folder builds?

One-folder mode makes missing files and dependency issues easier to diagnose.
It also avoids repeatedly unpacking an application at startup.

Distribute the generated ZIP or TAR archive as a whole. Do not distribute only
the executable from inside the folder.

## Architecture

The output architecture follows the Python interpreter and operating-system
runner used for the build.

For architecture-specific releases, run the script with the desired native
Python installation and label the resulting archive appropriately.
