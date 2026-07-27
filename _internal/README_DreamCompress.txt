DreamCompress CPR <-> PVR Tool v0.4.0
=====================================

Created by Kazetrigger

DreamCompress is a batch-oriented Dreamcast romhacking utility for detecting
and decompressing CPR resources, extracting PVR textures, converting textures
to PNG or BMP, rebuilding PVR data, and applying supported compression
wrappers.

The GUI is built around the deSPIRIA PVR/CPR backend v1.2.1.

Main features
-------------

- Batch CPR/PVR queues
- Per-file and multi-file wrapper settings
- Automatic wrapper detection with PVR validation
- LZSS, PRS, Zlib, Gzip, Bzip2, XZ, and raw PVR support
- PVR, PNG, and BMP extraction
- PVR metadata for dependable image rebuilding
- PVR pixel, twiddle, VQ, Small VQ, palette, and GBIX controls
- JSON game profiles
- Custom orange DreamCompress interface
- Built-in documentation and version history
- Native Windows, Linux, and macOS build tooling

Run from Python
---------------

Install Pillow:

    python -m pip install Pillow

Run:

    python dreamcompress_gui.py

Build executables
-----------------

Windows:

    BUILD_WINDOWS.bat

Linux:

    ./build_linux.sh

macOS:

    ./build_macos.sh

See BUILDING.md for complete instructions.

Files that must remain beside the Python source
------------------------------------------------

- dreamcompress_gui.py
- despiria_pvr_tool_v1.2.1.py
- dreamcompress_logo.png
- dreamcompress_logo.ico, when available

License and release terms should be added by Kazetrigger before public release.
