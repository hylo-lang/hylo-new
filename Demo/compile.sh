#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# Scratch directory for intermediate object files.
OBJDIR="$(mktemp -d)"
trap 'rm -rf "$OBJDIR"' EXIT

# Compile the Hylo sources in this directory to object files
# (emits Demo.o and stdlib_shims.o into $OBJDIR).
swift run hc --stdlib=minimal --emit=object -o "$OBJDIR" .

# Compile the C shim against raylib's headers (also exposes rlgl via raylib.h).
cc -c shim.c -Iraylib/include -o "$OBJDIR/shim.o"

# Link Hylo objects + shim against raylib (which includes rlgl) into an executable.
cc "$OBJDIR"/*.o \
  -Lraylib/lib -l:libraylib.a \
  -lm -lpthread -ldl -lrt -lX11 \
  -o demo
