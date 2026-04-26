#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# Locate the Hylo compiler `hc`, building it on demand.
HYLO_ROOT="$(cd .. && pwd)"
HC="$HYLO_ROOT/.build/debug/hc"
if [[ ! -x "$HC" ]]; then
  (cd "$HYLO_ROOT" && swift build --product hc)
fi

# Scratch directory for intermediate object files.
OBJDIR="$(mktemp -d)"
trap 'rm -rf "$OBJDIR"' EXIT

# Compile the Hylo sources in this directory to object files
# (emits Demo.o and stdlib_shims.o into $OBJDIR).
"$HC" --stdlib=minimal --emit=object -o "$OBJDIR" .

# Compile the C shim against raylib's headers (also exposes rlgl via raylib.h).
cc -c shim.c -Iraylib/include -o "$OBJDIR/shim.o"

# Link Hylo objects + shim against raylib (which includes rlgl) into an executable.
cc "$OBJDIR"/*.o \
  -Lraylib/lib -l:libraylib.a \
  -lm -lpthread -ldl -lrt -lX11 \
  -o demo
