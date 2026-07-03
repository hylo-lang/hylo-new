#!/usr/bin/env bash
# Formats the repository's Swift sources according to the Hylo coding guidelines.
#
# Usage: Tools/format.sh [--check] [<path> ...]
set -euo pipefail
cd "$(dirname "$0")/.."
swift run --package-path Tools/Formatter hylo-format "$@"
