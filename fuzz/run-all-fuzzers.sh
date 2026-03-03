#!/usr/bin/env bash
# Script to run all fuzz targets for a specified duration

set -e

DURATION=${1:-60}  # Default to 60 seconds if not specified

echo "Running all fuzz targets for ${DURATION} seconds each..."
echo ""

TARGETS=("fuzz_getopt" "fuzz_optstring" "fuzz_cstr")

for target in "${TARGETS[@]}"; do
    echo "========================================"
    echo "Running: $target"
    echo "========================================"
    cargo +nightly fuzz run "$target" -- -max_total_time="$DURATION" 2>&1 | tail -20
    echo ""
    echo "Completed: $target"
    echo ""
done

echo "========================================"
echo "All fuzz targets completed!"
echo "========================================"
echo ""
echo "Check fuzz/artifacts/ for any crashes found"
