#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Build one certificate at a time. Children inherit the address-space limit,
# so a large kernel reduction can fail without exhausting host memory.
ulimit -v 14680064
ulimit -c 0
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=65536 LEAN_MAIN_USE_THREAD=1 MALLOC_ARENA_MAX=2
config=$(mktemp --suffix=.toml .hubbard-lake.XXXXXX)
trap 'rm -f "$config"' EXIT
cat lakefile.toml > "$config"
printf '\nweakLeanArgs = ["-j1", "-s65536"]\n' >> "$config"
for mask in 0 1 2 3 4 5 6 7; do
    lake -f "$config" build "Grain.HubbardData.Mask${mask}"
done
lake -f "$config" build Grain.HubbardBenchmark Grain.HubbardOperators Grain.CooperBenchmark
lake -f "$config" env leanchecker Grain.HubbardBenchmark Grain.HubbardOperators Grain.CooperBenchmark
