#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if (( $# > 1 )) || [[ ${1:-} != "" && ${1:-} != --prediction-only ]]; then
  echo "usage: $0 [--prediction-only]" >&2
  exit 2
fi

# A 14 GiB address-space limit leaves headroom for Lake under a 16 GB budget.
ulimit -v 14680064
ulimit -c 0
export LEAN_NUM_THREADS=2 LEAN_STACK_SIZE_KB=65536 LEAN_MAIN_USE_THREAD=1 MALLOC_ARENA_MAX=2

config=$(mktemp --suffix=.toml .dfpt-lake.XXXXXX)
trap 'rm -f "$config"' EXIT
cat lakefile.toml > "$config"
printf '\nweakLeanArgs = ["-j2", "-s65536"]\n' >> "$config"

lake -f "$config" build Grain.DFPTFivePrediction
if [[ ${1:-} != --prediction-only ]]; then
  lake -f "$config" build Grain.DFPTFive
  for case_index in 0 1 2 3; do
    lake -f "$config" build "Grain.DFPTSeven.Case$case_index"
  done
  lake -f "$config" build Grain.DFPTSevenContrast
fi

export LEAN_NUM_THREADS=1
for module in SparseForm DFPTAssembly DFPTSector DFPTCertificate DFPTReduction DFPTShell DFPTFivePrediction; do
  lake -f "$config" env leanchecker -v "Grain.$module"
done
if [[ ${1:-} == --prediction-only ]]; then
  exit 0
fi
lake -f "$config" env leanchecker -v Grain.DFPTFive
for case_index in 0 1 2 3; do
  lake -f "$config" env leanchecker -v "Grain.DFPTSeven.Case$case_index"
done
# leanchecker treats a module name as a prefix. Keep the combined theorem
# outside Grain.DFPTSeven so replaying it cannot start all four cases together.
lake -f "$config" env leanchecker -v Grain.DFPTSevenContrast
