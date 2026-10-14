# Analysis and experiment scripts

The scripts remain flat here so their historical SHA-256 source hashes stay
unchanged. Their prefixes distinguish canonical research (`research.py`,
`finalize.py`), early grand-canonical work (`grandcanonical_*.py`), and the
phenomenological-RG branch (`prg_*.py`).

Run PRG scripts from the repository root, for example
`python3 scripts/prg_stage5_integrity.py`. The early grand-canonical scripts
with working-directory-relative paths should be run from this directory.
The relative symlinks here expose the original data/results paths and source
names; the target output directories are empty placeholders. They do not
duplicate raw data or compiled code. `build/` is generated locally and ignored
by Git. Historical data and certificates were removed, so audit scripts that
require them must follow a fresh experiment run.
