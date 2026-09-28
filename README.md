# eezott

The typed front end of Eezo: a cubical type theory (CCHM: De Morgan interval, PathP, partial elements, transp/hcomp,
Glue; universe levels; inductive families and higher inductive types with their eliminators; mutual blocks; implicit
arguments; numerals; machine words) whose well-typed programs erase to eezoc source. `eezott -A` prints the elaborated
core as a Cubical Agda module and `-C` as a cubicaltt module, for the differential test (`tests/fuzz.sh`).

Build: `mk` (see [mk](https://github.com/Levalicious/mk), [mkroot](https://github.com/Levalicious/mkroot)); links
[libeezo](https://github.com/Levalicious/libeezo) from `../libeezo`. Dependencies and their pinned commits:
`deps.lock`; `ci/deps.sh` fetches them beside this checkout - the workspace layout the
[umbrella](https://github.com/Levalicious/umbrella) repository lays out.

Tests: `tests/eezott.sh` (the gate: every program under `tests/tt` type-checks, erases, compiles and runs to the value
an oracle computes) needs eezoc, eezo and the stdlib's `tt/` beside it; `tests/fuzz.sh` needs Agda (and cubicaltt for
its third leg, skipped when absent) and runs in CI on `workflow_dispatch` only. `EEZO_WS`, `EEZOTT`, `EEZOC`, `EEZO`,
`LIB` override where the scripts look.
