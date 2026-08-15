# Archived Documents

These documents are historical/resolved and kept for reference. They are not
actively maintained.

| Document | Status | Why archived |
|---|---|---|
| `hadd_issue.md` | Resolved | The `hadd` hypothesis issue was resolved by switching to periodic boundary conditions (`PeriodicSite T L`). The fix is fully implemented. |
| `periodic_bc_plan.md` | Completed | The implementation plan for periodic boundary conditions. All steps completed; `PeriodicSite`, `addVectorPeriodic`, `reflectSitePeriodic` are in `Lattice.lean`. |
| `found_issues.md` | Mostly resolved | Historical record of found issues (reflection positivity hypothesis, transfer matrix identity, Tr(gh) PD obstruction). All resolved via axiomatization + the closure plan in `transfer_matrix_positivity_design.md`. |
| `setup.md` | Outdated | Referenced old project structure (pre-Proofs/ directory, Coq/Z3 stubs). Current structure is in `README.md`. |

For current status, see:
- `docs/STATUS.md` — detailed proof-state tracking
- `docs/transfer_matrix_positivity_design.md` — active design doc (Lüscher decomposition)
- `docs/path_forward.md` — path forward to close `transferMatrixPositivity_axiom`
- `GOALS.md` — high-level goals and honest status
