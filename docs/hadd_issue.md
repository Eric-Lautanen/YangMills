# Architectural Issue: `hadd` Hypothesis (Resolved)

## Problem (Historical)

The `gibbsExpectationZ4_reflection_positive` lemma in `LatticeMeasure.lean` had the hypothesis:

```lean
hadd : ∀ n, n ∈ sites → addVector n 0 ∈ sites
```

This requires the finite lattice `sites` to be **closed under forward time translation**:
if a site `n` is in the lattice, then `n + e₀` (the time-forward neighbor) must also be in the lattice.

## Why This Was Problematic

For a **finite** set `sites : Finset Z4Site`, this closure condition forces `sites = ∅`:

1. If `sites` is nonempty, take the site `n` with maximum time coordinate `m = n.1`.
2. By `hadd`, `addVector n 0 ∈ sites`, and `(addVector n 0).1 = n.1 + 1 = m + 1`.
3. But `m` is the maximum time coordinate, so `m + 1 ≤ m`, a contradiction.

The old proof of `gibbsExpectationZ4_reflection_positive` exploited exactly this: the nonempty case
derives a contradiction, so the theorem was only non-vacuously useful for `sites = ∅`.

## Resolution: Periodic Boundary Conditions

The fix was to replace the infinite lattice `Z4Site = ℤ⁴` with a periodic lattice
`PeriodicSite T L = ZMod T × ZMod L × ZMod L × ZMod L` (defined in `Lattice.lean`).

In this setting:
- **`addVector`** wraps around modulo `T`/`L` automatically via ZMod addition, making the lattice
  closed under forward time translation for **any** finite set of sites (in particular, `Finset.univ`).
- **`reflectSite`** maps time `t ↦ -t` (mod T), which is involutive.
- The `hadd` hypothesis is no longer needed because we always work with the full lattice
  `Finset.univ`, which is trivially closed.

## Current Status

The periodic boundary condition approach is fully implemented in `ReflectionPositivity.lean`:

1. **PeriodicSite** structure with `addVectorPeriodic` and `reflectSitePeriodic` (Lattice.lean)
2. **OS decomposition**: `wilsonActionOSPositive`, `wilsonActionOSNegative`, `wilsonActionOSInterface`
   — decomposing the Wilson action into positive-time, negative-time, and interface parts.
3. **Algebraic lemmas proved**:
   - `total_decomposition_os_periodic`: S_W = S_OS⁺ + S_OS⁻ + S_OS_int
   - `neg_action_reflection_os_periodic`: S_OS⁻[U] = S_OS⁺[θU]
   - `interface_action_reflection_symmetric_os_periodic`: S_OS_int[θU] = S_OS_int[U]
   - `trace_plaquetteProduct_reflect_all`: trace equality for all plaquettes
   - `plaquetteContribution_reflect_eq_all`: contribution equality for all plaquettes
4. **Gibbs expectation proof**: `gibbsExpectationPeriodic_reflection_positive` reduces
   the reflection positivity condition to ∫ G·θG dμ₀ ≥ 0 (all algebraic steps completed).
5. **One remaining gap — not a `sorry`**: The final positivity ∫ G·θG dμ₀ ≥ 0 requires
   the Peter–Weyl theorem on SU(N) (transfer matrix argument, Osterwalder-Seiler 1979, §3).
   In the current source, `gibbsExpectationPeriodic_reflection_positive` closes via
   `exact transferMatrixPositivity_axiom ...` (ReflectionPositivity.lean:2341/2441), a
   genuine axiom — the closure plan against it is tracked in
   `docs/transfer_matrix_positivity_design.md` §8.11.

## Impact

- The old `Z4Expectation` structure and `wilsonZ4Expectation` are deprecated in favor of
  `PeriodicExpectation` and `wilsonPeriodicExpectation`.
- The `hadd` hypothesis is no longer required for the reflection positivity proof.
- The `lattice_ym_reflection_positive_periodic` theorem provides a genuine reflection positivity
  certificate for the Wilson action on periodic lattices, modulo the transfer matrix positivity step.

## Old Fix Options (for reference)

### Option B: Remove `hadd`

Prove reflection positivity without the closure hypothesis. The `hadd` hypothesis is used in:
- The decomposition lemmas (to ensure reflected plaquette sites remain in the lattice)
- Transitive closure arguments

Without `hadd`, these lemmas need to handle plaquettes whose reflected corners fall outside
the lattice. This requires either:
- Restricting to lattices that are reflection-invariant (`hsites` already provides this)
- Handling boundary plaquettes separately

**Implementation complexity**: Medium. Would require a different proof approach that works
with boundaries.

### Option C: Infinite Lattice

Work with an infinite lattice (no `Finset` constraint on `sites`). This avoids the finiteness
issue but requires more measure-theoretic infrastructure (infinite product measures,
σ-finiteness, etc.).

**Implementation complexity**: High. Requires significant additional measure theory
infrastructure.
