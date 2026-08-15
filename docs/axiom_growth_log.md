# Axiom Growth Log

This file logs every instance where an axiom or bundled hypothesis was
strengthened (made more powerful) to get past a stuck proof, per the
project's standing instructions. Each entry records: what changed, why,
whether the new form is a standard/known result or introduced specifically
to unstick the proof, and whether it might be logically equivalent to or
close to what the blocked lemma was supposed to establish.

See also `docs/honest_frontier_audit.md` Part 1 for the full audit of the
seven strengthenings of `peterWeyl_clebschGordan_plaquette`.

---

## Session 117 (2026-08-15): No axiom changes — analysis session

No axioms were strengthened or added this session. This was an analysis
session that read the full state of STEP 6 (closing
`transferMatrixPositivity_axiom`).

### Key finding: Step A.2 already done

The handoff for session 117 listed "Step A.2: Show V is positive — connect
group-PD to operator positivity" as a TODO. On reading the codebase, this
is **already done**:

- `PositiveDefinite.integralOperator_nonneg`
  (`PositiveDefiniteIntegral/IntegralOperator.lean:140`) proves: for a
  compact group `G` with probability measure `μ`, a continuous
  positive-definite function `φ`, and continuous `f`,
  `∫∫ f(x)·conj(f(y))·φ(x⁻¹·y) dμ dμ ≥ 0`. This is the continuous analogue
  of the `PositiveDefinite` definition — exactly the "group-PD → positive
  integral operator" connection.

- `spatialBoltzmannPD` (`ReflectionPositivity/FullBoltzmannPD.lean:258`)
  proves the spatial Boltzmann factor is PD (Step A.1).

So Steps A.1 and A.2 of the Lüscher decomposition are already in place.
The remaining work is:
- Step A.3: Define U (temporal transfer operator) — requires the 3D
  cascade kernel, which is the crux (Step B).
- Step A.4: Show T = V^{1/2}·U·V^{1/2} — requires the action split.
- Step A.5: ABA ≥ 0 — algebraic, but in the concrete setting reduces to
  a change of variables built into the factorization.

### The crux: 3D off-diagonal cascade

- `single_site_3D_luscher_integral` (PeterWeyl/Site3DIntegral.lean:484):
  integrates ONE temporal link in 3 plaquettes — DONE.
- `cg_unitarity_nonneg` (Site3DIntegral.lean:725): DIAGONAL case
  (barred=unbarred → |C|² ≥ 0) — DONE.
- OFF-DIAGONAL case (multi-site, different plaquette structures → product
  of two DIFFERENT CG sums, NOT |C|²) — NOT formalized. This is the crux.

### No axiom strengthening needed

The path forward does NOT require strengthening any axiom. The 3D cascade
uses the existing `peterWeyl_clebschGordan_plaquette` axiom (which provides
CG decomposition + Schur orthogonality). The obstacle is formalization
effort, not missing assumptions.
