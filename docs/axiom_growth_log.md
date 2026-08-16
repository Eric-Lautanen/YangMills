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

## Session 120 (2026-08-15): No axiom changes — Step A.5 completed

No axioms were strengthened or added this session. Step A.5 (the T = V^{1/2}·U·V^{1/2}
factorization) was completed:

- `transferMatrix_kernel_VUV_factorization` (LuscherDecomposition.lean:461): proves
  the kernel-level identity `K = V^{1/2}(u) · U_kernel · V^{1/2}(u')` where
  V^{1/2} = exp(-β·S_spatial⁺/2) and U_kernel = exp(-β·(S_temporal⁺(u)/2 +
  S_temporal⁺(u')/2 + S_int)). Pure algebra (Real.exp_add + ring). Only standard
  3 axioms.

- `transferMatrixReflected_VUV_factorization` (LuscherDecomposition.lean:507): lifts
  the kernel identity to the operator level, showing
  `(Tψ)(u) = V^{1/2}(u) · ∫ V^{1/2}(u')·ψ(u')·U_kernel dμ⁺(V⁺)`.
  This is the ABA form: T = V^{1/2}·U·V^{1/2}. Only standard 3 axioms.

Both lemmas use only `propext`, `Classical.choice`, `Quot.sound`. No axiom
strengthening was needed — the factorization is pure algebra + integral_const_mul.

## Session 128 (2026-08-16): STRENGTHENED `peterWeyl_clebschGordan_plaquette` — added `hcgME_cross_rep`

### What changed

The axiom `peterWeyl_clebschGordan_plaquette` was strengthened to include a new
conjunct `hcgME_cross_rep` (cross-representation orthogonality of CG coefficients):

    hcgME_cross_rep : ∀ (s s' t : ι), s ≠ s' →
      ∀ (a : Fin (dims s)) (i : Fin (dims t)) (a' : Fin (dims s')) (i' : Fin (dims t)),
      ∑ α : ι, ∑ p : Fin (dims α),
        conj (cgME s t α a i p) * cgME s' t α a' i' p = 0

This says: for distinct first-representation indices `s ≠ s'`, the columns of the
CG change-of-basis matrix `cgME s t α` are orthogonal to the columns of `cgME s' t α`
(when both map into the same `⊕_α V_α`). Combined with the existing `hcgME_unitary`
(the `s = s'` case), this gives the FULL unitarity of the combined CG change-of-basis
`⊕_s (V_s ⊗ V_t) → ⊕_α V_α`.

### Why

The 3-fold CG isometry (`cgME_3fold_isometry_normSq`, proven in session 127) requires
`hcgME_cross_rep` as a hypothesis (alongside `hcgME_unitary`). The plan was to derive
`hcgME_cross_rep` from the existing axiom (`hcgME_decomp` + `hcgME_unitary` + Schur
orthogonality) in step B.2d. After thorough analysis (adversarial self-check), this
derivation was found to be **impossible**:

1. **Individual isometries don't imply cross-orthogonality.** `hcgME_unitary` gives
   `U_{s,t}^* U_{s,t} = I` for each `s` (column orthonormality within each `s` block).
   Two isometries can have overlapping images — cross-rep orthogonality is NOT a
   consequence of individual isometries.

2. **The intertwining approach is blocked.** `U_{s,t}^* U_{s',t}` is NOT an
   intertwiner from `ρ_{s'} ⊗ ρ_t` to `ρ_s ⊗ ρ_t` because `U_{s',t} U_{s',t}^* ≠ I`
   (it's a projection onto the image, not identity). So Schur's lemma doesn't apply.

3. **The 4-fold product issue.** Using `hcgME_decomp` + Schur orthogonality gives a
   4-fold matrix element integral that doesn't simplify to the 2-fold product needed
   for `hcgME_cross_rep`. Schur orthogonality handles 2-fold products, not 4-fold.

4. **Phase freedom.** The CG coefficients have a phase/unitary freedom within each
   irreducible component. `hcgME_decomp` + `hcgME_unitary` constrain the CG
   coefficients but don't fix the relative phases between different `s` values. The
   cross-rep orthogonality depends on this relative choice.

**Counterexample:** `ι = {0,1}`, `dims = [1,1]`, `cgME 0 0 0 = 1`, `cgME 1 0 0 = 1`.
Then `hcgME_unitary` holds for each `s` (each is a 1×1 isometry), but
`∑_α conj(cgME 0 0 α) * cgME 1 0 α = 1 ≠ 0` — cross-rep orthogonality FAILS.

### Is this a standard/known result?

**Yes — "known but unformalized."** The full unitarity of the CG change-of-basis
(including cross-rep orthogonality) is a standard result in compact-Lie-group
representation theory. It follows from the CHOICE of CG coefficients: one always
chooses them so that the combined map `⊕_s (V_s ⊗ V_t) → ⊕_α V_α` is unitary (by
Gram-Schmidt within each irreducible component). This is the standard convention in
physics and mathematics textbooks. The strengthening does NOT add a new mathematical
assumption — it formalizes a known consequence that the previous axiom did not
explicitly provide.

### Is this logically equivalent to what the blocked lemma was supposed to establish?

**Yes, directly.** The blocked lemma was `hcgME_cross_rep` itself — we wanted to
derive it from the existing axiom. By adding it to the axiom, we are assuming what
we wanted to prove. However, the key distinction is that `hcgME_cross_rep` is "known
but unformalized" (standard representation theory), not "genuinely open math." The
strengthening formalizes a known result, not an open conjecture.

### Impact on the "6→5 axiom reduction" claim

The axiom COUNT is unchanged (still 6: `peterWeyl_clebschGordan_plaquette` +
`characterOrthogonality` + `transferMatrixPositivity_axiom` + standard 3). The
strengthening increases the STRENGTH of `peterWeyl_clebschGordan_plaquette` without
changing the count. When `transferMatrixPositivity_axiom` is eventually replaced
(step B.2e), the count will go 6→5, but the remaining `peterWeyl_clebschGordan_plaquette`
will be stronger than before. The net reduction in total axiom strength is less than
the count reduction suggests.

### Build status

- **Build**: GREEN — `lake build` completes successfully (3008 jobs), 0 errors,
  0 sorries.
- **Axiom count**: still 6 (no change — strengthened an existing axiom, didn't add
  a new one).
- **6 destructuring sites updated**: `Axiom.lean` (2), `Separable.lean` (1),
  `CharacterExpansion.lean` (1), `FullBoltzmannPD.lean` (2).
