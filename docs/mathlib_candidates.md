# Mathlib Candidates: Running List of Possibly-Novel / Submittable Contributions

**Purpose.** This is a running catalog of results, lemmas, and proof techniques
produced in the course of the Yang-Mills formalization effort that are (a)
independent of the open conjecture, (b) appear to be absent from Mathlib, and
(c) may be worth upstreaming or writing up independently — *regardless of
whether the top-level Millennium Prize theorem ever closes*. Each entry is
classified as **standard-but-unformalized** (known in the literature, just not
in Lean) or **possibly-novel formulation** (the specific packaging / statement
does not appear to be in the literature or in any checked Lean repo).

The two already-packaged standalone files in the repo root
(`PositiveDefiniteKernelMathlibCandidate.lean`,
`PositiveDefiniteMathlibCandidate.lean`) and the companion `MATHLIB_SUBMISSION.md`
are the **priority** candidates. This document extends that list with everything
else discovered along the way, and is the place to record new candidates as they
are found.

---

## Status legend

- **Packaged** — already extracted into a standalone, Yang-Mills-free file with
  `#print axioms` verified (only `propext, Classical.choice, Quot.sound`).
- **Ready to package** — proved, 0 sorries, 0 custom axioms, but not yet
  extracted into a standalone file. Needs a dependency-stripping pass.
- **Embedded** — proved inside the Yang-Mills namespace; would need extraction
  and generalization before submission.
- **Technique** — a formalization pattern, not a theorem; documented for reuse.

---

## 1. Mercer-type positive-definite kernels (PRIORITY — possibly-novel formulation)

**Status:** Packaged. `PositiveDefiniteKernelMathlibCandidate.lean` + §1a of
`MATHLIB_SUBMISSION.md`.

**Statement.** A kernel `K : X → X → ℂ` on an arbitrary (pseudo)metric space is
*Mercer-positive-definite* if `Σ_{i,j} c_i · conj(c_j) · K(x_i, x_j) ≥ 0` for
every finite set and coefficients. If `X` is compact with a probability
measure, `K` is continuous Mercer-PD, and `f` is continuous, then
`∫∫ f(x) · conj(f(y)) · K(x, y) dμ dμ ≥ 0`.

**Why possibly-novel.** Mathlib's existing PD machinery
(`Mathlib.Analysis.InnerProductSpace.Reproducing`) is *finite-matrix* PSD
(`RKHS.posSemidef_kernel` gives a `Matrix.PosSemidef`). The candidate here is
the *continuous / measure-theoretic* generalization: the kernel is a function
on an arbitrary space and positivity is the integral-operator inequality. Full
grep + Loogle searches (documented in `MATHLIB_SUBMISSION.md` §3) found no
match in Mathlib. The external repo `Vilin97/lean-pool` covers only the
*group-theoretic* case; the Mercer-type version has no equivalent there either.

**Substance.** Standard analysis (Riemann-sum approximation + Heine–Cantor
uniform continuity). The contribution is the *formulation and packaging*, not
depth. Honest: this is "useful infrastructure absent from Mathlib," not a deep
theorem.

**Axioms.** `propext, Classical.choice, Quot.sound` only.

---

## 2. Group-theoretic positive-definite functions (standard-but-unformalized)

**Status:** Packaged. `PositiveDefiniteMathlibCandidate.lean` + §1b of
`MATHLIB_SUBMISSION.md`.

**Statements.**
- `PositiveDefinite.integral` — an integral average of PD functions is PD.
- `PositiveDefinite.integralOperator_nonneg` — a continuous PD function `φ` on
  a compact group gives `∫∫ f(x)·conj(f(y))·φ(x⁻¹y) dμ dμ ≥ 0`.
- `PositiveDefinite.sum_nonneg_of_map` — the quadratic form with a
  (possibly non-injective) mapped index set is non-negative (the key grouping
  argument underpinning both integral results).

**Why standard.** The Godement–Bochner characterization of PD functions and
the fact that PD kernels define positive integral operators are classical
(harmonic analysis on compact groups; Folland, *A Course in Abstract Harmonic
Analysis*). The Schur (Hadamard) product theorem for group-PD functions is
also classical.

**Why unformalized.** Mathlib has no `PositiveDefinite` definition for
group-valued functions (its PD work is matrix/quadratic-form based). The
external `Vilin97/lean-pool` has a functionally equivalent `IsPositiveDefinite`
on an additive group, but with a different API (`structure` vs `Prop`,
`Fin`-vs-`Finset`-indexed). The `integral` and `integralOperator_nonneg`
double-integral results have no equivalent in `lean-pool` or Mathlib.

**Axioms.** `propext, Classical.choice, Quot.sound` only.

---

## 3. Lüscher cascade integrals (Schur-orthogonality temporal-link integration)

**Status:** Embedded in `src/lean/YangMills/Proofs/PositiveDefinite.lean`.
Ready to package (general group `G`, no lattice).

**Statements.**
- `luscher_key_identity` (`PositiveDefinite.lean:1110`) — the single-link
  identity `∫_G χ_γ(g·h)·χ_{γ'}(g⁻¹·k) dμ = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)`.
- `luscher_2site_cascade_coeff` (`PositiveDefinite.lean:2119`) — the 2-site
  cascade: `∫∫ Σ_{s,t} F(s,t)·χ_s(g₀Wg₁⁻¹)·χ_t(g₁Vg₀⁻¹) = Σ_s F(s,s)·(1/d_s)·χ_s(WV)`.
- `luscher_3site_cascade_coeff` (`PositiveDefinite.lean:2350`) — the 3-site
  cascade: `∫∫∫ Σ_{s,t,u} F(s,t,u)·χ_s(g₀W₀g₁⁻¹)·χ_t(g₁W₁g₂⁻¹)·χ_u(g₂W₂g₀⁻¹)
  = Σ_s F(s,s,s)·(1/d_s)²·χ_s(W₀W₁W₂)`.

**Why standard-but-unformalized.** These are the Schur-orthogonality
calculations at the heart of Lüscher's transfer-matrix construction for lattice
gauge theory (Lüscher 1977; Osterwalder-Seiler). The single-link identity is a
direct application of the Great Orthogonality Theorem; the 2- and 3-site
cascades are Fubini iterations of it. They are "known to lattice gauge
theorists" but the explicit, fully-managed (integrability + Fubini exchange +
diagonal collapse + `χ(WV) = χ(VW)` via trace-commutativity) formalization is
genuine work and is not in Mathlib.

**Substance.** The *mathematics* is a standard Schur-orthogonality
calculation. The *formalization* is nontrivial: each cascade requires
discharging integrability of every `(s,t)` term, exchanging the character sum
with the integral (Fubini for finite sums), applying the key identity, and
collapsing the Kronecker-`δ` diagonal. The 3-site cascade is an inductive
extension (integrate out `g₁` first, then apply the 2-site cascade). This is a
clean, reusable "Schur-orthogonality cascade" API that Mathlib does not have.

**Axioms.** `propext, Classical.choice, Quot.sound, characterOrthogonality`
(the Great Orthogonality Theorem, itself a candidate for separate upstreaming —
see §6 below).

**Submittability.** Good candidate, *conditional* on `characterOrthogonality`
being accepted or proved first (the cascade lemmas depend on it). If Schur
orthogonality lands in Mathlib, the cascade lemmas are a natural follow-up.

---

## 4. Character-kernel integral non-negativity

**Status:** Embedded in `src/lean/YangMills/Proofs/PositiveDefiniteIntegral.lean`.
Ready to package.

**Statements.**
- `character_kernel_integral_nonneg` (`PositiveDefiniteIntegral.lean:1400`) —
  for a compact group with involution-invariant probability measure, and a
  kernel `K(W,V) = Σ_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`,
  `∫∫ f(W)·f(V⁻¹)·K(W,V) dμ dμ ≥ 0`.
- `character_expansion_nonneg` / `character_expansion_nonneg_shared`
  (`PositiveDefiniteIntegral.lean`) — the more general "separable expansion"
  non-negativity: `K(x,y) = Σ_i a_i · Φ_i(x)·conj(Φ_i(y))` with `a_i ≥ 0`
  implies `∫∫ g(x)·g(y)·K ≥ 0` (and the shared-`z` variant).
- `cascade_integral_nonneg` (`PositiveDefiniteIntegral.lean:1275`) — combines
  the 2D character-level cascade with `character_kernel_integral_nonneg`.

**Why standard-but-unformalized.** This is the standard fact that a
non-negative-weighted sum of characters (each PD) defines a positive integral
operator. It follows from `χ_ν(W·V) = Σ_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`
(unitarity) + the separable-expansion lemma. Classical in spirit (it is the
mechanism behind Lüscher's positivity), but the clean packaging as
"character-kernel → non-negative integral" is not in Mathlib.

**Axioms.** `propext, Classical.choice, Quot.sound` (the
`character_kernel_integral_nonneg` lemma itself does *not* depend on
`characterOrthogonality` — it uses only the unitarity trace expansion and the
separable-expansion lemma). This makes it more readily submittable than the
cascade lemmas.

**Submittability.** Strong candidate — fewer dependencies than the cascades,
clean statement, pure group/measure theory.

---

## 5. The `addVectorPeriodic` whnf-timeout workaround (TECHNIQUE)

**Status:** Technique. Documented in `ReflectionPositivity.lean` (comments at
`fullBoltzmannPD`, `spatialBoltzmannPD`) and in the design doc §8.11.68.

**The problem.** `addVectorPeriodic` (the periodic-lattice addition) is
defined with a `match μ with | 0 => ... | 1 => ... | 2 => ... | 3 => ...` on
`Fin 4`. When `μ` is a *variable* (not a literal), `whnf` / `isDefEq` gets
stuck trying to reduce the match, causing timeouts in `PositiveDefinite.congr`
and similar tactics that need to check definitional equality of the conclusion.

**The workaround.** Build `PositiveDefinite` proofs *without* a declared
conclusion type (so no conclusion defeq check fires), then transfer PD with
`PositiveDefinite.congr` applied to a function equality proved by `funext` +
`rfl` (which is alpha-equivalent and fast, avoiding the stuck match). This
sidesteps the `whnf` entirely.

**Why worth recording.** Anyone formalizing lattice gauge theory (or any
theory with `Fin n`-indexed matches over variable directions) will hit this.
It is a reusable formalization pattern, not a theorem. Not a Mathlib candidate
per se, but worth a note in any lattice-QFT formalization guide.

---

## 6. Schur orthogonality / Great Orthogonality Theorem (candidate, currently an AXIOM)

**Status:** Currently the axiom `characterOrthogonality` in
`PositiveDefinite.lean`. **NOT submittable as-is** — it is assumed, not proved.

**Statement.** For irreducible unitary representations of a compact group with
normalized Haar measure: `∫ (ρ_λ g)_{ij}·conj((ρ_μ g)_{kl}) dμ =
δ_{λμ}δ_{ik}δ_{jl}/dim(λ)` (the Great Orthogonality Theorem), stated as a
3-part conjunction (integrability + diagonal + off-diagonal).

**Why listed here.** This is a *major* Mathlib gap. Schur orthogonality is a
foundational result of compact-group representation theory and is the
dependency of the cascade lemmas (§3). If it were proved in Mathlib (from
Haar measure + irreducibility + Schur's lemma), the cascade lemmas and
`character_kernel_integral_nonneg` would become axiom-free (modulo the standard
three). This is the single most impactful upstream contribution the project
could motivate. It is *not* something this project has proved — it is an axiom
here — but it is the natural target for anyone wanting to de-axiomatize the
cascade results.

**Substance.** Substantial — own chapter in Fulton & Harris / Folland. But
well-understood and finite: it is a theorem with a known proof, not an open
problem. A Mathlib PR proving Schur orthogonality from Haar measure would be a
genuine contribution.

---

## 7. The §8.11.67 pedagogical clarification (NOT a theorem — a write-up candidate)

**Status:** Analysis, documented in `docs/transfer_matrix_positivity_design.md`
§8.11.67.

**Content.** The explicit articulation of *why* the group-PD of the full
Boltzmann factor `B` does **not** directly imply non-negativity of the
reflection integral `I = ∫ f(U)·f(θU)·B(U) dμ` (because `B(U) ≠ B(g⁻¹·h)` and
`θ` is not a group homomorphism), *why* the full character expansion fails
(it produces `Â_w · Â_{w*}` with `w* ≠ dual(w)`, i.e. a product of Fourier
coefficients at *different* weights, not `|Â_w|²`), and *why* the Lüscher
decomposition `T = V^{1/2}·U·V^{1/2}` is the correct mechanism (temporal
plaquettes → character expansion + Schur orthogonality → kernel
`Σ a_s χ_s(W·V)` with `a_s ≥ 0`; spatial plaquettes → Schur product → PD
multiplication operator).

**Why worth recording.** This distinction is known to experts
(Lüscher, Osterwalder-Seiler) but is frequently glossed in informal treatments,
where "the Boltzmann factor is PD, hence reflection positivity" is stated
without the caveat that the *group*-PD and the *reflection*-positivity integral
are structurally different. The explicit `Â_w · Â_{w*} ≠ |Â_w|²` obstruction
and the spatial/temporal split is a clean pedagogical contribution. Not a
Mathlib candidate, but a candidate for a short expository note.

---

## Summary table

| # | Candidate | Type | Axioms | Submittability |
|---|-----------|------|--------|----------------|
| 1 | Mercer-type `PositiveDefiniteKernel` | possibly-novel formulation | std 3 | **Priority** — packaged, no deps |
| 2 | Group-PD `PositiveDefinite` + integral | standard-but-unformalized | std 3 | **Packaged** — overlaps lean-pool |
| 3 | Lüscher cascade integrals | standard-but-unformalized | std 3 + Schur | Ready to package (needs Schur) |
| 4 | Character-kernel integral non-negativity | standard-but-unformalized | std 3 | **Strong** — few deps |
| 5 | `addVectorPeriodic` whnf workaround | technique | — | Document for reuse |
| 6 | Schur orthogonality (GOT) | standard, currently AXIOM | — | **High-impact target** (not proved here) |
| 7 | §8.11.67 RP obstruction clarification | expository | — | Write-up candidate |

**Honest bottom line.** The genuinely *novel* contribution (in formulation, not
depth) is #1 (Mercer-type kernels). Items #2–#4 are standard mathematics that
Mathlib happens to lack — valuable infrastructure, but not new theorems. Item
#6 is the highest-impact *target* but is not something this project has proved.
The rest are documentation / technique. None of these constitute progress on
the Millennium Prize problem; they are reusable infrastructure that fell out
of the attempt.

---

## Generalization investigation: `integralOperator_nonneg` (2026-08-11)

The current `PositiveDefiniteKernel.integralOperator_nonneg` hypotheses are:
`PseudoMetricSpace X`, `CompactSpace X`, `BorelSpace X`,
`SecondCountableTopology X`, `IsProbabilityMeasure μ`,
`Continuous (Function.uncurry K)`, `Continuous f`.

Possible generalizations (investigated, not yet implemented):

1. **`IsProbabilityMeasure` → `IsFiniteMeasure`** (straightforward). The
   proof uses `μ.real univ = 1` in the Riemann-sum bound (the partition
   measures sum to 1). For a finite measure, they sum to `μ.real univ < ∞`,
   and the error bound becomes `ε · μ.real univ` instead of `ε`. The
   non-negativity conclusion is unchanged. This is a clean, low-risk
   generalization — the result holds for any finite measure, not just
   probability measures.

2. **`PseudoMetricSpace` → `UniformSpace`** (clean). The Heine–Cantor
   uniform-continuity argument works in any compact uniform space, not just
   metric spaces. Mathlib has `CompactSpace.uniformContinuous_of_continuous`
   for uniform spaces. This would broaden the applicability without changing
   the proof structure.

3. **`Continuous f` → `Integrable f`** (substantial). The Riemann-sum
   approximation requires continuity. Extending to merely integrable `f`
   would require approximating `f` by continuous functions (density of
   `C_c(X)` in `L¹(μ)` for Radon measures on locally compact spaces) and
   passing to the limit. More machinery, but a standard technique.

4. **`CompactSpace` → locally compact + bounded support** (substantial).
   Without compactness, one needs `K` uniformly continuous and bounded on
   the support of `μ`, or works with `C_c(X)`. This would require
   partition-of-unity or tightness arguments.

**Recommendation:** generalizations 1 and 2 are low-risk and worth doing
before submission. Generalizations 3 and 4 are substantial and better left
for a follow-up PR.
