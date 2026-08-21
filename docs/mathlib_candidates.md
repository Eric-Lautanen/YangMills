# Mathlib Candidates: Running List of Possibly-Novel / Submittable Contributions

**Purpose.** This is a running catalog of results, lemmas, and proof techniques
produced in the course of the Yang-Mills formalization effort that are (a)
independent of the open conjecture, (b) appear to be absent from Mathlib, and
(c) may be worth upstreaming or writing up independently — *regardless of
whether the top-level Millennium Prize theorem ever closes*. Each entry is
classified as **standard-but-unformalized** (known in the literature, just not
in Lean) or **possibly-novel formulation** (the specific packaging / statement
does not appear to be in the literature or in any checked Lean repo).

The three already-packaged standalone files in the repo root
(`PositiveDefiniteKernelMathlibCandidate.lean`,
`PositiveDefiniteMathlibCandidate.lean`,
`PositiveDefiniteKernelGeneral.lean`) and the companion `MATHLIB_SUBMISSION.md`
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
| 8 | General L² integralOperator_nonneg (bounded diag) | possibly-novel formulation | std 3 | **Packaged** — `PositiveDefiniteKernelGeneral.lean`, VERIFIED, no sorry |
| 9 | `repCharacter_cyclic2`: 2-factor cyclic invariance | standard-but-unformalized | std 3 | Embedded — clean, few deps |
| 10 | `cgME_isometry_normSq`: Parseval for unitary change-of-basis | standard-but-unformalized | std 3 | Ready to package — pure algebra |

**Honest bottom line.** The genuinely *novel* contribution (in formulation, not
depth) is #1 (Mercer-type kernels). Items #2–#4 are standard mathematics that
Mathlib happens to lack — valuable infrastructure, but not new theorems. Item
#6 is the highest-impact *target* but is not something this project has proved.
The rest are documentation / technique. None of these constitute progress on
the Millennium Prize problem; they are reusable infrastructure that fell out
of the attempt.

---

## Generalization investigation: `integralOperator_nonneg` (2026-08-11)

### The question (from Mathlib review, Yaël Dillies)

Does `PositiveDefiniteKernel.integralOperator_nonneg` generalize beyond compact `X`
and continuous `K`/`f` to an arbitrary measure space with merely integrable `K` and
`f`, via simple-function approximation plus monotone/dominated convergence?

### Answer: the generalization IS true, but NOT via simple-function approximation

The result generalizes to: **a finite measure space `(X, μ)`, a pointwise PD kernel
`K` with `K ∈ L²(μ⊗μ)` and `K(x,x)` measurable, and `f ∈ L²(μ)`**, giving
`∫∫ f(x)·conj(f(y))·K(x,y) dμ dμ ≥ 0`. But the proof uses a completely different
technique (truncation + Moore–Aronszajn feature map + Bochner integral), not
simple-function approximation.

### Why simple-function + MCT/DCT does NOT work

The current proof approximates `∫∫ f(x)·conj(f(y))·K(x,y) dμ dμ` by Riemann sums
`Σ_{i,j} c_i·conj(c_j)·K(x_i, x_j)` (with `c_i = f(x_i)·μ(A_i)`), each non-negative
by `sum_nonneg_of_map` (the pointwise PD condition). Continuity of `K` bridges the
gap: `K` is nearly constant on small sets, so the Riemann sum (point evaluations)
approximates the integral (averages).

Without continuity, this bridge breaks. The simple-function approach replaces `f` by
`f_n = Σ a_i·1_{A_i}`, giving:

```
∫∫ f_n(x)·conj(f_n(y))·K(x,y) dμ dμ = Σ_{i,j} a_i·conj(a_j)·∫_{A_i×A_j} K d(μ⊗μ)
```

This is a quadratic form in the **averaged** matrix `M_{ij} = ∫_{A_i×A_j} K d(μ⊗μ)`,
NOT in the point-evaluation matrix `K(x_i, x_j)`. The pointwise PD condition
(`Σ c_i·conj(c_j)·K(x_i,x_j) ≥ 0` for all finite point sets) controls point
evaluations, not averages. Without continuity, `K(x_i, x_j)` tells you nothing about
`∫_{A_i×A_j} K`. So the simple-function quadratic form is not directly non-negative
from pointwise PD, and MCT/DCT cannot be applied to pass to the limit.

**The fundamental obstacle:** pointwise PD is a condition on **discrete measures**
(`Σ c_i δ_{x_i}`), while the integral is a quadratic form for **absolutely
continuous measures** (`f·dμ`). On a non-atomic measure space, discrete measures
and a.c. measures live in different worlds — delta functions are not in `L²(μ)`, so
the pointwise PD condition gives no direct information about the `L²` quadratic form.
Continuity is the bridge that connects them (by making point values approximate
averages); without it, the simple-function route is blocked.

### Why the generalization IS true (different proof)

**Generalized statement.** Let `(X, μ)` be a finite measure space, `K : X → X → ℂ`
pointwise PD (every finite submatrix PSD) with `K ∈ L²(μ⊗μ)` and `x ↦ K(x,x)`
μ-measurable, and `f ∈ L²(μ)`. Then `∫∫ f(x)·conj(f(y))·K(x,y) dμ dμ ≥ 0`.

**Proof sketch (truncation + Moore–Aronszajn + Bochner integral).**

1. **Truncate.** For `M > 0`, define `X_M = {x : K(x,x) ≤ M}` (measurable by
   hypothesis) and `K_M(x,y) = K(x,y)·1_{X_M}(x)·1_{X_M}(y)`. Then:
   - `K_M` is PD: for any finite set `S` and coefficients `c`,
     `Σ c_i·conj(c_j)·K_M(x_i,x_j) = Σ c'_i·conj(c'_j)·K(x_i,x_j) ≥ 0` where
     `c'_i = c_i·1_{X_M}(x_i)` (PD holds for any coefficients, including `c'`).
   - `K_M(x,x) ≤ M`, so `K_M(x,x) ∈ L^∞(μ) ⊂ L¹(μ)` (since `μ` is finite).

2. **Bounded-diagonal case (Moore–Aronszajn).** By the Moore–Aronszajn theorem,
   `K_M(x,y) = ⟨φ_M(x), φ_M(y)⟩_H` for some Hilbert space `H` and feature map
   `φ_M : X → H` with `‖φ_M(x)‖² = K_M(x,x) ≤ M`. Since `f ∈ L²(μ) ⊂ L¹(μ)`
   (finite measure), the Bochner integral `F_M = ∫ φ_M(x)·f(x) dμ(x) ∈ H` exists:
   `∫ |f(x)|·‖φ_M(x)‖ dμ ≤ √M·‖f‖_{L¹} < ∞`. Then:
   ```
   ∫∫ K_M(x,y)·f(x)·conj(f(y)) dμ dμ
     = ∫∫ ⟨φ_M(x), φ_M(y)⟩·f(x)·conj(f(y)) dμ dμ
     = ⟨∫ φ_M·f dμ, ∫ φ_M·f dμ⟩_H    (inner product of Bochner integrals)
     = ‖F_M‖²_H ≥ 0.
   ```
   The interchange `∫∫ ⟨u(x),v(y)⟩ a(x) b(y) = ⟨∫ a·u, ∫ b·v⟩` is justified by
   Fubini + sesquilinearity of the inner product (Bochner integrability established
   above).

3. **Pass to the limit.** `K_M → K` in `L²(μ⊗μ)` as `M → ∞`:
   - `K - K_M = K·(1 - 1_{X_M×X_M})`, supported on `(X∖X_M)×X ∪ X_M×(X∖X_M)`.
   - `X∖X_M = {x : K(x,x) > M} ↓ ∅` as `M → ∞` (since `K(x,x) < ∞` pointwise).
   - By dominated convergence (dominating function `|K|² ∈ L¹(μ⊗μ)`),
     `‖K - K_M‖_{L²} → 0`.
   - By Cauchy–Schwarz on `L²(μ⊗μ)`:
     `|∫∫ (K-K_M)·f·conj(f)| ≤ ‖K-K_M‖_{L²}·‖f⊗conj(f)‖_{L²} = ‖K-K_M‖_{L²}·‖f‖²_{L²} → 0`.
   - So `∫∫ K·f·conj(f) = lim_M ∫∫ K_M·f·conj(f) ≥ 0`. ∎

### Why the compact/continuous hypotheses are load-bearing for the CURRENT proof

The current Riemann-sum proof uses compactness and continuity in three essential
places, none of which can be dropped while keeping the same proof structure:

1. **`finite_cover_balls_of_compact`** (compactness of `X`): produces a finite
   partition of `X` into small balls, giving a finite Riemann sum. Without
   compactness, `X` may not admit a finite cover by small balls.

2. **`CompactSpace.uniformContinuous_of_continuous`** (compactness + continuity of
   `F = f·conj(f)·K`): gives uniform continuity, so `F` varies by at most `ε` on each
   ball. This is the error bound `‖I - S‖ ≤ ε` that makes the Riemann sum approximate
   the integral. Without continuity, `F` can be arbitrarily wild, and the Riemann sum
   (point evaluations) need not approximate the integral (averages).

3. **Boundedness of `F`** (compactness of the range, from continuity + compactness):
   gives integrability of `F` via `Integrable.of_bound`. Without compactness,
   continuity alone doesn't give boundedness.

These are load-bearing for the **proof technique** (Riemann sums), not for the
**result**. The generalized proof above uses a completely different technique
(truncation + feature map) that needs none of these.

### Lean proof difficulty assessment

**Mathlib infrastructure available:**
- `RKHS.OfKernel` + `kernel_ofKernel` in
  `Mathlib.Analysis.InnerProductSpace.Reproducing` — this IS the Moore–Aronszajn
  theorem (constructs an RKHS from a PSD matrix, shows the kernel equals the
  original matrix). Authored by Hampus Nyberg & Yaël Dillies (2026).
- `integral_inner` in `Mathlib.MeasureTheory.Function.L2Space` —
  `∫ ⟨c, f x⟩ dμ = ⟨c, ∫ f dμ⟩` (pulls inner product out of integral).
- `integral_integral_swap` in `Mathlib.MeasureTheory.Integral.Prod` — Fubini for
  Bochner integrals.
- Standard dominated convergence / `L²` convergence machinery.

**Estimated difficulty: moderate, comparable to the current proof (~150–200 lines).**
The main work:
- Type plumbing: converting `PositiveDefiniteKernel K` (scalar `X → X → ℂ`) to
  `Matrix.PosSemidef` on `Matrix X X (ℂ →L[ℂ] ℂ)` for `RKHS.OfKernel`.
- Proving the Bochner integral identity
  `∫∫ ⟨φ(x),φ(y)⟩ f(x) conj(f(y)) = ‖∫ φ·f dμ‖²` — should follow from
  `integral_inner` + Fubini, but needs careful setup of the vector-valued integral.
- The truncation `K_M` and `L²` convergence — straightforward (dominated
  convergence).

**Not harder than the current proof — just different.** The current proof is
analysis (Riemann sums, uniform continuity, compactness); the generalized proof is
functional analysis (RKHS, Bochner integrals, `L²` convergence). Neither is
conceptually deeper; the generalized proof trades compactness/continuity hypotheses
for a more abstract proof technique.

### Caveats and limitations

1. **Finite measure required.** The truncation argument needs `μ` finite (so
   `L^∞ ⊂ L¹` and `L² ⊂ L¹`). For an infinite measure, `K_M(x,x) ≤ M` does not
   imply `K_M(x,x) ∈ L¹(μ)`, and `f ∈ L²` does not imply `f ∈ L¹`. The
   generalization to σ-finite or infinite measures would need additional work
   (e.g., restricting to `f ∈ L¹ ∩ L²` and `K` bounded, or using a different
   truncation).

2. **Measurability of the diagonal.** The truncation `X_M = {x : K(x,x) ≤ M}`
   requires `x ↦ K(x,x)` to be μ-measurable. This holds automatically when `X` is a
   Borel space and `K` is Borel-measurable (the diagonal map is Borel), but may fail
   for an arbitrary measure space. This is a mild additional hypothesis.

3. **`K ∈ L²(μ⊗μ)`, not merely `L¹`.** The convergence argument uses Cauchy–Schwarz
   on `L²(μ⊗μ)`, requiring `K ∈ L²`. For `K ∈ L¹(μ⊗μ)` only (not `L²`), the
   integral `∫∫ f·conj(f)·K` may not exist for `f ∈ L²` (the product
   `f⊗conj(f)·K` may not be `L¹`), and a different approach would be needed.

4. **The `IsProbabilityMeasure → IsFiniteMeasure` generalization** (item 1 in the
   earlier list) is subsumed by this analysis — the generalized proof works for any
   finite measure, not just probability measures. The `μ.real univ = 1` in the
   current proof becomes `μ.real univ < ∞` (the Riemann-sum error bound becomes
   `ε·μ.real univ` instead of `ε·1`), but the generalized proof sidesteps this
   entirely.

5. **The `PseudoMetricSpace → UniformSpace` generalization** (item 2) is also
   subsumed — the generalized proof uses no topology on `X` at all (no metric, no
   uniform structure). The only structure needed is the measure space and the
   measurability of the diagonal.

### Recommendation

The generalization is mathematically sound and feasible in Lean using Mathlib's
existing `RKHS.OfKernel` and Bochner integral infrastructure. It should be pursued
as a follow-up to the current submission, NOT as a modification of the current
proof. The current proof (Riemann sums) is more elementary and self-contained; the
generalized proof (RKHS + Bochner) is more abstract but yields a strictly stronger
result with fewer hypotheses. Both are worth having: the current proof for
accessibility, the generalized proof for generality.

---

## 8. General L² integral-operator positivity — VERIFIED (2026-08-12)

**Status:** Packaged. `mathlib_candidates/PositiveDefiniteKernelGeneral.lean` +
§1c of `MATHLIB_SUBMISSION.md`.
**VERIFIED** — compiles with `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (NO `sorryAx`). Ready to package.

**Statement.** `PositiveDefiniteKernel.integralOperator_nonneg_general`:
For a finite measure space `(X, μ)`, a pointwise PD kernel `K` with bounded
diagonal (`∃ M, 0 ≤ M ∧ ∀ x, K(x,x) ≤ M`), a strongly measurable feature map
`φ : X → H` (the Moore–Aronszajn RKHS feature map), and `f ∈ L²(μ)`:
`∫∫ f(x) · conj(f(y)) · K(x,y) dμ dμ ≥ 0`.

This is the **bounded-diagonal** special case of the general result analyzed in
§above (the full `K ∈ L²(μ⊗μ)` version would add a truncation + dominated-
convergence limit; the bounded-diagonal case is the core RKHS/Bochner argument
and is what is currently formalized).

**Why possibly-novel.** Same novelty as §1 (the continuous/measure-theoretic
integral-operator positivity from a pointwise PD kernel), but with **no topology
on `X`, no continuity of `K` or `f`, and no compactness** — only the measure
structure, pointwise PD, and a bounded-diagonal hypothesis. Mathlib's
`RKHS.OfKernel` (Reproducing.lean) constructs the RKHS from a *finite-matrix* PSD
kernel; this file does the scalar `X → X → ℂ` case and proves the integral-
operator positivity. The combination (RKHS feature map + Bochner integral +
`‖F‖² ≥ 0`) is not present in Mathlib.

**Proof technique.** Moore–Aronszajn feature map `φ : X → H` into the RKHS `H`
(completion of the finitely-supported pre-Hilbert space `H₀ K` with inner product
`⟨f,g⟩ = Σ_{x,y} conj(f x) · g y · K(x,y)`). Define `F = ∫ conj(f) • φ dμ`
(Bochner integral in `H`, integrable by `‖conj(f)•φ(x)‖ ≤ √M·‖f(x)‖` and
`f ∈ L² ⊂ L¹`). Then:
- `inner ℂ (φ x) F = ∫ y, conj(f y) · K(x,y) dμ` (via `integral_inner` +
  `inner_smul_right` + `inner_featureMap`).
- `inner ℂ F F = conj(∫∫ f(x)·conj(f(y))·K(x,y) dμ dμ)` (via `integral_inner` +
  `inner_conj_symm` + `integral_conj` + the Hermitian symmetry `K(x,y)=conj(K(y,x))`).
- `inner ℂ F F` is self-conjugate (`inner_conj_symm`), so the goal equals
  `inner ℂ F F = ‖F‖² ≥ 0` (via `inner_self_eq_norm_sq_to_K`).

**Key formalization hurdles overcome (this session):**
1. **`smul_left` of `PreInnerProductSpace.Core`** — the recurring `conj` vs `star`
   defeq issue. Fix: match the `Reproducing.lean` pattern *exactly* —
   `rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]` with NO
   intervening `show` (the `show` with explicit `conj z * w * K x y` caused the
   `•` instance to elaborate differently and break `sum_smul_index` matching).
2. **`InnerProductSpace ℂ (H K)` stuck** — `H K = UniformSpace.Completion (H₀ K)`
   needed an explicit instance declaration
   `instance : InnerProductSpace ℂ (H K) := UniformSpace.Completion.innerProductSpace`
   to resolve (the anonymous completion instance wasn't firing through the `abbrev`).
3. **`conj`/`star` defeq in `rw`/`simp`** — `simp only [star_mul', Complex.conj_conj]`
   "made no progress" because `conj = starRingEnd ℂ` is not syntactically `star`.
   Fix: bridge with `show star (...) = ...` then `rw [star_mul', star_star, hK]`
   where `hK : star (K x y) = K y x` is proved from `conj_symm`.

**Axioms.** `propext, Classical.choice, Quot.sound` only — **no `sorryAx`**.

**Submittability.** Strong candidate — strictly stronger than §1 (drops
compactness, continuity of `K`/`f`, and the metric on `X`), clean statement,
pure measure theory + RKHS. The bounded-diagonal hypothesis is the natural
"first" version; the full `K ∈ L²` version (with truncation) is a follow-up.

**Comparison with in-progress Mathlib PR #42003 (TJHeeringa, `mercersTheorem`
branch, `Mathlib/Analysis/InnerProductSpace/Reproducing.lean`, draft/unmerged
2026-08-12) — informs future API alignment, not a code dependency.**
- `mercerForm` is a *single* integral over `μ.prod μ` with the one hypothesis
  `MemLp (fun p : X×X => K p.1 p.2) 2 (μ.prod μ)` (K itself L² on the product
  space). Integrand measurability is product-space `AEStronglyMeasurable`,
  assembled from `hK.aestronglyMeasurable` + `Lp.aestronglyMeasurable` pulled
  back via `comp_fst`/`comp_snd`; integrability is a clean Hölder (2,2) bound
  (`lintegral_norm_inner_le`), no dominated-construction needed.
- It **sidesteps the feature map entirely** in the Mercer section: no `φ : X → H`,
  no `StronglyMeasurable (featureMap K)` hypothesis, no H-valued Bochner integral
  of `conj(f) • φ`. `integralOperator` is built from `mercerForm` via the Riesz
  representer (`InnerProductSpace.toDual`); `isSelfAdjoint_integralOperator`
  follows from `mercerForm_conj_symm`.
- It does **not** prove `0 ≤ mercerForm f f` (positivity of the form) — it stops at
  the bilinear/self-adjoint scaffolding. Our `integralOperator_nonneg_general`
  supplies exactly that missing positivity (`⟨F,F⟩ = ‖F‖² ≥ 0`); the two are
  complementary, not redundant.
**Takeaway.** Our proof is complete and verified (0 sorries, 3 axioms) — no
refactor is needed to unstick anything. For an eventual Mathlib submission, the
PR's `MemLp K 2 (μ.prod μ)` convention is more standard than our
`StronglyMeasurable (featureMap K)` (the latter is non-standard API: strong
measurability into a user-defined completion is hard for a caller to verify).
Our bounded diagonal `∃ M, K(x,x) ≤ M` plus the kernel Cauchy–Schwarz bound
`|K(x,y)|² ≤ K(x,x)·K(y,y) ≤ M²` would *imply* `K ∈ L²(μ⊗μ)` for a finite measure
(via a kernel-CS lemma we do not currently prove). Recommendation: keep the
verified proof as-is; revisit restating in the product-measure/Lp convention
only after PR #42003 merges and stabilizes.

---

## 9. `repCharacter_cyclic2`: 2-factor cyclic invariance of characters (standard-but-unformalized)

**Status:** Embedded in `src/lean/YangMills/Proofs/PositiveDefinite.lean:795`.

**Statement.** For a group representation `ρ : G →* Matrix (Fin n) (Fin n) ℂ` and
group elements `g h : G`, the character `χ(g · h) = χ(h · g)`.

**Proof.** `χ(g · h) = Tr(ρ(g) · ρ(h)) = Tr(ρ(h) · ρ(g)) = χ(h · g)` by
`Matrix.trace_mul_comm`. No unitary or irreducibility hypothesis needed — pure
trace algebra. Depends only on `[propext, Classical.choice, Quot.sound]`.

**Why standard-but-unformalized.** This is the 2-factor special case of the
well-known cyclic invariance of the trace. Mathlib has `Matrix.trace_mul_comm`
(`Tr(A·B) = Tr(B·A)`) and the 3-factor character version
`repCharacter_cyclic` (`χ(g·h·k) = χ(h·k·g)`, proved in this project from
`trace_mul_comm`), but a direct 2-factor `χ(g·h) = χ(h·g)` lemma for group
characters does not appear to be in Mathlib. An absence check (grep for
`repCharacter_cyclic2` / `character.*cyclic.*2` / `trace_mul_comm.*character`
in Mathlib) found no match. The 3-factor version can derive it (set `k = 1`),
but the direct 2-factor form is cleaner for the bipartite cascade application.

**Use in this project.** Key lemma for rearranging character arguments in the
bipartite Lüscher cascade (`bipartiteChainIntegral_eq`): cyclically rotating
`χ((V-prod · b⁻¹ · W-prod⁻¹) · (W₀⁻¹ · a · V₀))` to
`χ(a · V₀ · V-prod · b⁻¹ · W-prod⁻¹ · W₀⁻¹)` via two applications.

---

## 10. `cgME_isometry_normSq`: Parseval identity for unitary change-of-basis matrices (standard-but-unformalized)

**Status:** Embedded in `src/lean/YangMills/Proofs/PeterWeyl/CGUnitarity.lean:37`.
Ready to package (general, no Yang-Mills-specific content).

**Statement.** Let `ι` be a finite type, `dims : ι → ℕ`, and
`cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ` a family of
"change-of-basis matrices" satisfying the **unitarity (completeness) relation**:
```
∀ (s t : ι) (a b : Fin (dims s)) (i j : Fin (dims t)),
  ∑ ν : ι, ∑ p : Fin (dims ν),
    conj (cgME s t ν a i p) * cgME s t ν b j p =
    if a = b ∧ i = j then (1 : ℂ) else 0
```
Then for any `v : Fin (dims s) → Fin (dims t) → ℂ`:
```
∑ (ν : ι), ∑ (p : Fin (dims ν)),
  Complex.normSq (∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
    cgME s t ν a i p * v a i) =
∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
  Complex.normSq (v a i)
```
This is the **Parseval identity** (ℓ²-norm preservation) for a unitary change-of-basis
matrix. The matrix `cgME s t ν` maps `Fin(dims s) × Fin(dims t)` to `⊕_ν Fin(dims ν)`,
and the unitarity relation says the "rows" are orthonormal. The identity says the map
`v ↦ (ν, p ↦ ∑_{a,i} cgME_{a,i,p} · v_{a,i})` is an ℓ²-isometry.

**Why standard-but-unformalized.** This is the finite-dimensional Parseval identity — a
direct consequence of a unitary matrix preserving the ℓ² norm. It is standard linear
algebra (equivalent to `‖Uv‖ = ‖v‖` for a unitary `U`). Mathlib has
`Matrix.PosSemidef`, `Matrix.IsUnitary`, and inner-product-space isometry machinery, but
the specific packaging — a 3-index "matrix" `cgME s t ν a i p` (not a standard
`Matrix (Fin m) (Fin n) ℂ`), with the unitarity relation stated as a sum-of-products
identity (not `U* U = I`), and the conclusion as a `normSq`-sum identity (not
`‖Uv‖ = ‖v‖` in an inner product space) — does not appear to be in Mathlib in this form.
An absence check (grep for `normSq.*sum.*isometry` / `Parseval` / `unitary.*normSq` in
Mathlib) found no direct match. The standard `InnerProductSpace` isometry API uses
`‖f x‖ = ‖x‖` for a continuous linear map `f`; this lemma is the explicit finite-sum
version for a "matrix" given by a sum-of-products unitarity relation, which is the natural
form for representation-theoretic CG coefficients.

**Substance.** The proof is a direct algebraic calculation: expand `|w|² = conj(w)·w`,
distribute the product of sums, exchange the `(ν,p)` sum with the `(a,i,b,j)` sums, apply
the unitarity relation to collapse `∑_{ν,p} conj(cgME_{a,i})·cgME_{b,j}` to `δ_{a,b}·δ_{i,j}`,
then collapse the delta. The formalization challenge is the sum reordering (8
`Finset.sum_comm` swaps with dependent types) and the `ℝ→ℂ` coercion bridge. Not deep,
but nontrivial to formalize cleanly.

**Axioms.** `propext, Classical.choice, Quot.sound` only — **no `sorryAx`**, no
Yang-Mills-specific axioms. The unitarity relation is a hypothesis, not an axiom.

**Submittability.** Good candidate — clean statement, pure algebra (finite sums over
`Fin`-indexed types, `Complex.normSq`), no analysis or measure theory. The 3-index
"matrix" form is the natural one for CG coefficients and other representation-theoretic
change-of-basis matrices. Would need extraction from the Yang-Mills namespace and
generalization (the `cgME` name is Yang-Mills-specific; the lemma itself is not).

**Use in this project.** The key building block for Step B.2 of the transfer matrix
positivity proof: the 3D Lüscher cascade defines a Fourier coefficient extraction
operator B, and `cgME_isometry_normSq` gives `‖Bg‖² = ‖g‖²` (Parseval), which is the
mechanism that makes the transfer matrix kernel `T = B*B` positive semidefinite. This is
the first-ever application of `hcgME_unitary` (the CG unitarity relation from the
Peter-Weyl axiom), which had been available but never applied.

---

## Tensor product isometry (B isometry ⟹ B ⊗ conj(B) isometry)

**Status:** Possibly-novel formulation. **Verified numerically** (8 random trials, all PASS)
but NOT yet formalized in Lean.

**Statement.** If B is an m×n isometry (B* B = I_n), then B ⊗ conj(B) (Kronecker product
with elementwise conjugate, NOT adjoint) is an isometry: (B ⊗ conj(B))* (B ⊗ conj(B)) =
I_{n²}.

**Proof sketch.** (B ⊗ conj(B))* (B ⊗ conj(B)) = (B* B) ⊗ (conj(B)* conj(B)) = I_n ⊗ I_n =
I_{n²}. The key identity: conj(B)* = conj(B*), and conj(B)* conj(B) = conj(B* B) = conj(I) =
I (since B* B = I and conj is a *-antiautomorphism).

**Why it might be novel / absent from Mathlib.** The Kronecker product of matrices with
elementwise conjugate (not adjoint) is a less common construction. Mathlib has
`Matrix.kroneckerMap` but the specific isometry property for B ⊗ conj(B) (with conj, not
adjoint) may not be formalized. An absence check (grep/Loogle for "kronecker" + "isometry"
+ "conj") should be done before claiming novelty.

**Use in this project.** Identified in session 130 (§8.11.94) as a potential ingredient for
the 6-fold isometry. The 6-fold isometry (shared α) turned out to be FALSE — it is the
DIAGONAL restriction of the tensor product isometry, which is NOT an isometry. The tensor
product isometry itself IS true but has a different structure (independent α₁, α₂) that
does not match the single-site integral structure. It remains a potentially useful general
result even though it does not directly apply to the current proof path.

**Submittability.** Good candidate IF formalized — clean linear algebra, no analysis. Would
need a proper Lean formalization and absence check before submission.


---

## Integrated kernel is PSD (kernel of positive type) - session 132

**Statement.** For any phi : X -> T -> C and measure mu on T, the integrated kernel
K(x, y) = integral of phi(x, t)*conj(phi(y, t)) dmu(t) is positive-semidefinite:
sum_{x in s} sum_{y in s} c x * conj(c y) * K x y >= 0 for finite s and c : X -> C.

**Proof.** Gram / sum-of-squares: sum c conj(c) K = integral of |sum_x c_x phi(x,t)|^2 dmu >= 0.
Formalized as integrated_kernel_psd in Proofs/PositiveDefinite/IntegratedKernel.lean. Depends
ONLY on [propext, Classical.choice, Quot.sound] - no custom axioms, no character theory.

**Why novel / absent from Mathlib.** General "kernel of positive type from a feature map into
L2" fact. Mathlib has Matrix.PosSemidef and inner-product machinery, but a packaged
"integrated/Gram kernel is PSD" lemma for Bochner integrals may be absent. Absence check
(grep/Loogle) needed before claiming novelty. Status: embedded (proven, in-project).

**Use in this project.** Provable core of Step B.2e.2 (design doc 8.11.96). NOTE: NOT sufficient
by itself to close transferMatrixPositivity_axiom - the kernel here is the double integral
integral phi(x,t) conj(phi(y,t)), while reflection positivity needs the single integral with the
geometric reflection theta (the c' != conj(c) obstacle). See design doc 8.11.96 Findings 2-3.

Also formalized this session: integral_prod_repCharacter_conj (paired character orthogonality
for product measures), the paired analogue of integral_prod_repCharacter_trivial. Depends on
characterOrthogonality (existing axiom).
