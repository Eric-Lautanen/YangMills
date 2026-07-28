# Mathlib Candidate: Positive-Definite Kernels and Integral Operators

This document packages three independently-verified, general-purpose results
for review by Mathlib maintainers. It is a pointer and a verification
checklist, not an essay. The results are pure group / measure / kernel theory
and are unrelated to the Yang-Mills problem that motivated their
formalization (see "Provenance" below).

Two standalone, Yang-Mills-free files are provided so each result group can
be evaluated independently:

- `PositiveDefiniteKernelMathlibCandidate.lean` — **priority candidate** —
  Mercer-type positive-definite kernels (no group structure required).
- `PositiveDefiniteMathlibCandidate.lean` — group-theoretic positive-definite
  functions on a group.

---

## 1. Lemma statements

### 1a. Mercer-type positive-definite kernels (priority)

**Plain language.** A kernel `K : X → X → ℂ` is *positive-definite in the
Mercer sense* if for every finite set `{x_i}` and coefficients `{c_i}`,
`Σ_{i,j} c_i · conj(c_j) · K(x_i, x_j) ≥ 0`. This generalizes the
group-theoretic notion of positive-definiteness (where `K(x, y) = φ(x⁻¹·y)`
for a PD function `φ` on a group) to arbitrary spaces: the reduction
group-PD ⟹ Mercer-PD is proved as `PositiveDefinite.toPositiveDefiniteKernel`.
(Only this one direction is proved; no claim of proper containment is made.)

**Main theorem.** If `X` is a compact (pseudo)metric space with a probability
measure `μ`, `K` is a continuous Mercer-PD kernel, and `f` is continuous,
then `∫∫ f(x) · conj(f(y)) · K(x, y) dμ dμ ≥ 0`. The proof approximates the
integral by Riemann sums (each non-negative by
`PositiveDefiniteKernel.sum_nonneg_of_map`) and controls the error via
uniform continuity on `X × X` (Heine–Cantor). No group structure is needed.

**Lean signatures.**

```lean
def PositiveDefiniteKernel {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (s : Finset X) (c : X → ℂ),
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j

lemma PositiveDefiniteKernel.integralOperator_nonneg
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    (hK_cont : Continuous (Function.uncurry K))
    {f : X → ℂ} (hf_cont : Continuous f) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ
```

**Supporting lemma suite** (all in `PositiveDefiniteKernelMathlibCandidate.lean`):

- `PositiveDefiniteKernel.sum_nonneg_of_map` — the quadratic form with a
  mapped (possibly non-injective) index set is non-negative (key grouping
  argument; uses the `private` helper `sum_fiber_kernel`).
- `PositiveDefiniteKernel.conj_symm` — Hermitian symmetry
  `K(x, y) = conj(K(y, x))`, via the 2-point quadratic-form trick.
- `PositiveDefiniteKernel.one` — the constant-one kernel is PD.
- `PositiveDefiniteKernel.matrix_posSemidef` (`private`) — a Mercer-PD kernel
  gives a PSD matrix on any finite subset (used by `.mul`).
- `PositiveDefiniteKernel.mul` — Schur / Hadamard product theorem.
- `PositiveDefiniteKernel.smul_nonneg` — non-negative scaling.
- `PositiveDefiniteKernel.finprod` — n-ary Schur product.
- `PositiveDefiniteKernel.comp` — PD preserved by composition with `f : X → Y`.
- `PositiveDefiniteKernel.continuous_comp` — continuity preserved by composition.
- `PositiveDefinite.toPositiveDefiniteKernel` — group-PD ⟹ Mercer-PD.

### 1b. Group-theoretic positive-definite functions

**Plain language.** A function `φ : G → ℂ` on a group `G` is
*positive-definite* if `Σ_{i,j} c_i · conj(c_j) · φ(g_i⁻¹·g_j) ≥ 0` for every
finite set and coefficients.

**Theorem 1.** An integral average of PD functions is PD (the continuous
analogue of the finite-sum fact): if `Φ t` is PD for `ν`-a.e. `t` and each
`t ↦ Φ t g` is `ν`-integrable, then `g ↦ ∫ t, Φ t g ∂ν` is PD.

**Theorem 2.** If `G` is a compact (pseudo)metric topological group with
probability measure `μ`, `φ` is continuous PD, and `f` is continuous, then
`∫∫ f(x) · conj(f(y)) · φ(x⁻¹·y) dμ dμ ≥ 0`. Same Riemann-sum argument as
above, using `PositiveDefinite.sum_nonneg_of_map`.

**Lean signatures.**

```lean
def PositiveDefinite {G : Type*} [Group G] (φ : G → ℂ) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ),
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)

lemma PositiveDefinite.integral {T : Type*} [MeasurableSpace T] (ν : Measure T)
    (Φ : T → G → ℂ) (hPD : ∀ᵐ t ∂ν, PositiveDefinite (Φ t))
    (hint : ∀ g : G, Integrable (fun t => Φ t g) ν) :
    PositiveDefinite (fun g => ∫ t, Φ t g ∂ν)

lemma PositiveDefinite.integralOperator_nonneg
    {G : Type*} [Group G] [PseudoMetricSpace G] [CompactSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {φ : G → ℂ} (hφ : PositiveDefinite φ) (hφ_cont : Continuous φ)
    {f : G → ℂ} (hf_cont : Continuous f) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * φ (x⁻¹ * y) ∂μ ∂μ
```

Supporting lemma: `PositiveDefinite.sum_nonneg_of_map` (and the `private`
helper `sum_fiber`).

---

## 2. Provenance

These results came out of an AI-agent-assisted formalization side-project
working toward the Yang-Mills mass gap problem. They are general-purpose
group/measure/kernel theory and are unrelated to that problem's actual
(unsolved) difficulty, which concerns a *single* reflection integral
`∫ f(U)·f(θU)·exp(-β S_W) dμ` that is not of the standard PD quadratic form
addressed here. These lemmas are offered as standalone infrastructure.

---

## 3. Absence-verification summary

Checked against the Mathlib version pinned in `lake-manifest.json`
(commit `3bc2a1801c2416549ba5ba0b3f5728a28b87e7d9`, Lean `v4.33.0-rc1`).

- `grep` for `PositiveDefiniteKernel` across the entire Mathlib source tree:
  **0 matches**. The identifier does not exist.
- `grep` for `def PositiveDefinite` (group-theoretic, as a bare `def`):
  **0 matches**. Mathlib's existing PD machinery is matrix/quadratic-form
  based (`Matrix.PosDef`, `Matrix.PosSemidef`, `PosSemidef`) and never
  touches Haar measure or the group-PD-function notion defined here.
- `grep` for `integralOperator_nonneg`: **0 matches**.
- Loogle subexpression search `0 ≤ ∫ x, ∫ y, _ * _ * _ ∂_ ∂_` over all 56
  declarations mentioning `HMul.hMul`, `LE.le`, `MeasureTheory.integral`,
  and `OfNat.ofNat`: **0 matches** for the double-integral pattern. The
  related search `0 ≤ ∫ _, _ ∂_` returns only generic pointwise-nonnegative
  integrand lemmas (`integral_nonneg`, `setIntegral_nonneg`), nothing
  kernel- or group-theoretic.
- Loogle identifier search for `PositiveDefiniteKernel` and `PositiveDefinite`:
  **0 matches** (neither name exists in Mathlib).
- `grep` for `Mercer`, `Godement`, `Bochner.*positive` across Mathlib:
  no relevant matches (the single `Mercer` hit is in `docs/1000.yaml`, a
  bibliography file, not a theorem).

**Comparison with `Mathlib/Analysis/InnerProductSpace/Reproducing.lean`.**
That file defines `RKHS` (reproducing kernel Hilbert spaces) and proves
`RKHS.posSemidef_kernel` — the kernel of an RKHS is a positive-semidefinite
*matrix* (`Matrix.PosSemidef`), and `RKHS.OfKernel` constructs an RKHS from a
finite-matrix PSD kernel. The Mercer-PD notion here
(`PositiveDefiniteKernel`) is the *continuous / measure-theoretic*
generalization: the kernel is a function `X → X → ℂ` on an arbitrary
(possibly continuous) space, and the positivity is the integral-operator
inequality `∫∫ f(x)·conj(f(y))·K(x,y) dμ dμ ≥ 0`, not a finite-matrix
condition. A search for any Mathlib file generalizing `Reproducing.lean`'s
finite-matrix PD kernel to the continuous/measure-theoretic setting found
nothing. The two notions are related but distinct; the candidate here is
closer in spirit to the continuous side that Mathlib does not yet have.

**Limits of this search.** This is not an exhaustive proof of absence. It
covers: full-text `grep` of the pinned Mathlib tree for the relevant
identifiers and concept names, and Loogle type-signature / subexpression
searches. It does not cover every possible reformulation or naming
convention a future Mathlib contribution might use.

---

## 4. Exact reproduction steps

A fresh clean `lake build` succeeds (verified manually before the packaging
session; not re-run during packaging to avoid the slow rebuild). The two
standalone files compile standalone, reusing the already-built `.lake`
cache, via:

```
lake env lean PositiveDefiniteKernelMathlibCandidate.lean
lake env lean PositiveDefiniteMathlibCandidate.lean
```

(Both exit 0 with no errors. Run from the repo root so the `.lake` cache is
found.)

**`#print axioms` output** (identical from the original
`src/lean/YangMills/Proofs/PositiveDefiniteIntegral.lean` location and from
both standalone files):

```
'PositiveDefinite.integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefinite.integralOperator_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.integralOperator_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.sum_nonneg_of_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.conj_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefinite.toPositiveDefiniteKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.finprod' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.continuous_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveDefiniteKernel.smul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`); no custom axiom, no `sorry`. To reproduce, add the
`#print axioms` lines to the bottom of the relevant file (or a scratch file
importing it) and run `lake env lean <file>.lean`.

**File paths:**

- `PositiveDefiniteKernelMathlibCandidate.lean` (repo root) — Mercer kernel.
- `PositiveDefiniteMathlibCandidate.lean` (repo root) — group-theoretic PD.
- Original source: `src/lean/YangMills/Proofs/PositiveDefiniteIntegral.lean`
  (and `src/lean/YangMills/Proofs/PositiveDefinite.lean` for the group-PD
  definition and `sum_nonneg_of_map`).

---

## 5. What is explicitly NOT being claimed

- **No claim about the Yang-Mills problem.** The mass-gap conjecture is
  unsolved; the top-level theorem in this repo rests on `mass_gap_axiom`,
  which is the conjecture itself. The results packaged here are independent
  of that axiom and of any gauge-theoretic content.
- **No claim of exhaustive Mathlib search.** The absence check covers
  full-text `grep` of the pinned Mathlib tree plus Loogle searches; it is
  not a proof that no equivalent result exists under some other name or
  formulation. A reviewer may find a reformulation this search missed.
- **No claim that these results are difficult or deep.** They are
  standard analysis (Riemann-sum approximation + uniform continuity). The
  claim is only that they appear correct, non-vacuous, and currently absent
  from Mathlib, and that they may be useful infrastructure.
- **No claim of "strictly more general."** Only the one-directional
  reduction group-PD ⟹ Mercer-PD is proved
  (`PositiveDefinite.toPositiveDefiniteKernel`); the Mercer notion is stated
  to *generalize* the group notion, not to *strictly* contain it.
