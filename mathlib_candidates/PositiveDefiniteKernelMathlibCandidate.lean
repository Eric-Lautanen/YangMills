/-
# Mercer-type positive-definite kernels — Mathlib candidate

This is a standalone, self-contained file extracting the Mercer-type
positive-definite-kernel theory developed in the YangMills project
(`src/lean/YangMills/Proofs/PositiveDefiniteIntegral.lean`).  It is pure
group/measure/kernel theory: no gauge theory, no lattice, no Yang-Mills.

## Main result

`PositiveDefiniteKernel.integralOperator_nonneg`: a continuous Mercer-PD
kernel on a compact (pseudo)metric space with a probability measure defines
a positive integral operator:
`∫∫ f(x) * conj(f(y)) * K(x, y) dμ dμ ≥ 0`.

The proof approximates the integral by Riemann sums (each non-negative by
`PositiveDefiniteKernel.sum_nonneg_of_map`) and controls the error via
uniform continuity on the compact space `X × X` (Heine–Cantor).

## Supporting lemmas

* `PositiveDefiniteKernel.conj_symm` — Hermitian symmetry `K(x,y) = conj K(y,x)`.
* `PositiveDefiniteKernel.one` — the constant-one kernel is PD.
* `PositiveDefiniteKernel.mul` — Schur (Hadamard) product theorem.
* `PositiveDefiniteKernel.smul_nonneg` — non-negative scaling.
* `PositiveDefiniteKernel.finprod` — n-ary Schur product.
* `PositiveDefiniteKernel.comp` — PD preserved by composition with `f : X → Y`.
* `PositiveDefiniteKernel.continuous_comp` — continuity preserved by composition.
* `PositiveDefinite.toPositiveDefiniteKernel` — every group-PD function gives a
  Mercer-PD kernel `K(x,y) = φ(x⁻¹ * y)`, showing the Mercer notion
  generalizes the group-theoretic one.

## Verification

All lemmas depend only on `propext`, `Classical.choice`, `Quot.sound`
(verified by `#print axioms`), with 0 `sorry`s and 0 custom axioms.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Disjointed
import Mathlib.Topology.Constructions.SumProd

open Finset MeasureTheory Complex Metric Matrix

open scoped ComplexConjugate ComplexOrder Function

/-- A function `φ : G → ℂ` on a group `G` is *positive-definite* if for every
finite set `{g_i}` and coefficients `{c_i}`, the quadratic form
`∑ c_i * conj(c_j) * φ(g_i⁻¹ * g_j) ≥ 0`. -/
def PositiveDefinite {G : Type*} [Group G] (φ : G → ℂ) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ),
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)

/-- A kernel `K : X → X → ℂ` is positive-definite (Mercer sense): every finite
submatrix `(K x_i x_j)_{i,j ∈ s}` is positive-semidefinite in the sense of
`Matrix.PosSemidef`.  This is the direct `Matrix.PosSemidef` formulation
(suggested by Yaël Dillies): `PositiveDefiniteKernel K ↔
∀ s : Finset X, (Matrix.of (fun i j : ↥s => K i.val j.val)).PosSemidef`.
The equivalence with the quadratic-form formulation
`∀ s c, 0 ≤ Σ c_i * conj(c_j) * K(x_i, x_j)` is provided by
`PositiveDefiniteKernel.quadratic_form_nonneg` (forward) and
`PositiveDefiniteKernel.of_quadratic_form` (backward). -/
def PositiveDefiniteKernel {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (s : Finset X), Matrix.PosSemidef (Matrix.of fun (i j : ↥s) => K i.val j.val)

/-- The quadratic form `Σ c_i * conj(c_j) * K(x_i, x_j) ≥ 0` — derived from
`Matrix.PosSemidef.dotProduct_mulVec_nonneg` via the new definition.  This is
the "old definition" direction of the equivalence
`PositiveDefiniteKernel K ↔ ∀ s c, 0 ≤ Σ c_i * conj(c_j) * K(x_i, x_j)`. -/
lemma PositiveDefiniteKernel.quadratic_form_nonneg
    {X : Type*} {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    (s : Finset X) (c : X → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j := by
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let M : Matrix ↥s ↥s ℂ := fun i j => K i.val j.val
  have hM : M.PosSemidef := hK s
  let x : ↥s → ℂ := fun i => conj (c i.val)
  have hquad : 0 ≤ star x ⬝ᵥ (M *ᵥ x) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hM x
  have hdot : star x ⬝ᵥ (M *ᵥ x) =
      ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j := by
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    simp only [M, x, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_coe_sort s
        (fun a => ∑ j : ↥s, c a * K a j.val * conj (c j.val))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_coe_sort s (fun b => c i * K i b * conj (c b))]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_right_comm _ _ _
  rw [← hdot]; exact hquad

/-- Hermitian symmetry `K(x,y) = conj(K(y,x))` derived from the quadratic form
(non-negativity for all finite sets and coefficients).  This is the key
ingredient for `of_quadratic_form` (quadratic form → `PosSemidef`). -/
private lemma quadratic_form_conj_symm
    {X : Type*} (K : X → X → ℂ)
    (h : ∀ (s : Finset X) (c : X → ℂ),
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j) :
    ∀ x y, K x y = conj (K y x) := by
  intro x y
  classical
  have h_diag : ∀ z, 0 ≤ K z z := fun z => by
    have h' := h (Finset.cons z ∅ (by simp)) (fun _ => 1)
    simp at h'; exact h'
  have h_diag_im : ∀ z, (K z z).im = 0 := fun z =>
    (Complex.nonneg_iff.mp (h_diag z)).2.symm
  by_cases hxy : x = y
  · subst hxy; exact (Complex.conj_eq_iff_im.mpr (h_diag_im x)).symm
  · have hne1' : (y : X) ∉ (∅ : Finset X) := by simp
    have hne2 : (x : X) ∉ Finset.cons y ∅ hne1' := by simp [hxy]
    have hS : ∀ t : ℂ,
        0 ≤ K x x + conj t * K x y + t * K y x + (t * conj t) * K y y := by
      intro t
      have h' := h (Finset.cons x (Finset.cons y ∅ hne1') hne2)
          (fun z => if z = x then 1 else t)
      have hsum : (∑ i ∈ Finset.cons x (Finset.cons y ∅ hne1') hne2,
          ∑ j ∈ Finset.cons x (Finset.cons y ∅ hne1') hne2,
          (if i = x then 1 else t) * conj (if j = x then 1 else t) * K i j) =
          K x x + conj t * K x y + t * K y x + (t * conj t) * K y y := by
        simp only [Finset.sum_cons, Finset.sum_empty,
          ite_true, if_neg (Ne.symm hxy), one_mul, mul_one, map_one]
        ring
      rw [hsum] at h'; exact h'
    have h_im_sum : (K x y).im + (K y x).im = 0 := by
      have key := (Complex.nonneg_iff.mp (hS 1)).2
      have hkey : K x x + conj 1 * K x y + 1 * K y x + (1 * conj 1) * K y y =
          K x x + K x y + K y x + K y y := by simp
      rw [hkey] at key
      have h2 : (K x x + K x y + K y x + K y y).im =
          (K x x).im + (K x y).im + (K y x).im + (K y y).im := by simp [Complex.add_im]
      rw [h2, h_diag_im x, h_diag_im y] at key; linarith
    have h_re_diff : (K y x).re - (K x y).re = 0 := by
      have key := (Complex.nonneg_iff.mp (hS Complex.I)).2
      have heq : K x x + conj Complex.I * K x y + Complex.I * K y x +
          (Complex.I * conj Complex.I) * K y y =
          K x x + K y y + Complex.I * (K y x - K x y) := by simp [Complex.conj_I]; ring
      rw [heq] at key
      have h2 : (K x x + K y y + Complex.I * (K y x - K x y)).im =
          (K x x).im + (K y y).im + ((K y x).re - (K x y).re) := by
        simp [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.I_re, Complex.I_im]
      rw [h2, h_diag_im x, h_diag_im y] at key; linarith
    apply Complex.ext
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_im]; linarith

/-- If the quadratic form is non-negative for every finite set and coefficients,
then `K` is a Mercer-PD kernel (the reverse direction of the equivalence). -/
lemma PositiveDefiniteKernel.of_quadratic_form
    {X : Type*} (K : X → X → ℂ)
    (h : ∀ (s : Finset X) (c : X → ℂ),
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j) :
    PositiveDefiniteKernel K := by
  intro s
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let M : Matrix ↥s ↥s ℂ := fun i j => K i.val j.val
  change Matrix.PosSemidef M
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ?_
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    -- `IsHermitian.ext` wants `star (M j i) = M i j`; `quadratic_form_conj_symm`
    -- gives `K i j = conj (K j i)`, so we take the symmetric form.
    exact (quadratic_form_conj_symm K h i.val j.val).symm
  · intro x
    let c : X → ℂ := fun g => if hg : g ∈ s then conj (x ⟨g, hg⟩) else 0
    have hc'val : ∀ i : ↥s, c i.val = conj (x i) := fun i => by
      simp only [c, dif_pos i.property]
    have hPD := h s c
    have hdot : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j) = star x ⬝ᵥ (M *ᵥ x) := by
      rw [Matrix.dot_mulVec_eq_sum_sum]
      conv_rhs => rw [Finset.sum_comm]
      simp only [M, Pi.star_apply, Complex.star_def]
      rw [← Finset.sum_coe_sort s
          (fun a => ∑ j ∈ s, c a * conj (c j) * K a j)]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_coe_sort s
          (fun b => c i.val * conj (c b) * K i.val b)]
      simp only [hc'val, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_right_comm _ _ _
    rw [← hdot]; exact hPD

/-- Helper: sum over fibers of a function.  For any `f : α → X`, the sum
`∑ i ∈ s, w i * Φ (f i)` can be regrouped by the value of `f i`. -/
private lemma sum_fiber_kernel {α X : Type*} [DecidableEq X]
    (s : Finset α) (f : α → X) (w : α → ℂ) (Φ : X → ℂ) :
    ∑ i ∈ s, w i * Φ (f i) =
    ∑ g ∈ s.image f, (∑ i ∈ s.filter (fun i => f i = g), w i) * Φ g := by
  let t := s.image f
  have hmaps : ∀ i ∈ s, f i ∈ t := fun i hi => Finset.mem_image_of_mem f hi
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  have hfg : ∀ i ∈ s.filter (fun i => f i = g), f i = g := fun i hi =>
    (Finset.mem_filter.mp hi).2
  have hsum : ∑ i ∈ s.filter (fun i => f i = g), w i * Φ (f i) =
      ∑ i ∈ s.filter (fun i => f i = g), w i * Φ g := by
    apply Finset.sum_congr rfl
    intro i hi; rw [hfg i hi]
  rw [hsum, ← Finset.sum_mul]

/-- For a Mercer-PD kernel, the quadratic form with a mapped index set
is non-negative.  This is the key grouping argument: even if `f : α → X` is
not injective, the sum `∑ c_i conj(c_j) K(f i, f j)` is non-negative. -/
lemma PositiveDefiniteKernel.sum_nonneg_of_map
    {X : Type*} {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    {α : Type*} (s : Finset α) (f : α → X) (c : α → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K (f i) (f j) := by
  classical
  let t := s.image f
  let d : X → ℂ := fun g => ∑ i ∈ s.filter (fun i => f i = g), c i
  have h_conj_d : ∀ h, ∑ j ∈ s.filter (fun j => f j = h), conj (c j) = conj (d h) := by
    intro h
    simp only [d, ← map_sum (starRingEnd ℂ)]
  have h_fiber_i : ∀ j ∈ s, ∑ i ∈ s, c i * K (f i) (f j) =
      ∑ g ∈ t, d g * K g (f j) := by
    intro j hj
    exact sum_fiber_kernel s f c (fun g => K g (f j))
  have h_fiber_j : ∀ g ∈ t, ∑ j ∈ s, conj (c j) * K g (f j) =
      ∑ h ∈ t, conj (d h) * K g h := by
    intro g hg
    rw [sum_fiber_kernel s f (fun j => conj (c j)) (fun h => K g h)]
    apply Finset.sum_congr rfl
    intro h hh
    rw [h_conj_d h]
  calc
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K (f i) (f j)
        = ∑ j ∈ s, ∑ i ∈ s, c i * conj (c j) * K (f i) (f j) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ s, conj (c j) * ∑ i ∈ s, c i * K (f i) (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h_rearr : ∑ i ∈ s, c i * conj (c j) * K (f i) (f j) =
          ∑ i ∈ s, conj (c j) * (c i * K (f i) (f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm (c i) (conj (c j)), mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ = ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * K g (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h_fiber_i j hj]
    _ = ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * K g (f j) := by
      have h1 : ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * K g (f j) =
          ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * K g (f j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [← mul_assoc]
      have h2 : ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * K g (f j) =
          ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * K g (f j) := by
        exact Finset.sum_comm ..
      have h3 : ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * K g (f j) =
          ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * K g (f j) := by
        apply Finset.sum_congr rfl
        intro g hg
        have h_rearr : ∑ j ∈ s, conj (c j) * d g * K g (f j) =
            ∑ j ∈ s, d g * (conj (c j) * K g (f j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_comm (conj (c j)) (d g), mul_assoc]
        rw [h_rearr, ← Finset.mul_sum]
      rw [h1, h2, h3]
    _ = ∑ g ∈ t, d g * ∑ h ∈ t, conj (d h) * K g h := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [h_fiber_j g hg]
    _ = ∑ g ∈ t, ∑ h ∈ t, d g * conj (d h) * K g h := by
      apply Finset.sum_congr rfl
      intro g hg
      have h_rearr : ∑ h ∈ t, d g * conj (d h) * K g h =
          ∑ h ∈ t, d g * (conj (d h) * K g h) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [← mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ ≥ 0 := hK.quadratic_form_nonneg t d

/-- A group-theoretic PD function gives a Mercer-PD kernel `K(x, y) = φ(x⁻¹ * y)`.
This shows the Mercer notion generalizes the group-theoretic one. -/
lemma PositiveDefinite.toPositiveDefiniteKernel
    {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefiniteKernel (fun x y => φ (x⁻¹ * y)) := by
  apply PositiveDefiniteKernel.of_quadratic_form
  intro s c; exact hφ s c

/-- A Mercer-PD kernel is Hermitian: `K(x, y) = conj(K(y, x))`, derived from
`Matrix.PosSemidef.IsHermitian` via the quadratic-form argument. -/
lemma PositiveDefiniteKernel.conj_symm {X : Type*} {K : X → X → ℂ}
    (hK : PositiveDefiniteKernel K) : ∀ x y, K x y = conj (K y x) :=
  quadratic_form_conj_symm K hK.quadratic_form_nonneg

/-- The constant-one kernel is Mercer-PD (via `of_quadratic_form`). -/
lemma PositiveDefiniteKernel.one (X : Type*) :
    PositiveDefiniteKernel (fun (_ _ : X) => (1 : ℂ)) := by
  apply PositiveDefiniteKernel.of_quadratic_form
  intro s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * 1) =
      conj (∑ i ∈ s, c i) * (∑ i ∈ s, c i) := by
    simp only [mul_one]
    rw [← Finset.sum_mul_sum, ← map_sum (starRingEnd ℂ) c s, mul_comm]
  rw [hsum, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- **Schur product theorem for Mercer-PD kernels.**  The pointwise product of
two Mercer-PD kernels is again Mercer-PD.  With the `Matrix.PosSemidef`-based
definition, this is a direct application of `Matrix.PosSemidef.hadamard` (the
Schur product theorem for positive-semidefinite matrices): the Hadamard product
of the two finite submatrices is positive-semidefinite, and `Matrix.hadamard`
is pointwise multiplication by definition. -/
lemma PositiveDefiniteKernel.mul {X : Type*} {K1 K2 : X → X → ℂ}
    (hK1 : PositiveDefiniteKernel K1) (hK2 : PositiveDefiniteKernel K2) :
    PositiveDefiniteKernel (fun x y => K1 x y * K2 x y) := by
  intro s
  exact Matrix.PosSemidef.hadamard (hK1 s) (hK2 s)

/-- Non-negative scaling preserves Mercer-PD (via `of_quadratic_form`). -/
lemma PositiveDefiniteKernel.smul_nonneg {X : Type*} {K : X → X → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hK : PositiveDefiniteKernel K) :
    PositiveDefiniteKernel (fun x y => (r : ℂ) * K x y) := by
  apply PositiveDefiniteKernel.of_quadratic_form
  intro s c
  have h := hK.quadratic_form_nonneg s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ((r : ℂ) * K i j)) =
      (r : ℂ) * (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j) := by
    simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [hsum]
  have h_nonneg_complex : (0 : ℂ) ≤ (r : ℂ) := by
    rw [Complex.nonneg_iff]; constructor
    · simpa using hr
    · simp
  exact mul_nonneg h_nonneg_complex h

/-- **Finite product of Mercer-PD kernels is Mercer-PD** (n-ary Schur product). -/
lemma PositiveDefiniteKernel.finprod {ι X : Type*} (s : Finset ι)
    (f : ι → X → X → ℂ) (hf : ∀ i ∈ s, PositiveDefiniteKernel (f i)) :
    PositiveDefiniteKernel (fun x y => ∏ i ∈ s, f i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact PositiveDefiniteKernel.one X
  | insert a s ha ih =>
    have hPDa : PositiveDefiniteKernel (f a) := hf a (Finset.mem_insert_self a s)
    have hPDs : PositiveDefiniteKernel (fun x y => ∏ i ∈ s, f i x y) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x y => ∏ i ∈ insert a s, f i x y) =
        fun x y => f a x y * ∏ i ∈ s, f i x y := by
      funext x y; rw [Finset.prod_insert ha]
    rw [heq]
    exact PositiveDefiniteKernel.mul hPDa hPDs

/-- **Mercer-PD is preserved by composition with a function on both arguments.**
If `K` is a Mercer-PD kernel on `Y` and `f : X → Y`, then
`fun x y => K (f x) (f y)` is a Mercer-PD kernel on `X`. -/
lemma PositiveDefiniteKernel.comp {X Y : Type*} {K : Y → Y → ℂ}
    (hK : PositiveDefiniteKernel K) (f : X → Y) :
    PositiveDefiniteKernel (fun x y => K (f x) (f y)) := by
  apply PositiveDefiniteKernel.of_quadratic_form
  intro s c
  exact hK.sum_nonneg_of_map s f c

/-- **Continuity of a Mercer-PD kernel is preserved by composition with a
continuous function on both arguments.** -/
lemma PositiveDefiniteKernel.continuous_comp {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {K : Y → Y → ℂ} (hK_cont : Continuous (Function.uncurry K))
    (f : X → Y) (hf_cont : Continuous f) :
    Continuous (Function.uncurry (fun x y => K (f x) (f y))) := by
  have hf_fst : Continuous (fun p : X × X => f p.1) := hf_cont.comp continuous_fst
  have hf_snd : Continuous (fun p : X × X => f p.2) := hf_cont.comp continuous_snd
  have hf_prod : Continuous (fun p : X × X => (f p.1, f p.2)) :=
    Continuous.prodMk hf_fst hf_snd
  exact hK_cont.comp hf_prod

/-- **A continuous Mercer-PD kernel on a compact space defines a positive
integral operator.**

For a compact (pseudo)metric space `X` with probability measure `μ`, a
continuous kernel `K` that is positive-definite in the Mercer sense, and a
continuous function `f`, the integral
`∫∫ f(x) * conj(f(y)) * K(x, y) dμ dμ ≥ 0`.

The proof approximates the integral by Riemann sums (each non-negative by
`PositiveDefiniteKernel.sum_nonneg_of_map`) and controls the error via
uniform continuity on the compact space `X × X`.  No group structure is
needed. -/
lemma PositiveDefiniteKernel.integralOperator_nonneg
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    (hK_cont : Continuous (Function.uncurry K))
    {f : X → ℂ} (hf_cont : Continuous f) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ := by
  let F : X × X → ℂ := fun p => f p.1 * conj (f p.2) * K p.1 p.2
  have hF_cont : Continuous F := by
    have h_fst : Continuous (fun p : X × X => f p.1) := hf_cont.comp continuous_fst
    have h_snd : Continuous (fun p : X × X => f p.2) := hf_cont.comp continuous_snd
    have h_conj_snd : Continuous (fun p : X × X => conj (f p.2)) :=
      Complex.continuous_conj.comp h_snd
    have h_K : Continuous (fun p : X × X => K p.1 p.2) := hK_cont
    convert Continuous.mul (Continuous.mul h_fst h_conj_snd) h_K using 1
    ext p; rfl
  haveI : CompactSpace (X × X) := inferInstance
  have hF_unif : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF_cont
  have hF_aes : AEStronglyMeasurable F (μ.prod μ) :=
    Continuous.aestronglyMeasurable_of_compactSpace hF_cont
  have hF_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : X × X, ‖F z‖ ≤ C := by
    have h_range_compact : IsCompact (Set.range F) := by
      rw [← Set.image_univ]
      exact isCompact_univ.image hF_cont
    obtain ⟨C, hCpos, hC⟩ := h_range_compact.isBounded.exists_pos_norm_le
    exact ⟨C, hCpos.le, fun z => hC (F z) (Set.mem_range_self _)⟩
  obtain ⟨C, hCnn, hC⟩ := hF_bdd
  have hF_int : Integrable F (μ.prod μ) := by
    apply Integrable.of_bound hF_aes C
    filter_upwards with z using hC z
  have hFub : ∫ z, F z ∂(μ.prod μ) = ∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ := by
    rw [integral_prod F hF_int]
  rw [← hFub]
  set I : ℂ := ∫ z, F z ∂(μ.prod μ)
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ S : ℂ, 0 ≤ S ∧ ‖I - S‖ ≤ ε := by
    intro ε εpos
    obtain ⟨δ, δpos, hδ⟩ := Metric.uniformContinuous_iff.mp hF_unif ε εpos
    obtain ⟨t, _, ht_fin, ht_cover⟩ :=
      finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set X)) (half_pos δpos)
    let ts : Finset X := ht_fin.toFinset
    have hts_eq : ↑ts = t := ht_fin.coe_toFinset
    let n := ts.card
    let e : Fin n ≃ ↥ts := ts.equivFin.symm
    let x : Fin n → X := fun i => (e i : X)
    let B : Fin n → Set X := fun i => ball (x i) (δ / 2)
    have hA_disjoint : Pairwise (Disjoint on disjointed B) := disjoint_disjointed B
    have hA_cover : (Set.univ : Set X) ⊆ ⋃ (i : Fin n), disjointed B i := by
      rw [iUnion_disjointed]
      intro g hg
      simp only [Set.mem_iUnion]
      have hg' := ht_cover hg
      simp only [Set.mem_iUnion₂] at hg'
      obtain ⟨xg, hxg, hg_ball⟩ := hg'
      have hxg_ts : xg ∈ ts := by
        have : xg ∈ (↑ts : Set X) := hts_eq.symm ▸ hxg
        exact Finset.mem_coe.mp this
      obtain ⟨i, hi⟩ := (Equiv.surjective e) ⟨xg, hxg_ts⟩
      refine ⟨i, ?_⟩
      have hxi : x i = xg := by simp only [x, hi]
      simp only [B, hxi]
      exact hg_ball
    have hA_meas : ∀ (i : Fin n), MeasurableSet (disjointed B i) := by
      intro i
      rw [disjointed_apply, Finset.sup_set_eq_biUnion]
      exact MeasurableSet.diff isOpen_ball.measurableSet
        (Finset.measurableSet_biUnion _ (fun j _ => isOpen_ball.measurableSet))
    let c : Fin n → ℂ := fun i => f (x i) * ((μ.real (disjointed B i)) : ℂ)
    refine ⟨∑ i, ∑ j, c i * conj (c j) * K (x i) (x j), ?_, ?_⟩
    · exact hK.sum_nonneg_of_map Finset.univ x c
    · have hCover : (Set.univ : Set (X × X)) =
        ⋃ (ij : Fin n × Fin n), disjointed B ij.1 ×ˢ disjointed B ij.2 := by
        rw [Set.iUnion_prod]
        have hU : (⋃ i, disjointed B i) = (Set.univ : Set X) :=
          (Set.subset_univ _).antisymm hA_cover
        simp only [hU, Set.univ_prod_univ]
      have hDisj : Pairwise (Disjoint on
          fun ij : Fin n × Fin n => disjointed B ij.1 ×ˢ disjointed B ij.2) := by
        intro ij ij' hij
        simp only [Function.onFun]
        rw [Set.disjoint_prod]
        by_cases h1 : ij.1 = ij'.1
        · right; exact hA_disjoint (fun heq => hij (Prod.ext h1 heq))
        · left; exact hA_disjoint h1
      have hMeas' : ∀ (ij : Fin n × Fin n),
          MeasurableSet (disjointed B ij.1 ×ˢ disjointed B ij.2) :=
        fun ij => MeasurableSet.prod (hA_meas ij.1) (hA_meas ij.2)
      have hInt' : ∀ (ij : Fin n × Fin n),
          IntegrableOn F (disjointed B ij.1 ×ˢ disjointed B ij.2) (μ.prod μ) :=
        fun ij => hF_int.integrableOn
      have hI_part : I = ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F z ∂(μ.prod μ) := by
        rw [show I = ∫ z in Set.univ, F z ∂(μ.prod μ) from setIntegral_univ.symm, hCover]
        exact integral_iUnion_fintype hMeas' hDisj hInt'
      have h_term : ∀ (ij : Fin n × Fin n),
          c ij.1 * conj (c ij.2) * K (x ij.1) (x ij.2) =
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F (x ij.1, x ij.2) ∂(μ.prod μ) := by
        intro ij
        rw [setIntegral_const, measureReal_prod_prod]
        simp only [c, F, map_mul, Complex.conj_ofReal,
          Algebra.smul_def, Complex.coe_algebraMap]
        ring
      have hS_part : (∑ i, ∑ j, c i * conj (c j) * K (x i) (x j)) =
          ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F (x ij.1, x ij.2) ∂(μ.prod μ) := by
        rw [← Finset.sum_product', Finset.univ_product_univ]
        exact Finset.sum_congr rfl (fun ij _ => h_term ij)
      have hIS : I - ∑ i, ∑ j, c i * conj (c j) * K (x i) (x j) =
          ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2,
            (F z - F (x ij.1, x ij.2)) ∂(μ.prod μ) := by
        rw [hI_part, hS_part, sub_eq_add_neg, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ij _
        rw [← sub_eq_add_neg, ← integral_sub (hInt' ij) ((integrable_const _).integrableOn)]
      have hUC : ∀ (ij : Fin n × Fin n),
          ∀ z ∈ disjointed B ij.1 ×ˢ disjointed B ij.2,
          ‖F z - F (x ij.1, x ij.2)‖ ≤ ε := by
        intro ij z hz
        have ha : z.1 ∈ disjointed B ij.1 := hz.1
        have hb : z.2 ∈ disjointed B ij.2 := hz.2
        have ha_sub : disjointed B ij.1 ⊆ B ij.1 := disjointed_subset B ij.1
        have hb_sub : disjointed B ij.2 ⊆ B ij.2 := disjointed_subset B ij.2
        have ha_dist : dist z.1 (x ij.1) < δ / 2 := ha_sub ha
        have hb_dist : dist z.2 (x ij.2) < δ / 2 := hb_sub hb
        have hdist : dist z (x ij.1, x ij.2) < δ := by
          rw [Prod.dist_eq]
          exact (max_lt ha_dist hb_dist).trans (by linarith [δpos])
        have hnorm : ‖F z - F (x ij.1, x ij.2)‖ < ε := by
          have := hδ hdist
          rwa [dist_eq_norm] at this
        exact le_of_lt hnorm
      have hSumMeas : ∑ (ij : Fin n × Fin n),
          (μ.prod μ).real (disjointed B ij.1 ×ˢ disjointed B ij.2) = 1 := by
        rw [← measureReal_iUnion_fintype hDisj hMeas', ← hCover]
        simp [measureReal_def]
      rw [hIS]
      calc ‖∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2,
            (F z - F (x ij.1, x ij.2)) ∂(μ.prod μ)‖
          ≤ ∑ (ij : Fin n × Fin n),
              ‖∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2,
                  (F z - F (x ij.1, x ij.2)) ∂(μ.prod μ)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ (ij : Fin n × Fin n),
              ε * (μ.prod μ).real (disjointed B ij.1 ×ˢ disjointed B ij.2) := by
            apply Finset.sum_le_sum
            intro ij _
            exact norm_setIntegral_le_of_norm_le_const (by finiteness) (hUC ij)
        _ = ε * ∑ (ij : Fin n × Fin n),
              (μ.prod μ).real (disjointed B ij.1 ×ˢ disjointed B ij.2) := by
            rw [← Finset.mul_sum]
        _ = ε * 1 := by rw [hSumMeas]
        _ = ε := mul_one ε
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · by_contra h
    have hneg : I.re < 0 := lt_of_not_ge h
    obtain ⟨S, hS_nonneg, hS_bound⟩ := hkey (-I.re / 2) (half_pos (neg_pos.mpr hneg))
    have hReS : 0 ≤ S.re := (Complex.nonneg_iff.mp hS_nonneg).1
    have h_abs : |I.re - S.re| ≤ ‖I - S‖ := by
      rw [show I.re - S.re = (I - S).re from rfl]
      exact abs_re_le_norm (I - S)
    have h_bound : |I.re - S.re| ≤ -I.re / 2 := h_abs.trans hS_bound
    have h_lower : I.re ≥ S.re - (-I.re / 2) := by linarith [abs_le.mp h_bound]
    linarith
  · by_contra h
    have hne : I.im ≠ 0 := fun heq => h heq.symm
    have habs : 0 < |I.im| := abs_pos.mpr hne
    obtain ⟨S, hS_nonneg, hS_bound⟩ := hkey (|I.im| / 2) (half_pos habs)
    have hImS : S.im = 0 := (Complex.nonneg_iff.mp hS_nonneg).2.symm
    have h_abs : |I.im - S.im| ≤ ‖I - S‖ := by
      rw [show I.im - S.im = (I - S).im from rfl]
      exact abs_im_le_norm (I - S)
    have h_bound : |I.im| ≤ |I.im| / 2 := by
      rw [hImS] at h_abs
      simp only [sub_zero] at h_abs
      exact h_abs.trans hS_bound
    linarith

#print axioms PositiveDefiniteKernel.quadratic_form_nonneg
#print axioms PositiveDefiniteKernel.of_quadratic_form
#print axioms PositiveDefiniteKernel.conj_symm
#print axioms PositiveDefiniteKernel.one
#print axioms PositiveDefiniteKernel.mul
#print axioms PositiveDefiniteKernel.smul_nonneg
#print axioms PositiveDefiniteKernel.finprod
#print axioms PositiveDefiniteKernel.comp
#print axioms PositiveDefiniteKernel.continuous_comp
#print axioms PositiveDefiniteKernel.sum_nonneg_of_map
#print axioms PositiveDefiniteKernel.integralOperator_nonneg
#print axioms PositiveDefinite.toPositiveDefiniteKernel
