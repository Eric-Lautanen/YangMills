/-
# Positive Definite: Product Group
-/

import YangMills.Proofs.PositiveDefinite.Basic

open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills
section ProductGroup

attribute [local instance] Classical.propDecidable

/-- Helper: sum over fibers of a function.  For any `f : α → G`, the sum
`∑ i ∈ s, w i * Φ (f i)` can be regrouped by the value of `f i`. -/
lemma sum_fiber {α : Type*} {G : Type*}
    (s : Finset α) (f : α → G) (w : α → ℂ) (Φ : G → ℂ) :
    ∑ i ∈ s, w i * Φ (f i) =
    ∑ g ∈ s.image f, (∑ i ∈ s.filter (fun i => f i = g), w i) * Φ g := by
  classical
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

/-- For a positive-definite function `φ`, the quadratic form with a mapped index set
is non-negative.  This is the key grouping argument: even if `f : α → G` is not
injective, the sum `∑ c_i conj(c_j) φ(f(i)⁻¹ * f(j))` is non-negative. -/
lemma PositiveDefinite.sum_nonneg_of_map
    {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ)
    {α : Type*} (s : Finset α) (f : α → G) (c : α → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j) := by
  classical
  let t := s.image f
  let d : G → ℂ := fun g => ∑ i ∈ s.filter (fun i => f i = g), c i
  have h_conj_d : ∀ h, ∑ j ∈ s.filter (fun j => f j = h), conj (c j) = conj (d h) := by
    intro h
    simp only [d, ← map_sum (starRingEnd ℂ)]
  have h_fiber_i : ∀ j ∈ s, ∑ i ∈ s, c i * φ ((f i)⁻¹ * f j) =
      ∑ g ∈ t, d g * φ (g⁻¹ * f j) := by
    intro j hj
    exact sum_fiber s f c (fun g => φ (g⁻¹ * f j))
  have h_fiber_j : ∀ g ∈ t, ∑ j ∈ s, conj (c j) * φ (g⁻¹ * f j) =
      ∑ h ∈ t, conj (d h) * φ (g⁻¹ * h) := by
    intro g hg
    rw [sum_fiber s f (fun j => conj (c j)) (fun h => φ (g⁻¹ * h))]
    apply Finset.sum_congr rfl
    intro h hh
    rw [h_conj_d h]
  calc
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)
        = ∑ j ∈ s, ∑ i ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ s, conj (c j) * ∑ i ∈ s, c i * φ ((f i)⁻¹ * f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h_rearr : ∑ i ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j) =
          ∑ i ∈ s, conj (c j) * (c i * φ ((f i)⁻¹ * f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm (c i) (conj (c j)), mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ = ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * φ (g⁻¹ * f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h_fiber_i j hj]
    _ = ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * φ (g⁻¹ * f j) := by
      have h1 : ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * φ (g⁻¹ * f j) =
          ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * φ (g⁻¹ * f j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [← mul_assoc]
      have h2 : ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * φ (g⁻¹ * f j) =
          ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * φ (g⁻¹ * f j) := by
        exact Finset.sum_comm ..
      have h3 : ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * φ (g⁻¹ * f j) =
          ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * φ (g⁻¹ * f j) := by
        apply Finset.sum_congr rfl
        intro g hg
        have h_rearr : ∑ j ∈ s, conj (c j) * d g * φ (g⁻¹ * f j) =
            ∑ j ∈ s, d g * (conj (c j) * φ (g⁻¹ * f j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_comm (conj (c j)) (d g), mul_assoc]
        rw [h_rearr, ← Finset.mul_sum]
      rw [h1, h2, h3]
    _ = ∑ g ∈ t, d g * ∑ h ∈ t, conj (d h) * φ (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [h_fiber_j g hg]
    _ = ∑ g ∈ t, ∑ h ∈ t, d g * conj (d h) * φ (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g hg
      have h_rearr : ∑ h ∈ t, d g * conj (d h) * φ (g⁻¹ * h) =
          ∑ h ∈ t, d g * (conj (d h) * φ (g⁻¹ * h)) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [← mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ ≥ 0 := hφ t d

/-- For a positive-definite function `φ`, the matrix `φ(f(i)⁻¹ * f(j))` indexed
by a finset `s` (via a possibly non-injective map `f`) is positive semidefinite. -/
lemma PositiveDefinite.matrix_posSemidef_of_map
    {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ)
    {α : Type*} (s : Finset α) (f : α → G) :
    Matrix.PosSemidef (fun (i j : ↥s) => φ ((f i.val)⁻¹ * f j.val) : Matrix ↥s ↥s ℂ) := by
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  refine (Matrix.posSemidef_iff_dotProduct_mulVec (M := (fun (i j : ↥s) => φ ((f i.val)⁻¹ * f j.val) : Matrix ↥s ↥s ℂ))).mpr ?_
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    show conj (φ ((f j.val)⁻¹ * f i.val)) = φ ((f i.val)⁻¹ * f j.val)
    rw [← hφ.conj_inv ((f j.val)⁻¹ * f i.val)]
    congr 1
    simp [_root_.mul_inv_rev, inv_inv]
  · intro x
    set c : α → ℂ := fun a => if ha : a ∈ s then conj (x ⟨a, ha⟩) else 0
    have hcval : ∀ i : ↥s, c i.val = conj (x i) := fun i => by
      simp only [c, dif_pos i.property]
    have hcconj : ∀ j : ↥s, conj (c j.val) = x j := fun j => by
      rw [hcval j]; exact star_star _
    let M : Matrix ↥s ↥s ℂ := fun i j => φ ((f i.val)⁻¹ * f j.val)
    have hquad : star x ⬝ᵥ (M *ᵥ x) =
        (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      simp only [M, Pi.star_apply, Complex.star_def]
      conv_rhs => rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [← Finset.sum_coe_sort]
      simp only [hcval, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_right_comm _ _ _
    rw [hquad]
    exact hφ.sum_nonneg_of_map s f c

/-- **Product of positive-definite functions on different groups.**
If `φ : G → ℂ` is positive-definite and `ψ : H → ℂ` is positive-definite,
then `(g, h) ↦ φ(g) * ψ(h)` is positive-definite on `G × H`.

This follows from the Schur product theorem: the kernel matrix factors as a
Hadamard product of two PSD matrices (one from `φ` on the `G`-component, one
from `ψ` on the `H`-component), each PSD by the grouping argument. -/
lemma PositiveDefinite.prod {G H : Type*} [Group G] [Group H]
    {φ : G → ℂ} {ψ : H → ℂ} (hφ : PositiveDefinite φ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite (λ (p : G × H) => φ p.1 * ψ p.2) := by
  intro s c
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let A : Matrix ↥s ↥s ℂ := fun i j => φ ((i.val.1)⁻¹ * j.val.1)
  let B : Matrix ↥s ↥s ℂ := fun i j => ψ ((i.val.2)⁻¹ * j.val.2)
  have hA : Matrix.PosSemidef A := hφ.matrix_posSemidef_of_map s (fun p => p.1)
  have hB : Matrix.PosSemidef B := hψ.matrix_posSemidef_of_map s (fun p => p.2)
  have hAB : Matrix.PosSemidef (A ⊙ B) := Matrix.PosSemidef.hadamard hA hB
  let w : ↥s → ℂ := fun i => conj (c i.val)
  have hquad : 0 ≤ star w ⬝ᵥ ((A ⊙ B) *ᵥ w) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hAB w
  have htarget : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) *
      (φ ((i⁻¹ * j).1) * ψ ((i⁻¹ * j).2))) =
      star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp only [Pi.star_apply, Complex.star_def, Matrix.hadamard_apply, A, B, w,
      Complex.conj_conj]
    conv_lhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_right_comm _ _ _
  rw [htarget]
  exact hquad

end ProductGroup
