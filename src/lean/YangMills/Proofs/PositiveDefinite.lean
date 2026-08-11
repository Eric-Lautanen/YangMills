/-
# Positive-Definite Functions on Groups

A function φ : G → ℂ on a group G is called *positive-definite* if for any
finite set {g₁, ..., gₙ} ⊂ G and coefficients {c₁, ..., cₙ} ⊂ ℂ:

    Σ_{i,j} c_i · conj(c_j) · φ(g_i⁻¹ g_j) ≥ 0

## References

* K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"
  (Ann. Phys. 110, 1978, pp 440–471), §3.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import YangMills.SpecialUnitary
open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills

/-- A function φ : G → ℂ is positive-definite. -/
def PositiveDefinite {G : Type*} [Group G] (φ : G → ℂ) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)) ≥ 0

section BasicProperties

variable {G : Type*} [Group G] {φ ψ : G → ℂ}

/-- Positive-definiteness is invariant under function equality: if `φ = ψ`
pointwise and `ψ` is PD, then `φ` is PD.  This avoids expensive `convert` /
`exact` defeq checks on large functions — prove the equality with `funext` +
`simp` (which handles stuck matches via case analysis), then transfer PD. -/
lemma PositiveDefinite.congr (h : φ = ψ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite φ := by
  rw [h]; exact hψ

lemma PositiveDefinite.add (hφ : PositiveDefinite φ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite (λ g => φ g + ψ g) := by
  intro s c
  have h1 := hφ s c
  have h2 := hψ s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ((λ g => φ g + ψ g) (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)) +
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ψ (i⁻¹ * j)) := by
    simp [Finset.sum_add_distrib, mul_add]
  rw [hsum]
  exact add_nonneg h1 h2

lemma PositiveDefinite.smul_nonneg {r : ℝ} (hr : 0 ≤ r) (hφ : PositiveDefinite φ) :
    PositiveDefinite (λ g => (r : ℂ) * φ g) := by
  intro s c
  have h := hφ s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ((r : ℂ) * φ (i⁻¹ * j))) =
      (r : ℂ) * (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)) := by
    simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [hsum]
  have h_nonneg_complex : (0 : ℂ) ≤ (r : ℂ) := by
    rw [Complex.nonneg_iff]
    constructor
    · simpa using hr
    · simp
  exact mul_nonneg h_nonneg_complex h

/-- A positive-definite function satisfies φ(g⁻¹) = conj(φ(g)). -/
lemma PositiveDefinite.conj_inv (hφ : PositiveDefinite φ) : ∀ g, φ g⁻¹ = conj (φ g) := by
  intro g
  classical
  have h_one : 0 ≤ φ (1 : G) := by
    have h := hφ (Finset.cons 1 ∅ (by simp)) (fun _ => 1)
    simp [Finset.sum_empty] at h
    exact h
  have h_one_im : (φ (1 : G)).im = 0 := (Complex.nonneg_iff.mp h_one).2.symm
  by_cases hg : g = 1
  · subst hg; rw [inv_one]; exact (Complex.conj_eq_iff_im.mpr h_one_im).symm
  · have hS : ∀ t : ℂ, 0 ≤ (1 + t * conj t) * φ (1 : G) + conj t * φ g + t * φ g⁻¹ := by
      intro t
      have hne1 : (g : G) ∉ (∅ : Finset G) := by simp
      have hne2 : (1 : G) ∉ Finset.cons g ∅ hne1 := by simp [Ne.symm hg]
      have h := hφ (Finset.cons 1 (Finset.cons g ∅ hne1) hne2) (fun x => if x = 1 then 1 else t)
      have hsum : (∑ i ∈ Finset.cons 1 (Finset.cons g ∅ hne1) hne2,
          ∑ j ∈ Finset.cons 1 (Finset.cons g ∅ hne1) hne2,
          (if i = 1 then 1 else t) * conj (if j = 1 then 1 else t) * φ (i⁻¹ * j)) =
          (1 + t * conj t) * φ (1 : G) + conj t * φ g + t * φ g⁻¹ := by
        simp only [Finset.sum_cons, Finset.sum_empty, if_pos (rfl : (1 : G) = 1), if_neg hg]
        simp only [one_mul, mul_one, inv_one, map_one, ite_true]
        simp only [show (g : G)⁻¹ * g = 1 from by simp]
        ring
      rw [hsum] at h
      exact h
    have h_im_sum : (φ g).im + (φ g⁻¹).im = 0 := by
      have key := (Complex.nonneg_iff.mp (hS 1)).2
      have hkey : (1 + 1 * conj 1) * φ (1 : G) + conj 1 * φ g + 1 * φ g⁻¹ =
          2 * φ (1 : G) + φ g + φ g⁻¹ := by simp only [map_one, one_mul, mul_one]; ring
      rw [hkey] at key
      have h2 : (2 * φ (1 : G) + φ g + φ g⁻¹).im = 2 * (φ (1 : G)).im + (φ g).im + (φ g⁻¹).im := by
        simp [Complex.add_im]
      rw [h2, h_one_im] at key
      linarith
    have h_re_diff : (φ g⁻¹).re - (φ g).re = 0 := by
      have key := (Complex.nonneg_iff.mp (hS Complex.I)).2
      have hI2 : Complex.I * conj Complex.I = 1 := by simp [Complex.conj_I]
      have heq : (1 + Complex.I * conj Complex.I) * φ (1 : G) +
        conj Complex.I * φ g + Complex.I * φ g⁻¹ =
        2 * φ (1 : G) + Complex.I * (φ g⁻¹ - φ g) := by simp [Complex.conj_I]; ring
      rw [heq] at key
      have h2 : (2 * φ (1 : G) + Complex.I * (φ g⁻¹ - φ g)).im =
          2 * (φ (1 : G)).im + ((φ g⁻¹).re - (φ g).re) := by
        simp [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.I_re, Complex.I_im]
      rw [h2, h_one_im] at key
      linarith
    apply Complex.ext
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_im]; linarith

/-- The zero function is positive-definite. -/
lemma PositiveDefinite.zero : PositiveDefinite (λ (_ : G) => (0 : ℂ)) := by
  intro s c; simp

/-- The constant-one function is positive-definite. -/
lemma PositiveDefinite.one : PositiveDefinite (λ (_ : G) => (1 : ℂ)) := by
  intro s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * 1) =
      conj (∑ i ∈ s, c i) * (∑ i ∈ s, c i) := by
    simp only [mul_one]
    rw [← Finset.sum_mul_sum, ← map_sum (starRingEnd ℂ) c s, mul_comm]
  rw [hsum, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- A positive-definite function gives a positive-semidefinite matrix on any finite subset. -/
private lemma PositiveDefinite.matrix_posSemidef (hφ : PositiveDefinite φ) (s : Finset G) :
    Matrix.PosSemidef (fun (i j : ↥s) => φ (i.val⁻¹ * j.val) : Matrix ↥s ↥s ℂ) := by
  haveI : DecidableEq ↥s := Classical.decEq _
  classical
  refine (Matrix.posSemidef_iff_dotProduct_mulVec (M := (fun (i j : ↥s) => φ (i.val⁻¹ * j.val) : Matrix ↥s ↥s ℂ))).mpr ?_
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    show conj (φ (j.val⁻¹ * i.val)) = φ (i.val⁻¹ * j.val)
    rw [← hφ.conj_inv (j.val⁻¹ * i.val)]
    congr 1
    simp
  · intro x
    let c' : G → ℂ := fun g => if hg : g ∈ s then conj (x ⟨g, hg⟩) else 0
    have hPD := hφ s c'
    have hc'val : ∀ i : ↥s, c' i.val = conj (x i) := by
      intro i
      simp only [c', dif_pos i.property]
    have hc'conj : ∀ j : ↥s, conj (c' j.val) = x j := by
      intro j
      rw [hc'val j]
      exact star_star _
    let M : Matrix ↥s ↥s ℂ := fun i j => φ (i.val⁻¹ * j.val)
    have hdot : star x ⬝ᵥ (M *ᵥ x) =
        (∑ i ∈ s, ∑ j ∈ s, c' i * conj (c' j) * φ (i⁻¹ * j)) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      simp only [M, Pi.star_apply, Complex.star_def]
      conv_rhs => rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [← Finset.sum_coe_sort]
      simp only [hc'val, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_right_comm _ _ _
    rw [hdot]
    exact hPD

/-- Pointwise product of two positive-definite functions is positive-definite (Schur product theorem). -/
lemma PositiveDefinite.mul (hφ : PositiveDefinite φ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite (λ g => φ g * ψ g) := by
  intro s c
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let A : Matrix ↥s ↥s ℂ := fun i j => φ (i.val⁻¹ * j.val)
  let B : Matrix ↥s ↥s ℂ := fun i j => ψ (i.val⁻¹ * j.val)
  let v : ↥s → ℂ := fun i => c i.val
  have hA : Matrix.PosSemidef A := hφ.matrix_posSemidef s
  have hB : Matrix.PosSemidef B := hψ.matrix_posSemidef s
  have hAB : Matrix.PosSemidef (A ⊙ B) := Matrix.PosSemidef.hadamard hA hB
  let w : ↥s → ℂ := fun i => conj (v i)
  have hquad : 0 ≤ star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := Matrix.PosSemidef.dotProduct_mulVec_nonneg hAB w
  have htarget : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (φ (i⁻¹ * j) * ψ (i⁻¹ * j))) =
      star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp only [Pi.star_apply, Complex.star_def, Matrix.hadamard_apply, A, B, w, v,
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

/-- Pointwise power of a positive-definite function is positive-definite. -/
lemma PositiveDefinite.pow (hφ : PositiveDefinite φ) (n : ℕ) : PositiveDefinite (φ ^ n) := by
  induction n with
  | zero => simp [pow_zero]; exact PositiveDefinite.one
  | succ n ih =>
    have h := PositiveDefinite.mul ih hφ
    rw [show φ ^ (n + 1) = (λ g => (φ ^ n) g * φ g) from by funext g; simp [pow_succ]]
    exact h

/-- Pointwise limit of positive-definite functions is positive-definite. -/
lemma PositiveDefinite.tendsto {F : ℕ → G → ℂ} {φ : G → ℂ}
    (hPD : ∀ n, PositiveDefinite (F n))
    (hlim : ∀ g, Tendsto (fun n => F n g) atTop (nhds (φ g))) :
    PositiveDefinite φ := by
  intro s c
  have hGn_nonneg : ∀ n, 0 ≤ (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * F n (i⁻¹ * j)) :=
    fun n => hPD n s c
  have hGn_tendsto : Tendsto (fun n => ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * F n (i⁻¹ * j)) atTop
      (nhds (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j))) := by
    exact tendsto_finsetSum s (fun i _ =>
      tendsto_finsetSum s (fun j _ =>
        Tendsto.mul tendsto_const_nhds (hlim (i⁻¹ * j))))
  exact ge_of_tendsto' hGn_tendsto hGn_nonneg

end BasicProperties

section ProductGroup

attribute [local instance] Classical.propDecidable

/-- Helper: sum over fibers of a function.  For any `f : α → G`, the sum
`∑ i ∈ s, w i * Φ (f i)` can be regrouped by the value of `f i`. -/
private lemma sum_fiber {α : Type*} {G : Type*}
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
private lemma PositiveDefinite.matrix_posSemidef_of_map
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

/-! ## Building blocks for the full Boltzmann factor

These lemmas are the abstract ingredients needed to promote the single-plaquette
positive-definiteness result `plaquetteBoltzmannPD` (in `PeterWeyl.lean`) to
positive-definiteness of the *full* Wilson Boltzmann factor
`exp(-β · S_W)` on the entire link-variable group `SU(N)^{#links}`.

* `PositiveDefinite.comp_mulEquiv`: positive-definiteness is preserved by group
  isomorphisms.  This lets one permute / rearrange the factors of a product group
  (e.g. place four plaquette links at arbitrary positions among all links).
* `PositiveDefinite.fst` / `.snd`: a positive-definite function on one factor,
  viewed as a function on a product group that ignores the other factor, is
  positive-definite.  This lets one regard a single-plaquette factor (which
  depends on only four links) as a function on the full link group.
* `PositiveDefinite.finprod`: a finite product of positive-definite functions on
  the same group is positive-definite (the n-ary Schur product theorem).  This
  combines the individual (extended) plaquette factors into the full Boltzmann
  factor `∏_p exp(β · Re Tr(U_{∂p}))`.
-/

section BuildingBlocks

variable {G H : Type*} [Group G] [Group H]

/-- Positive-definiteness is preserved by group isomorphisms: if `e : G ≃* H`
is a group isomorphism and `φ : H → ℂ` is positive-definite, then
`φ ∘ e : G → ℂ` is positive-definite.  The proof regroups the quadratic form by
the image of `e` using `PositiveDefinite.sum_nonneg_of_map`. -/
lemma PositiveDefinite.comp_mulEquiv (e : G ≃* H) {φ : H → ℂ}
    (hφ : PositiveDefinite φ) : PositiveDefinite (fun g => φ (e g)) := by
  intro s c
  have hkey := hφ.sum_nonneg_of_map s e c
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (e (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((e i)⁻¹ * e j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [MulEquiv.map_mul, MulEquiv.map_inv]
  rw [hsum_eq]
  exact hkey

/-- Positive-definiteness is preserved by group homomorphisms: if `f : G →* H`
is a group homomorphism and `φ : H → ℂ` is positive-definite, then
`φ ∘ f : G → ℂ` is positive-definite.  This generalizes `comp_mulEquiv` from
isomorphisms to arbitrary homomorphisms (e.g. coordinate projections from a
product group to a sub-product).  The proof regroups the quadratic form by the
image of `f` using `PositiveDefinite.sum_nonneg_of_map`. -/
lemma PositiveDefinite.comp_hom (f : G →* H) {φ : H → ℂ}
    (hφ : PositiveDefinite φ) : PositiveDefinite (fun g => φ (f g)) := by
  intro s c
  have hkey := hφ.sum_nonneg_of_map s f c
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (f (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [MonoidHom.map_mul, MonoidHom.map_inv]
  rw [hsum_eq]
  exact hkey

/-- A positive-definite function on `G`, regarded as a function on `G × H` that
ignores the `H`-component, is positive-definite on `G × H`. -/
lemma PositiveDefinite.fst {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefinite (fun (p : G × H) => φ p.1) := by
  have h := PositiveDefinite.prod hφ (@PositiveDefinite.one H _)
  convert h using 1
  ext p; simp

/-- A positive-definite function on `H`, regarded as a function on `G × H` that
ignores the `G`-component, is positive-definite on `G × H`. -/
lemma PositiveDefinite.snd {ψ : H → ℂ} (hψ : PositiveDefinite ψ) :
    PositiveDefinite (fun (p : G × H) => ψ p.2) := by
  have h := PositiveDefinite.prod (@PositiveDefinite.one G _) hψ
  convert h using 1
  ext p; simp

/-- A finite product of positive-definite functions on the same group is
positive-definite (the n-ary Schur product theorem). -/
lemma PositiveDefinite.finprod {ι : Type*} (s : Finset ι) (f : ι → G → ℂ)
    (hf : ∀ i ∈ s, PositiveDefinite (f i)) :
    PositiveDefinite (fun g => ∏ i ∈ s, f i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PositiveDefinite.one]
  | insert x s hx ih =>
    have hPDx : PositiveDefinite (f x) := hf x (Finset.mem_insert_self x s)
    have hPDs : PositiveDefinite (fun g => ∏ i ∈ s, f i g) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun g => ∏ i ∈ insert x s, f i g) =
        fun g => f x g * ∏ i ∈ s, f i g := by
      funext g; rw [Finset.prod_insert hx]
    rw [heq]
    exact PositiveDefinite.mul hPDx hPDs

end BuildingBlocks

section SU_N

open Matrix

lemma conjTranspose_eq_inv (N : ℕ) (g : SU N) :
    ((g : Matrix (Fin N) (Fin N) ℂ)ᴴ) = (g : Matrix (Fin N) (Fin N) ℂ)⁻¹ := by
  have h_unitary : (g : Matrix (Fin N) (Fin N) ℂ) * ((g : Matrix (Fin N) (Fin N) ℂ)ᴴ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp g.property.1)
  exact (Matrix.inv_eq_right_inv h_unitary).symm

noncomputable def fundamentalCharacter (N : ℕ) (g : SU N) : ℂ :=
  Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)

lemma fundamentalCharacter_positiveDefinite (N : ℕ) :
    PositiveDefinite (fundamentalCharacter N) := by
  intro s c
  have h_nonneg_sq : ∀ (M : Matrix (Fin N) (Fin N) ℂ), 0 ≤ Matrix.trace (Mᴴ * M) := by
    intro M
    have : Matrix.trace (Mᴴ * M) = (∑ i : Fin N, (Mᴴ * M) i i : ℂ) := by
      simp [Matrix.trace]
    rw [this]
    refine Finset.sum_nonneg (λ i _ => ?_)
    have : (Mᴴ * M) i i = ∑ k : Fin N, conj (M k i) * M k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [this]
    refine Finset.sum_nonneg (λ k _ => ?_)
    have : 0 ≤ conj (M k i) * M k i := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have h_nonneg_sq_val : 0 ≤ Complex.normSq (M k i) := Complex.normSq_nonneg _
      rw [Complex.nonneg_iff]
      constructor
      · simpa using h_nonneg_sq_val
      · simp
    exact this
  have dummy : True := trivial
  have h_tr_eq : Matrix.trace (
      ((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) *
      (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * fundamentalCharacter N (i⁻¹ * j)) :=
    calc
      Matrix.trace (((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)))
          = Matrix.trace ((∑ i ∈ s, (c i : ℂ) • (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹)) * (∑ j ∈ s, (conj (c j) : ℂ) • ((j : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
        simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star, conjTranspose_eq_inv N]
      _ = Matrix.trace (∑ i ∈ s, ∑ j ∈ s, ((c i : ℂ) * (conj (c j) : ℂ)) • (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ * ((j : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
        simp [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_assoc, mul_comm, mul_left_comm]
        try rw [Finset.sum_comm]
        try simp [mul_comm, mul_left_comm, mul_assoc]
      _ = ∑ i ∈ s, ∑ j ∈ s, ((c i : ℂ) * (conj (c j) : ℂ)) * Matrix.trace (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ * ((j : SU N) : Matrix (Fin N) (Fin N) ℂ)) := by
        simp [Matrix.trace_smul]
      _ = (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * fundamentalCharacter N (i⁻¹ * j)) := by
        have h_val_inv (g : SU N) : ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
          calc
            ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)ᴴ :=
              (conjTranspose_eq_inv N g).symm
            _ = star ((g : SU N) : Matrix (Fin N) (Fin N) ℂ) := rfl
            _ = ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
              have h_star_eq_inv : (star (g : SU N) : SU N) = g⁻¹ := Matrix.star_eq_inv (A := g)
              simpa using congrArg Subtype.val h_star_eq_inv
        simp [fundamentalCharacter, h_val_inv, mul_comm, mul_left_comm]
  have h_trace_nonneg : 0 ≤ Matrix.trace (((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))) :=
    h_nonneg_sq ((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N) (Fin N) ℂ)
  rw [← h_tr_eq]
  exact h_trace_nonneg

lemma PositiveDefinite.conj {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefinite (λ g => conj (φ g)) := by
  intro s c
  have h := hφ s (λ g => conj (c g))
  -- h: ∑ conj(c i) * conj(conj(c j)) * φ(i⁻¹ * j) ≥ 0
  have h_simp : (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) ≥ 0 := by
    simpa [star_star] using h
  rcases Complex.nonneg_iff.mp h_simp with ⟨h_re, h_im⟩
  have h_im_zero : (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)).im = 0 := h_im.symm
  have h_conj_eq : conj (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) =
      (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) :=
    (Complex.conj_eq_iff_im.mpr h_im_zero)
  have h_target : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * conj (φ (i⁻¹ * j))) =
      conj (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) := by
    simp [map_sum, mul_comm, mul_left_comm]
  rw [h_target, h_conj_eq]
  exact h_simp

lemma reTrace_positiveDefinite (N : ℕ) :
    PositiveDefinite (λ (g : SU N) => ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ)) := by
  have h_trace_re_eq : ∀ (g : SU N), ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ) =
      (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2 := by
    intro g
    calc
      ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ) =
        ((fundamentalCharacter N g).re : ℂ) := by simp [fundamentalCharacter]
      _ = (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2 := by
        rw [Complex.re_eq_add_conj]
  have h_scaled : PositiveDefinite (λ (g : SU N) => (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2) := by
    have h_sum : PositiveDefinite (λ g : SU N => fundamentalCharacter N g + conj (fundamentalCharacter N g)) :=
      PositiveDefinite.add (fundamentalCharacter_positiveDefinite N) (PositiveDefinite.conj (fundamentalCharacter_positiveDefinite N))
    have h_half_nonneg : (0 : ℝ) ≤ 1/2 := by norm_num
    have h_smul := PositiveDefinite.smul_nonneg h_half_nonneg h_sum
    simpa [div_eq_inv_mul, smul_eq_mul] using h_smul
  simpa [h_trace_re_eq] using h_scaled

lemma exp_reTrace_positiveDefinite (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    PositiveDefinite (λ (g : SU N) => (Real.exp (c * ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℝ)) : ℂ)) := by
  set h : SU N → ℝ := fun g => (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re
  set f : SU N → ℂ := fun g => (h g : ℂ)
  have hf : PositiveDefinite f := by
    have := reTrace_positiveDefinite N
    convert this using 1
  set S : ℕ → SU N → ℂ := fun n g =>
    ∑ k ∈ Finset.range n, ((c ^ k / k.factorial : ℝ) : ℂ) * ((f ^ k) g)
  have hS_PD : ∀ n, PositiveDefinite (S n) := by
    intro n
    induction n with
    | zero => simp [S, Finset.sum_empty]; exact PositiveDefinite.zero
    | succ n ih =>
      have hterm : PositiveDefinite (λ g => ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) := by
        apply PositiveDefinite.smul_nonneg
        · exact div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg _)
        · exact PositiveDefinite.pow hf n
      have hadd : PositiveDefinite (λ g => S n g + ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) :=
        PositiveDefinite.add ih hterm
      have heq : S (n + 1) = (λ g => S n g + ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) := by
        funext g
        simp only [S, Finset.sum_range_succ]
      rw [heq]
      exact hadd
  have hS_tendsto : ∀ g, Tendsto (fun n => S n g) atTop (nhds ((Real.exp (c * h g)) : ℂ)) := by
    intro g
    have hexp : HasSum (fun k => (c * h g) ^ k / k.factorial) (Real.exp (c * h g)) := by
      have := NormedSpace.expSeries_div_hasSum_exp (c * h g)
      rwa [← Real.exp_eq_exp_ℝ] at this
    have hT_tendsto : Tendsto (fun n => ∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial) atTop
        (nhds (Real.exp (c * h g))) := hexp.tendsto_sum_nat
    have hSeq : ∀ n, S n g = ((∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial : ℝ) : ℂ) := by
      intro n
      simp only [S, f, h, Pi.pow_apply, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
        Complex.ofReal_sum, mul_pow, mul_div_assoc, div_mul_eq_mul_div]
    rw [show (fun n => S n g) = (fun n =>
        ↑(∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial)) from by funext n; exact hSeq n]
    exact (Complex.continuous_ofReal.tendsto _).comp hT_tendsto
  exact PositiveDefinite.tendsto hS_PD hS_tendsto

end SU_N

section UnitaryRepresentation

variable {G : Type*} [Group G] {n : ℕ}

/-- A unitary representation of `G` is a group homomorphism into unitary matrices. -/
def IsUnitaryRepresentation (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ

/-- The character of a representation is the trace of the representation matrix. -/
def repCharacter (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g : G) : ℂ :=
  Matrix.trace (ρ g)

/-- For a unitary matrix `A`, the conjugate transpose equals the inverse. -/
private lemma conjTranspose_eq_inv_of_unitary
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Aᴴ = A⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  exact (Matrix.inv_eq_left_inv h).symm

/-- The character of a unitary representation is positive-definite.

This generalizes `fundamentalCharacter_positiveDefinite` from the fundamental
representation of `SU(N)` to arbitrary unitary representations of any group.

The proof: for `B = ∑ conj(c_g) • ρ(g)`, the PD sum equals `Tr(Bᴴ * B) ≥ 0`,
using that `ρ(g)ᴴ = ρ(g⁻¹)` (unitary + homomorphism). -/
lemma repCharacter_positiveDefinite
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) :
    PositiveDefinite (repCharacter ρ) := by
  intro s c
  -- Tr(Mᴴ * M) ≥ 0 for any matrix M
  have h_nonneg_sq : ∀ (M : Matrix (Fin n) (Fin n) ℂ), 0 ≤ Matrix.trace (Mᴴ * M) := by
    intro M
    have htrace : Matrix.trace (Mᴴ * M) = (∑ i : Fin n, (Mᴴ * M) i i : ℂ) := by
      simp [Matrix.trace]
    rw [htrace]
    refine Finset.sum_nonneg (λ i _ => ?_)
    have hdiag : (Mᴴ * M) i i = ∑ k : Fin n, conj (M k i) * M k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hdiag]
    refine Finset.sum_nonneg (λ k _ => ?_)
    have hnn : 0 ≤ conj (M k i) * M k i := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have hval : 0 ≤ Complex.normSq (M k i) := Complex.normSq_nonneg _
      rw [Complex.nonneg_iff]
      exact ⟨by simpa using hval, by simp⟩
    exact hnn
  -- Key: ρ(g)ᴴ = ρ(g⁻¹) for unitary representations
  have h_star_eq (g : G) : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  -- B = ∑ conj(c_g) • ρ(g)
  set B : Matrix (Fin n) (Fin n) ℂ := ∑ g ∈ s, (conj (c g) : ℂ) • (ρ g)
  -- Bᴴ = ∑ c_g • ρ(g⁻¹)
  have hB_star : Bᴴ = ∑ g ∈ s, (c g : ℂ) • (ρ g⁻¹) := by
    show (∑ g ∈ s, (conj (c g) : ℂ) • (ρ g))ᴴ = _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Matrix.conjTranspose_smul, h_star_eq g]
    simp [Complex.conj_conj]
  -- Key identity: Tr(Bᴴ * B) = ∑ c_i conj(c_j) * χ(i⁻¹ * j)
  have hBstarB : Bᴴ * B = ∑ i ∈ s, ∑ j ∈ s,
      ((c i : ℂ) * (conj (c j) : ℂ)) • (ρ (i⁻¹ * j)) := by
    rw [hB_star]
    show (∑ g ∈ s, (c g : ℂ) • (ρ g⁻¹)) * (∑ g ∈ s, (conj (c g) : ℂ) • (ρ g)) = _
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← ρ.map_mul]
  have h_tr_eq : Matrix.trace (Bᴴ * B) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * repCharacter ρ (i⁻¹ * j)) := by
    rw [hBstarB]
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [repCharacter]
  have h_trace_nonneg : 0 ≤ Matrix.trace (Bᴴ * B) := h_nonneg_sq B
  rw [← h_tr_eq]
  exact h_trace_nonneg

/-- For a unitary representation, the character satisfies `χ(g⁻¹) = conj(χ(g))`.
This follows from `ρ(g⁻¹) = ρ(g)⁻¹ = ρ(g)ᴴ` (unitary) and
`Tr(Mᴴ) = conj(Tr(M))`. -/
lemma repCharacter_inv (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G) :
    repCharacter ρ g⁻¹ = conj (repCharacter ρ g) := by
  have h_star_eq : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  rw [repCharacter, repCharacter, ← h_star_eq]
  simp [Matrix.trace, Matrix.conjTranspose_apply, Complex.star_def]

/-- The character is invariant under cyclic permutations of its argument:
`χ(g * h * k) = χ(h * k * g)`.

This is the *class-function* (conjugation-invariance) property of characters,
expressed via the cyclic invariance of the trace: `Tr(ABC) = Tr(BCA)`.
It follows from `Matrix.trace_mul_comm` applied twice.  No unitary hypothesis
is needed — this is pure trace algebra. -/
lemma repCharacter_cyclic (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g h k : G) :
    repCharacter ρ (g * h * k) = repCharacter ρ (h * k * g) := by
  simp only [repCharacter, MonoidHom.map_mul]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc]

/-- **Characters are class functions** (conjugation-invariant): `χ(g · h · g⁻¹) = χ(h)`.

This follows from `repCharacter_cyclic` (cyclic invariance of the trace) plus the
group inverse property `g⁻¹ · g = 1`. No unitary hypothesis is needed — this is
pure trace algebra.

This is the key property for the 3D Lüscher cascade (Step 3c of the roadmap):
a "local" plaquette at site `x` in direction `ν` has plaquette variable
`u_t(x) · W_ν(x) · u_t(x)⁻¹`, and since `B_p` is a sum of characters (each a
class function), `B_p(u · W · u⁻¹) = B_p(W)` — the local plaquette contributes a
CONSTANT (independent of `u_t(x)`), which factors out of the temporal-link
integral. Only NON-LOCAL plaquettes (connecting different sites) contribute to
the cascade. 0 sorries, 0 new axioms. -/
lemma repCharacter_isClassFunction (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g h : G) :
    repCharacter ρ (g * h * g⁻¹) = repCharacter ρ h := by
  rw [repCharacter_cyclic, mul_assoc, inv_mul_cancel, mul_one]

/-- For a unitary representation, the character is bounded by the dimension:
`‖χ(g)‖ ≤ n` where `n = dim(ρ)`.

This follows from `|Tr(A)| ≤ ∑ |A_jj| ≤ ∑ 1 = n` for a unitary `n×n` matrix `A`,
using `entry_norm_bound_of_unitary` (each entry of a unitary matrix has norm ≤ 1).
This bound is a key ingredient for proving integrability of the character-expansion
terms w.r.t. the finite Haar measure (needed for the Fubini exchange in step 4c). -/
lemma repCharacter_norm_le_dim (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G) :
    ‖repCharacter ρ g‖ ≤ n := by
  have hU : ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ := h_unitary g
  have h_entry : ∀ j : Fin n, ‖(ρ g) j j‖ ≤ 1 := fun j =>
    entry_norm_bound_of_unitary hU j j
  rw [repCharacter]
  simp only [Matrix.trace]
  calc ‖∑ j : Fin n, (ρ g) j j‖
      ≤ ∑ j : Fin n, ‖(ρ g) j j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => h_entry j
    _ = n := by simp

#print axioms repCharacter_norm_le_dim

/-- For a unitary representation, the matrix element at `g⁻¹` equals the
conjugate of the transposed matrix element at `g`:

    (ρ g⁻¹)_{ij} = conj((ρ g)_{ji})

This follows from `ρ(g⁻¹) = ρ(g)ᴴ` (unitary + homomorphism) and the definition
of conjugate transpose `(Mᴴ)_{ij} = conj(M_{ji})`.

This is the key relation connecting the σ reflection (inversion of time-like
interface links) to the matrix-element basis. In the L² expansion approach to
closing `transferMatrixPositivity_axiom`, the σ reflection on a time-like
interface link `g ↦ g⁻¹` transforms matrix elements as
`(ρ(σ(g)))_{ij} = conj((ρ g)_{ji})`, which is essential for evaluating the
reflection-positivity integral using Schur orthogonality. -/
lemma repMatrixElement_inv (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G)
    (i j : Fin n) :
    (ρ g⁻¹) i j = conj ((ρ g) j i) := by
  have h_star_eq : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  rw [← h_star_eq]
  simp [Matrix.conjTranspose_apply]

#print axioms repMatrixElement_inv

/-! ## Irreducible representations and character orthogonality

The Osterwalder–Seiler reflection-positivity argument requires not just that
the Boltzmann factor is positive-definite (proved modulo Peter–Weyl as
`boltzmannFactorPD`), but that the reflection-positivity integral
`∫ f(U)·f(θU)·exp(-β S_W) dμ` is non-negative.  As documented in
`docs/gap_analysis.md`, this integral is NOT the standard PD quadratic form
`∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0`; it is a single integral with the
geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`).

The Peter–Weyl character expansion of `K = exp(-β S_W)` writes
`K = ∑_λ a_λ χ_λ`, and the reflection-positivity integral becomes a sum of
terms `∑_λ a_λ · |∫ f · χ_λ|²` (using character orthogonality and the
reflection symmetry of the Haar measure).  Each term is non-negative because
`a_λ ≥ 0` and `|·|² ≥ 0`.  This is the missing step.

The infrastructure below axiomatizes the two deep theorems of compact-Lie-group
representation theory that are not in Mathlib:
1. **Irreducibility** of a unitary representation (no non-trivial invariant
   subspaces).
2. **Character orthogonality** for irreducible unitary representations of a
   compact group with normalized Haar measure: the integral of `χ_λ · conj(χ_μ)`
   is `1` if `λ = μ` (same irrep) and `0` otherwise (Schur orthogonality).

These are the ingredients needed to turn the character expansion of the
Boltzmann factor into the `|Fourier coefficient|²` decomposition of the
reflection-positivity integral.  See `docs/gap_analysis.md` for the full
analysis.
-/

/-- A unitary representation `ρ` is *irreducible* if the only invariant
subspaces (subspaces `W` with `ρ(g) W ⊆ W` for all `g`) are `{0}` and the
whole space.  This is the standard representation-theoretic notion. -/
def IsIrreducible {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (W : Submodule ℂ (Fin n → ℂ)),
    (∀ g : G, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → (W = ⊥ ∨ W = ⊤)

/-- **Axiom (Schur orthogonality for matrix elements of irreducible unitary
representations of a compact group).**

For a compact group `G` with normalized Haar measure `μ`, and irreducible
unitary representations `ρ_λ, ρ_μ` with matrix elements `(ρ_λ g)_{ij}`,
`(ρ_μ g)_{kl}`, the **Schur orthogonality relations** state:

  ∫_G (ρ_λ g)_{ij} · conj((ρ_μ g)_{kl}) dμ(g) = δ_{λμ} δ_{ik} δ_{jl} / dim(λ)

i.e. the integral is `1 / dim(λ)` if `λ = μ`, `i = k`, and `j = l`, and `0`
otherwise.

This is the **Great Orthogonality Theorem** for compact groups, a cornerstone
of the Peter–Weyl theorem.  It is not currently in Mathlib.  The axiom is
stated for a *finite* index set of irreps (the Peter–Weyl theorem gives a
countable family; for the lattice Boltzmann factor only finitely many irreps
appear in the character expansion, so a finite family suffices).

**Strengthened** (2026-08-01 session) from providing only character
orthogonality (`∫ χ_λ · conj(χ_μ) = δ_{λμ}`) to providing the full Schur
orthogonality of **matrix elements**.  The character-orthogonality version is
the `i = j`, `k = l` special case (the diagonal matrix elements, whose sum is
the character/trace).  The stronger matrix-element version is needed for the
L² expansion approach to closing `transferMatrixPositivity_axiom`: the test
function `f` produces arbitrary (non-class) functions of the interface links,
which must be expanded in the matrix-element basis (not just the character
basis) and evaluated using Schur orthogonality of matrix elements.  See
`docs/transfer_matrix_positivity_design.md` §5a for the full analysis.

The axiom is stated as a conjunction of three parts:
* **Integrability** of all matrix-element products (needed for the
  sum-integral exchange in `character_orthogonality_from_schur`).
* **Diagonal** (same irrep `λ = μ`): the matrix elements of a single irrep
  are orthogonal, with `∫ (ρ_λ g)_{ij} · conj((ρ_λ g)_{kl}) dμ = δ_{ik} δ_{jl} / dim(λ)`.
* **Off-diagonal** (distinct irreps `λ ≠ μ`): matrix elements of distinct
  irreps are orthogonal, with `∫ (ρ_λ g)_{ij} · conj((ρ_μ g)_{kl}) dμ = 0`.

The two-part diagonal/off-diagonal formulation avoids dependent-type issues:
in the diagonal case all indices share the type `Fin (dims r)`, and in the
off-diagonal case the result is `0` regardless of the (different-typed)
indices.  The hypothesis `hDims : ∀ i, 0 < dims i` ensures the representations
are non-degenerate (positive dimension), which is needed for
`dims r * (1 / dims r) = 1` in the character-orthogonality derivation. -/
axiom characterOrthogonality {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i)) :
    -- Integrability of all matrix-element products
    (∀ (r s : ι) (i : Fin (dims r)) (j : Fin (dims r)) (k : Fin (dims s)) (l : Fin (dims s)),
      Integrable (fun g => (ρ r g) i j * conj ((ρ s g) k l)) μ) ∧
    -- Schur orthogonality of matrix elements (diagonal: same irrep)
    (∀ (r : ι) (i j k l : Fin (dims r)),
      ∫ g, (ρ r g) i j * conj ((ρ r g) k l) ∂μ =
        if i = k ∧ j = l then (1 / dims r : ℂ) else 0) ∧
    -- Schur orthogonality of matrix elements (off-diagonal: distinct irreps)
    (∀ (r s : ι) (i j : Fin (dims r)) (k l : Fin (dims s)),
      r ≠ s →
      ∫ g, (ρ r g) i j * conj ((ρ s g) k l) ∂μ = 0)

/-- **Character orthogonality from Schur orthogonality of matrix elements.**

The character `χ_r(g) = Tr(ρ_r(g)) = ∑_a (ρ_r g)_{aa}` is the trace (sum of
diagonal matrix elements).  Schur orthogonality of matrix elements implies
character orthogonality:

  ∫ χ_r(g) · conj(χ_s(g)) dμ = ∑_{a,b} ∫ (ρ_r g)_{aa} · conj((ρ_s g)_{bb}) dμ

For `r = s`: each term is `1/dim(r)` if `a = b`, `0` otherwise; the sum is
`dim(r) · (1/dim(r)) = 1`.  For `r ≠ s`: each term is `0`; the sum is `0`.

This lemma derives the (weaker) character-orthogonality statement — previously
an axiom in its own right — from the strengthened `characterOrthogonality`
axiom that now provides the full Schur orthogonality of matrix elements.
Verified by `#print axioms` to depend only on `propext`, `Classical.choice`,
`Quot.sound` (plus `characterOrthogonality`). -/
lemma character_orthogonality_from_schur
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (r s : ι) :
    ∫ g, repCharacter (ρ r) g * conj (repCharacter (ρ s) g) ∂μ =
      if r = s then (1 : ℂ) else 0 := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- repCharacter (ρ k) g = ∑ a, (ρ k g) a a  (trace = sum of diagonal entries)
  have hchar : ∀ (k : ι) (g : G),
      repCharacter (ρ k) g = ∑ a : Fin (dims k), (ρ k g) a a := by
    intro k g; simp [repCharacter, Matrix.trace]
  -- conj pushes through a finite sum: conj (∑ a, f a) = ∑ a, conj (f a)
  -- (since `conj = starRingEnd ℂ` and `star = starRingEnd ℂ` definitionally)
  have hconj_sum : ∀ {n : ℕ} (f : Fin n → ℂ),
      conj (∑ a, f a) = ∑ a, conj (f a) := by
    intro n f; rw [starRingEnd_apply, star_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [starRingEnd_apply]
  by_cases h : r = s
  · -- Case r = s: ∫ χ_r · conj(χ_r) dμ = 1
    subst h
    -- Expand the integrand to a double sum of matrix elements
    have hprod : ∀ (g : G),
        repCharacter (ρ r) g * conj (repCharacter (ρ r) g) =
          ∑ a : Fin (dims r), ∑ b : Fin (dims r), (ρ r g) a a * conj ((ρ r g) b b) := by
      intro g; simp only [hchar]; rw [hconj_sum, Fintype.sum_mul_sum]
    rw [show (∫ g, repCharacter (ρ r) g * conj (repCharacter (ρ r) g) ∂μ) =
          ∫ g, (∑ a : Fin (dims r), ∑ b : Fin (dims r),
            (ρ r g) a a * conj ((ρ r g) b b)) ∂μ from by
        congr 1 with g; exact hprod g]
    -- Exchange the outer sum with the integral
    have hInt_inner : ∀ (a : Fin (dims r)),
        Integrable (fun g => ∑ b : Fin (dims r), (ρ r g) a a * conj ((ρ r g) b b)) μ := by
      intro a; exact integrable_finsetSum Finset.univ (fun b _ => hInt r r a a b b)
    rw [integral_finsetSum Finset.univ (fun a _ => hInt_inner a)]
    -- Exchange the inner sum with the integral
    rw [show (∑ a : Fin (dims r), ∫ g, ∑ b : Fin (dims r),
            (ρ r g) a a * conj ((ρ r g) b b) ∂μ) =
        ∑ a : Fin (dims r), ∑ b : Fin (dims r),
          ∫ g, (ρ r g) a a * conj ((ρ r g) b b) ∂μ from by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum Finset.univ (fun b _ => hInt r r a a b b)]]
    -- Apply Schur orthogonality (diagonal case) and evaluate the sums
    simp only [hSchur_diag, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    -- Goal: ∑ a : Fin (dims r), (1 / dims r : ℂ) = 1
    have hn : (dims r : ℂ) ≠ 0 := by exact_mod_cast (hDims r).ne'
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_div_cancel₀ (1 : ℂ) hn]
  · -- Case r ≠ s: ∫ χ_r · conj(χ_s) dμ = 0
    have hprod : ∀ (g : G),
        repCharacter (ρ r) g * conj (repCharacter (ρ s) g) =
          ∑ a : Fin (dims r), ∑ b : Fin (dims s), (ρ r g) a a * conj ((ρ s g) b b) := by
      intro g; simp only [hchar]; rw [hconj_sum, Fintype.sum_mul_sum]
    rw [show (∫ g, repCharacter (ρ r) g * conj (repCharacter (ρ s) g) ∂μ) =
          ∫ g, (∑ a : Fin (dims r), ∑ b : Fin (dims s),
            (ρ r g) a a * conj ((ρ s g) b b)) ∂μ from by
        congr 1 with g; exact hprod g]
    -- Exchange the outer sum with the integral
    have hInt_inner : ∀ (a : Fin (dims r)),
        Integrable (fun g => ∑ b : Fin (dims s), (ρ r g) a a * conj ((ρ s g) b b)) μ := by
      intro a; exact integrable_finsetSum Finset.univ (fun b _ => hInt r s a a b b)
    rw [integral_finsetSum Finset.univ (fun a _ => hInt_inner a)]
    -- Exchange the inner sum with the integral
    rw [show (∑ a : Fin (dims r), ∫ g, ∑ b : Fin (dims s),
            (ρ r g) a a * conj ((ρ s g) b b) ∂μ) =
        ∑ a : Fin (dims r), ∑ b : Fin (dims s),
          ∫ g, (ρ r g) a a * conj ((ρ s g) b b) ∂μ from by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum Finset.univ (fun b _ => hInt r s a a b b)]]
    -- Apply Schur orthogonality (off-diagonal case): every term is 0
    have hzero : (∑ a : Fin (dims r), ∑ b : Fin (dims s),
        ∫ g, (ρ r g) a a * conj ((ρ s g) b b) ∂μ) = (0 : ℂ) := by
      refine Finset.sum_eq_zero (fun a _ => ?_)
      refine Finset.sum_eq_zero (fun b _ => ?_)
      exact hSchur_offdiag r s a a b b h
    rw [hzero, if_neg h]

/-- **Integral of a character equals 1 for the trivial representation, 0 otherwise.**

For a compact group `G` with probability measure `μ`, a finite family of
irreducible unitary representations `ρ_ν` of dimension `dims ν`, and a
trivial representation `triv` (with `χ_{triv}(g) = 1` for all `g`):

    ∫_G χ_γ(g) ∂μ(g) = if γ = triv then 1 else 0

This follows from `character_orthogonality_from_schur` (`∫ χ_r · conj(χ_s) = δ_{rs}`)
with `s = triv`: since `χ_{triv}(g) = 1`, we have `conj(χ_{triv}(g)) = 1`, so
`∫ χ_γ · conj(χ_{triv}) = ∫ χ_γ · 1 = ∫ χ_γ`.

This is step 5 sub-lemma 3 of the 6-step `transferMatrixPositivity_axiom` closure
plan (§8.11.40): the temporal integral `∫ χ_γ(g) dg` collapses the character sum
to terms where the temporal link carries the trivial representation. -/
lemma integral_repCharacter_eq_iff_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (triv : ι) (htriv : ∀ (g : G), repCharacter (ρ triv) g = 1)
    (r : ι) :
    ∫ g, repCharacter (ρ r) g ∂μ =
      if r = triv then (1 : ℂ) else 0 := by
  have h := character_orthogonality_from_schur μ ι dims hDims ρ hU hIrr r triv
  have hcong : ∀ g,
      repCharacter (ρ r) g = repCharacter (ρ r) g * conj (repCharacter (ρ triv) g) := by
    intro g; simp [htriv]
  exact (integral_congr_ae (ae_of_all μ hcong)).trans h

#print axioms integral_repCharacter_eq_iff_trivial

/-- **Lüscher key identity** (matrix-element level).

For irreducible unitary representations `ρ_γ, ρ_{γ'}` of a compact group `G`
with normalized Haar measure `μ`, and any `h, k : G`:

    ∫_G χ_γ(g * h) · χ_{γ'}(g⁻¹ * k) ∂μ(g) = δ_{γγ'} · (1/d_γ) · χ_γ(h * k)

This is the fundamental identity underlying the Lüscher mechanism: integrating
out a "temporal" link variable `g`, the Schur orthogonality of matrix elements
forces the representations to match (`δ_{γγ'}`), and the surviving term gives
`(1/d_γ) · χ_γ(h * k)` with a strictly positive coefficient `1/d_γ > 0`.

The proof expands both characters into matrix elements (using
`Tr(AB) = ∑_{i,j} A_{ij} B_{ji}` and the unitary property
`ρ(g⁻¹) = ρ(g)†`), exchanges the finite sums with the integral, and applies
Schur orthogonality. -/
lemma luscher_key_identity
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (γ γ' : ι) (h k : G) :
    ∫ g, repCharacter (ρ γ) (g * h) * repCharacter (ρ γ') (g⁻¹ * k) ∂μ =
      if γ = γ' then (1 / dims γ : ℂ) * repCharacter (ρ γ) (h * k) else 0 := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Helper: unitary matrix element (ρ i g⁻¹) c d = conj ((ρ i g) d c)
  have h_unitary_elem : ∀ (i : ι) (g : G) (c d : Fin (dims i)),
      (ρ i g⁻¹) c d = conj ((ρ i g) d c) := by
    intro i g c d
    have h_star : (ρ i g)ᴴ = ρ i g⁻¹ := by
      rw [conjTranspose_eq_inv_of_unitary (hU i g)]
      have hmul : ρ i g * ρ i g⁻¹ = 1 := by
        rw [← MonoidHom.map_mul, show g * g⁻¹ = 1 from by simp, MonoidHom.map_one]
      exact Matrix.inv_eq_right_inv hmul
    rw [← h_star, Matrix.conjTranspose_apply]
    simp [Complex.star_def]
  -- Helper: trace of product Tr(AB) = ∑ i j, A i j * B j i
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B
    simp [Matrix.trace, Matrix.mul_apply]
  -- Step 1: Expand χ_γ(g * h) = ∑ a b, (ρ_γ g)_{ab} (ρ_γ h)_{ba}
  have hchar_gh : ∀ (g : G),
      repCharacter (ρ γ) (g * h) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), (ρ γ g) a b * (ρ γ h) b a := by
    intro g
    rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  -- Step 2: Expand χ_{γ'}(g⁻¹ * k) = ∑ c d, conj((ρ_{γ'} g)_{dc}) (ρ_{γ'} k)_{dc}
  have hchar_ginv_k : ∀ (g : G),
      repCharacter (ρ γ') (g⁻¹ * k) =
        ∑ c : Fin (dims γ'), ∑ d : Fin (dims γ'),
          conj ((ρ γ' g) d c) * (ρ γ' k) d c := by
    intro g
    rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [h_unitary_elem γ' g c d]
  -- Step 3: Pointwise identity — product of two double sums → 4-index sum
  -- simp only [Fintype.sum_mul_sum] distributes both levels, giving order a, c, b, d
  -- with body (f a b) * (g c d) = ((ρ γ g) a b * (ρ γ h) b a) * (conj ((ρ γ' g) d c) * (ρ γ' k) d c)
  have hprod : ∀ (g : G),
      repCharacter (ρ γ) (g * h) * repCharacter (ρ γ') (g⁻¹ * k) =
        ∑ a : Fin (dims γ), ∑ c : Fin (dims γ'),
          ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
            (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) := by
    intro g
    rw [hchar_gh, hchar_ginv_k]
    simp only [Fintype.sum_mul_sum]
  -- Step 4: Rewrite the integral using the pointwise identity
  rw [show (∫ g, repCharacter (ρ γ) (g * h) * repCharacter (ρ γ') (g⁻¹ * k) ∂μ) =
        ∫ g, (∑ a : Fin (dims γ), ∑ c : Fin (dims γ'),
          ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
            (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c)) ∂μ from by
    congr 1 with g; exact hprod g]
  -- Step 5: Integrability of each 4-index term (constant × Schur-integrable product)
  have hInt_term : ∀ (a b : Fin (dims γ)) (c d : Fin (dims γ')),
      Integrable (fun g =>
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c)) μ := by
    intro a b c d
    have h_gdep : Integrable (fun g => (ρ γ g) a b * conj ((ρ γ' g) d c)) μ :=
      hInt γ γ' a b d c
    -- The full integrand is const • g_dep where const = (ρ γ h) b a * (ρ γ' k) d c
    refine (h_gdep.smul ((ρ γ h) b a * (ρ γ' k) d c)).congr ?_
    exact Filter.Eventually.of_forall (fun g => by
      simp only [Pi.smul_def, smul_eq_mul]
      ring)
  -- Step 6: Exchange sums with integral, factor constants, apply Schur orthogonality
  -- Integrability helpers for each sum level (order: a, c, b, d)
  have hInt_d : ∀ (a : Fin (dims γ)) (c : Fin (dims γ')) (b : Fin (dims γ)),
      Integrable (fun g => ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c)) μ :=
    fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
  have hInt_b : ∀ (a : Fin (dims γ)) (c : Fin (dims γ')),
      Integrable (fun g => ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c)) μ :=
    fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
  have hInt_c : ∀ (a : Fin (dims γ)),
      Integrable (fun g => ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c)) μ :=
    fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
  -- Exchange 4 sums with integral
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_c a)]
  rw [show (∑ a : Fin (dims γ), ∫ g, ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ) =
      ∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∫ g, ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum Finset.univ (fun c _ => hInt_b a c)]]
  rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∫ g, ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ) =
      ∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∫ g, ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_finsetSum Finset.univ (fun b _ => hInt_d a c b)]]
  rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∫ g, ∑ d : Fin (dims γ'),
        (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ) =
      ∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        ∫ g, (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_finsetSum Finset.univ (fun d _ => hInt_term a b c d)]]
  -- Factor constants out of each integral
  have hfactor : ∀ (a b : Fin (dims γ)) (c d : Fin (dims γ')),
      ∫ g, (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ
        = (ρ γ h) b a * (ρ γ' k) d c * ∫ g, (ρ γ g) a b * conj ((ρ γ' g) d c) ∂μ := by
    intro a b c d
    rw [show (∫ g, (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ)
          = ∫ g, ((ρ γ h) b a * (ρ γ' k) d c) • ((ρ γ g) a b * conj ((ρ γ' g) d c)) ∂μ from by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by simp only [smul_eq_mul]; ring)]
    rw [integral_smul]
    simp only [smul_eq_mul]
  -- Apply hfactor to all terms
  rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        ∫ g, (ρ γ g) a b * (ρ γ h) b a * (conj ((ρ γ' g) d c) * (ρ γ' k) d c) ∂μ) =
      ∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ h) b a * (ρ γ' k) d c * ∫ g, (ρ γ g) a b * conj ((ρ γ' g) d c) ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    exact hfactor a b c d]
  -- Split into diagonal/off-diagonal cases
  by_cases hγγ' : γ = γ'
  · -- Diagonal case: γ = γ'
    subst hγγ'
    -- Apply Schur orthogonality (diagonal)
    simp only [hSchur_diag]
    -- Simplify d-sum: picks d = a (since a = d ↔ d = a, and for d ≠ a the if is 0)
    have hd : ∀ (a b c : Fin (dims γ)),
        ∑ d : Fin (dims γ), (ρ γ h) b a * (ρ γ k) d c *
          (if a = d ∧ b = c then (1 / dims γ : ℂ) else 0)
        = (ρ γ h) b a * (ρ γ k) a c * (if b = c then (1 / dims γ : ℂ) else 0) := by
      intro a b c
      have heq : ∑ d : Fin (dims γ), (ρ γ h) b a * (ρ γ k) d c *
          (if a = d ∧ b = c then (1 / dims γ : ℂ) else 0)
        = (ρ γ h) b a * (ρ γ k) a c * (if a = a ∧ b = c then (1 / dims γ : ℂ) else 0) := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro d _ hd
          have had : ¬ (a = d) := fun h => hd h.symm
          have hneg : ¬ (a = d ∧ b = c) := fun h => had h.1
          rw [if_neg hneg]
          ring
        · intro h
          exact absurd (Finset.mem_univ a) h
      rw [heq]
      simp only [eq_self_iff_true, true_and]
    -- Apply hd to simplify the d-sum
    rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ), ∑ b : Fin (dims γ),
          ∑ d : Fin (dims γ), (ρ γ h) b a * (ρ γ k) d c *
            (if a = d ∧ b = c then (1 / dims γ : ℂ) else 0)) =
        ∑ a : Fin (dims γ), ∑ c : Fin (dims γ), ∑ b : Fin (dims γ),
          (ρ γ h) b a * (ρ γ k) a c * (if b = c then (1 / dims γ : ℂ) else 0) from by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      exact hd a b c]
    -- Simplify b-sum: picks b = c
    have hb : ∀ (a c : Fin (dims γ)),
        ∑ b : Fin (dims γ), (ρ γ h) b a * (ρ γ k) a c *
          (if b = c then (1 / dims γ : ℂ) else 0)
        = (ρ γ h) c a * (ρ γ k) a c * (1 / dims γ : ℂ) := by
      intro a c
      have heq : ∑ b : Fin (dims γ), (ρ γ h) b a * (ρ γ k) a c *
          (if b = c then (1 / dims γ : ℂ) else 0)
        = (ρ γ h) c a * (ρ γ k) a c * (if c = c then (1 / dims γ : ℂ) else 0) := by
        refine Finset.sum_eq_single c ?_ ?_
        · intro b _ hb
          have hbc : ¬ (b = c) := hb
          rw [if_neg hbc]
          ring
        · intro h
          exact absurd (Finset.mem_univ c) h
      rw [heq]
      simp only [eq_self_iff_true, if_true]
    -- Apply hb to simplify the b-sum
    rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ), ∑ b : Fin (dims γ),
          (ρ γ h) b a * (ρ γ k) a c * (if b = c then (1 / dims γ : ℂ) else 0)) =
        ∑ a : Fin (dims γ), ∑ c : Fin (dims γ),
          (ρ γ h) c a * (ρ γ k) a c * (1 / dims γ : ℂ) from by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      exact hb a c]
    -- Factor out (1 / dims γ) and recognize the trace
    rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ),
          (ρ γ h) c a * (ρ γ k) a c * (1 / dims γ : ℂ)) =
        (1 / dims γ : ℂ) * ∑ a : Fin (dims γ), ∑ c : Fin (dims γ),
          (ρ γ h) c a * (ρ γ k) a c from by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      ring]
    -- Recognize the trace: ∑ a c, (ρ γ h) c a * (ρ γ k) a c = trace (ρ γ k * ρ γ h)
    rw [show (∑ a : Fin (dims γ), ∑ c : Fin (dims γ), (ρ γ h) c a * (ρ γ k) a c) =
        ∑ a : Fin (dims γ), ∑ c : Fin (dims γ), (ρ γ k) a c * (ρ γ h) c a from by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      ring]
    rw [← htrace_mul]
    -- trace (ρ γ k * ρ γ h) = trace (ρ γ h * ρ γ k) by trace_mul_comm
    rw [Matrix.trace_mul_comm]
    -- trace (ρ γ h * ρ γ k) = repCharacter (ρ γ) (h * k) by MonoidHom.map_mul
    rw [repCharacter, ← MonoidHom.map_mul]
    simp only [eq_self_iff_true, if_true]
  · -- Off-diagonal case: γ ≠ γ'
    have hzero : (∑ a : Fin (dims γ), ∑ c : Fin (dims γ'), ∑ b : Fin (dims γ), ∑ d : Fin (dims γ'),
        (ρ γ h) b a * (ρ γ' k) d c * ∫ g, (ρ γ g) a b * conj ((ρ γ' g) d c) ∂μ) = 0 := by
      refine Finset.sum_eq_zero (fun a _ => ?_)
      refine Finset.sum_eq_zero (fun c _ => ?_)
      refine Finset.sum_eq_zero (fun b _ => ?_)
      refine Finset.sum_eq_zero (fun d _ => ?_)
      rw [hSchur_offdiag γ γ' a b d c hγγ']
      ring
    rw [hzero, if_neg hγγ']

/-- **2-site 1D Lüscher cascade (Step 3 of the Lüscher roadmap, §8.11.41).**

For irreducible unitary representations of a compact group with normalized Haar
measure, the 2-site periodic temporal plaquette integral (the minimal cascade
demonstrating the Lüscher mechanism) evaluates to:

    ∫∫ χ_{γ₀}(g₀·W₀·g₁⁻¹) · χ_{γ₁}(g₁·W₁·g₀⁻¹) dg₁ dg₀
      = δ_{γ₀γ₁} · (1/d_γ) · χ_γ(W₀·W₁)

Proof: rewrite the first character factor using the cyclic (class-function)
property `repCharacter_cyclic` to move `g₁⁻¹` to the left, commute the product,
then apply `luscher_key_identity` to the inner `g₁` integral.  The Schur
orthogonality forces `γ₁ = γ₀`, and the surviving term is
`(1/d_γ) · χ_γ((W₁·g₀⁻¹)·(g₀·W₀)) = (1/d_γ) · χ_γ(W₁·W₀)` (using
`g₀⁻¹·g₀ = 1`), which equals `(1/d_γ) · χ_γ(W₀·W₁)` by `trace_mul_comm`.
The outer `g₀` integral is then the integral of a constant over a probability
measure, which equals the constant.

The coefficient `1/d_γ > 0` is strictly positive, and `χ_γ` is positive-definite.
This is the Lüscher mechanism: the cascade of Schur orthogonality matches
representations across sites, giving non-negative coefficients.  0 sorries,
0 new axioms. -/
lemma luscher_2site_cascade
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (γ₀ γ₁ : ι) (W₀ W₁ : G) :
    ∫ g₀, ∫ g₁,
      repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) * repCharacter (ρ γ₁) (g₁ * W₁ * g₀⁻¹) ∂μ ∂μ =
      if γ₀ = γ₁ then (1 / dims γ₀ : ℂ) * repCharacter (ρ γ₀) (W₀ * W₁) else 0 := by
  -- Helper: cyclic rewrite of the first character factor
  -- χ_γ₀(g₀·W₀·g₁⁻¹) = χ_γ₀(g₁⁻¹·(g₀·W₀)) by trace cyclic invariance
  have hcyc : ∀ (g₀ g₁ : G),
      repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) = repCharacter (ρ γ₀) (g₁⁻¹ * (g₀ * W₀)) := by
    intro g₀ g₁
    rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]
  -- Helper: the inner integral (for fixed g₀), after cyclic rewrite + luscher_key_identity
  have hInner : ∀ (g₀ : G),
      ∫ g₁, repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) * repCharacter (ρ γ₁) (g₁ * W₁ * g₀⁻¹) ∂μ =
      if γ₁ = γ₀ then (1 / dims γ₁ : ℂ) * repCharacter (ρ γ₁) (W₁ * W₀) else 0 := by
    intro g₀
    -- Rewrite the integrand: cyclic + commutativity + associativity
    rw [show (∫ g₁, repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ γ₁) (g₁ * W₁ * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ γ₁) (g₁ * (W₁ * g₀⁻¹)) *
          repCharacter (ρ γ₀) (g₁⁻¹ * (g₀ * W₀)) ∂μ from by
      congr 1 with g₁
      rw [hcyc, mul_assoc]
      ring]
    -- Apply luscher_key_identity to the inner g₁ integral
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr γ₁ γ₀ (W₁ * g₀⁻¹) (g₀ * W₀)]
    -- Simplify (W₁ * g₀⁻¹) * (g₀ * W₀) = W₁ * W₀ inside the if
    by_cases h : γ₁ = γ₀
    · rw [if_pos h, if_pos h]
      rw [show (W₁ * g₀⁻¹) * (g₀ * W₀) = W₁ * W₀ from by
        have hinv : g₀⁻¹ * g₀ = 1 := inv_mul_cancel _
        calc (W₁ * g₀⁻¹) * (g₀ * W₀) = W₁ * (g₀⁻¹ * (g₀ * W₀)) := by rw [mul_assoc]
          _ = W₁ * ((g₀⁻¹ * g₀) * W₀) := by rw [← mul_assoc g₀⁻¹ g₀ W₀]
          _ = W₁ * (1 * W₀) := by rw [hinv]
          _ = W₁ * W₀ := by rw [one_mul]]
    · rw [if_neg h, if_neg h]
  -- Rewrite the outer integral using hInner
  rw [show (∫ g₀, ∫ g₁,
        repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) * repCharacter (ρ γ₁) (g₁ * W₁ * g₀⁻¹) ∂μ ∂μ) =
      ∫ g₀, if γ₁ = γ₀ then (1 / dims γ₁ : ℂ) * repCharacter (ρ γ₁) (W₁ * W₀) else 0 ∂μ from by
    congr 1 with g₀; exact hInner g₀]
  -- Split cases on γ₁ = γ₀
  by_cases h : γ₁ = γ₀
  · -- γ₁ = γ₀: the integrand is a constant (1/d_γ₁) * χ_γ₁(W₁ * W₀)
    rw [if_pos h, if_pos h.symm, h]
    -- ∫ g₀, constant ∂μ = constant (probability measure)
    have hC : ∫ g₀, (1 / dims γ₀ : ℂ) * repCharacter (ρ γ₀) (W₁ * W₀) ∂μ =
        (1 / dims γ₀ : ℂ) * repCharacter (ρ γ₀) (W₁ * W₀) := by
      haveI : IsFiniteMeasure μ := inferInstance
      simp [integral_const, IsProbabilityMeasure.measure_univ]
    rw [hC]
    -- χ_γ₀(W₁ * W₀) = χ_γ₀(W₀ * W₁) by trace_mul_comm
    rw [show repCharacter (ρ γ₀) (W₁ * W₀) = repCharacter (ρ γ₀) (W₀ * W₁) from by
      show Matrix.trace (ρ γ₀ (W₁ * W₀)) = Matrix.trace (ρ γ₀ (W₀ * W₁))
      rw [show ρ γ₀ (W₁ * W₀) = ρ γ₀ W₁ * ρ γ₀ W₀ from MonoidHom.map_mul _ _ _,
          show ρ γ₀ (W₀ * W₁) = ρ γ₀ W₀ * ρ γ₀ W₁ from MonoidHom.map_mul _ _ _,
          Matrix.trace_mul_comm]]
  · -- γ₁ ≠ γ₀: the integrand is 0
    rw [if_neg h, integral_zero, if_neg (Ne.symm h)]

#print axioms luscher_2site_cascade

/-- **3-site 1D Lüscher cascade (Step 3 of the Lüscher roadmap, §8.11.41).**

For irreducible unitary representations of a compact group with normalized Haar
measure, the 3-site periodic temporal plaquette integral (generalizing the 2-site
cascade) evaluates to:

    ∫∫∫ χ_{γ₀}(g₀·W₀·g₁⁻¹) · χ_{γ₁}(g₁·W₁·g₂⁻¹) · χ_{γ₂}(g₂·W₂·g₀⁻¹) dg₁ dg₂ dg₀
      = δ_{γ₀γ₁}·δ_{γ₁γ₂} · (1/d_γ)² · χ_γ(W₀·W₁·W₂)

Proof: integrate out g₁ first (using `luscher_key_identity` with the constant
χ_{γ₂} pulled out via `integral_const_mul`), then apply `luscher_2site_cascade`
to the remaining g₀-g₂ integral. The Schur orthogonality forces γ₁=γ₀ and γ₂=γ₀,
and the surviving coefficient is (1/d_γ)² > 0. 0 sorries, 0 new axioms. -/
lemma luscher_3site_cascade
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (γ₀ γ₁ γ₂ : ι) (W₀ W₁ W₂ : G) :
    ∫ g₀, ∫ g₂, ∫ g₁,
      repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) *
      repCharacter (ρ γ₁) (g₁ * W₁ * g₂⁻¹) *
      repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ ∂μ =
      if γ₀ = γ₁ ∧ γ₁ = γ₂ then (1 / dims γ₀ : ℂ)^2 * repCharacter (ρ γ₀) (W₀ * W₁ * W₂) else 0 := by
  -- Helper: cyclic rewrite of the first character factor
  have hcyc : ∀ (g₀ g₁ : G),
      repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) = repCharacter (ρ γ₀) (g₁⁻¹ * (g₀ * W₀)) := by
    intro g₀ g₁
    rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]
  -- Helper: the inner integral (for fixed g₀, g₂), after pulling out constant χ_γ₂
  -- and applying luscher_key_identity to the g₁ integral
  have hInner : ∀ (g₀ g₂ : G),
      ∫ g₁, repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) *
             repCharacter (ρ γ₁) (g₁ * W₁ * g₂⁻¹) *
             repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ =
        (if γ₁ = γ₀ then (1 / dims γ₁ : ℂ) * repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
        repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) := by
    intro g₀ g₂
    -- Rewrite to put the constant (χ_γ₂) on the left
    rw [show (∫ g₁, repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ γ₁) (g₁ * W₁ * g₂⁻¹) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) *
          (repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) * repCharacter (ρ γ₁) (g₁ * W₁ * g₂⁻¹)) ∂μ from by
      congr 1 with g₁; ring]
    -- Pull out the constant χ_γ₂
    rw [integral_const_mul]
    -- Rewrite the remaining integrand using hcyc + commutativity to match luscher_key_identity
    rw [show (∫ g₁, repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ γ₁) (g₁ * W₁ * g₂⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ γ₁) (g₁ * (W₁ * g₂⁻¹)) *
          repCharacter (ρ γ₀) (g₁⁻¹ * (g₀ * W₀)) ∂μ from by
      congr 1 with g₁; rw [hcyc, mul_assoc]; ring]
    -- Apply luscher_key_identity to the g₁ integral
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr γ₁ γ₀ (W₁ * g₂⁻¹) (g₀ * W₀)]
    -- Handle the if
    by_cases h : γ₁ = γ₀
    · rw [if_pos h, if_pos h]
      -- Rewrite χ_γ₁((W₁ * g₂⁻¹) * (g₀ * W₀)) = χ_γ₁(g₀ * W₀ * W₁ * g₂⁻¹) via repCharacter_cyclic
      rw [show repCharacter (ρ γ₁) ((W₁ * g₂⁻¹) * (g₀ * W₀)) =
           repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) from by
        rw [← mul_assoc (W₁ * g₂⁻¹) g₀ W₀, repCharacter_cyclic, ← mul_assoc (g₀ * W₀) W₁ g₂⁻¹]]
      ring
    · rw [if_neg h, if_neg h]
      ring
  -- Rewrite the full integral using hInner
  rw [show (∫ g₀, ∫ g₂, ∫ g₁,
        repCharacter (ρ γ₀) (g₀ * W₀ * g₁⁻¹) *
        repCharacter (ρ γ₁) (g₁ * W₁ * g₂⁻¹) *
        repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, (if γ₁ = γ₀ then (1 / dims γ₁ : ℂ) * repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
        repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ from by
    congr 1 with g₀; congr 1 with g₂; exact hInner g₀ g₂]
  -- Split cases on γ₁ = γ₀
  by_cases h : γ₁ = γ₀
  · -- γ₁ = γ₀ case
    simp only [if_pos h]
    -- Step 1: Rewrite integrand to put (1/d_γ₁) on the outside of the product
    rw [show (∫ g₀, ∫ g₂, ((1 / dims γ₁ : ℂ) * repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹)) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ) =
        ∫ g₀, ∫ g₂, (1 / dims γ₁ : ℂ) * (repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
      congr 1 with g₀; congr 1 with g₂; ring]
    -- Step 2: Pull (1/d_γ₁) out of the inner integral (over g₂)
    rw [show (∫ g₀, ∫ g₂, (1 / dims γ₁ : ℂ) * (repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ) =
        ∫ g₀, (1 / dims γ₁ : ℂ) * ∫ g₂, repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ from by
      congr 1 with g₀; rw [integral_const_mul]]
    -- Step 3: Pull (1/d_γ₁) out of the outer integral (over g₀)
    rw [integral_const_mul]
    -- Step 4: Rewrite g₀*W₀*W₁*g₂⁻¹ to g₀*(W₀*W₁)*g₂⁻¹ to match luscher_2site_cascade
    rw [show (∫ g₀, ∫ g₂, repCharacter (ρ γ₁) (g₀ * W₀ * W₁ * g₂⁻¹) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ) =
        ∫ g₀, ∫ g₂, repCharacter (ρ γ₁) (g₀ * (W₀ * W₁) * g₂⁻¹) *
          repCharacter (ρ γ₂) (g₂ * W₂ * g₀⁻¹) ∂μ ∂μ from by
      congr 1 with g₀; congr 1 with g₂; rw [mul_assoc g₀ W₀ W₁]]
    -- Step 5: Apply luscher_2site_cascade with γ₀→γ₁, γ₁→γ₂, W₀→W₀*W₁, W₁→W₂
    rw [luscher_2site_cascade μ ι dims hDims ρ hU hIrr γ₁ γ₂ (W₀ * W₁) W₂]
    -- Step 6: Substitute γ₁ = γ₀ (rewrites all γ₁ to γ₀)
    rw [h]
    -- Step 7: Simplify γ₀ = γ₀ ∧ γ₀ = γ₂ to γ₀ = γ₂
    simp only [true_and, eq_self_iff_true]
    -- Step 8: Split on γ₀ = γ₂
    by_cases h₂ : γ₀ = γ₂
    · rw [if_pos h₂, if_pos h₂]
      ring
    · rw [if_neg h₂, if_neg h₂]
      ring
  · -- γ₁ ≠ γ₀ case: integrand is 0, result is 0
    simp only [if_neg h]
    simp only [zero_mul, integral_zero]
    rw [if_neg (fun hcond => h hcond.1.symm)]

#print axioms luscher_3site_cascade

/-! ## The full 1D L-site Lüscher cascade (Step 3b of the Lüscher roadmap)

The 2-site and 3-site cascades above demonstrate the Lüscher mechanism for fixed small site
counts. Here we generalize to an arbitrary number of sites via an open-chain integral defined
recursively, and prove the cascade by induction on the chain length. -/

/-- The open-chain Lüscher cascade integral. For endpoints `a, b` and a non-empty list of
(representation, Wilson-line) pairs `links = [(γ₀,W₀), (γ₁,W₁), ...]`, this is the iterated
integral `∫∫... χ_{γ₀}(a·W₀·g₁⁻¹)·χ_{γ₁}(g₁·W₁·g₂⁻¹)·...·χ_{γₙ}(gₙ·Wₙ·b⁻¹)` where the
interior variables `g₁, ..., gₙ` are integrated out one at a time (each application of
`luscher_key_identity`). The base case (single link) has no integration. -/
noncomputable def chainIntegral
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (a b : G) : List (ι × G) → ℂ
  | [] => 0
  | [x] => repCharacter (ρ x.1) (a * x.2 * b⁻¹)
  | x :: y :: rest => ∫ g, repCharacter (ρ x.1) (a * x.2 * g⁻¹) * chainIntegral μ ι dims ρ g b (y :: rest) ∂μ

/-- Helper: all representations in a list of (rep, Wilson-line) pairs equal a given `γ₀`. -/
def allSameRep (γ₀ : ι) : List (ι × G) → Prop
  | [] => True
  | (γ, _) :: rest => γ = γ₀ ∧ allSameRep γ₀ rest

instance instDecidableAllSameRep [DecidableEq ι] (γ₀ : ι) :
    ∀ (l : List (ι × G)), Decidable (allSameRep γ₀ l)
  | [] => isTrue True.intro
  | (γ, _) :: rest => @instDecidableAnd (γ = γ₀) (allSameRep γ₀ rest)
      (inferInstance) (instDecidableAllSameRep γ₀ rest)

/-- **Full 1D L-site Lüscher cascade (Step 3b of the Lüscher roadmap, §8.11.41).**

For irreducible unitary representations of a compact group with normalized Haar measure, the
open-chain L-site Lüscher cascade evaluates to:

    chainIntegral a b [(γ₀,W₀),...,(γₙ,Wₙ)] = δ_{all γ=γ₀} · (1/d_γ)^n · χ_γ(a · (∏ W) · b⁻¹)

where `n = links.length - 1` is the number of interior integrations. The Schur orthogonality
forces all representations to match (δ conditions), and the surviving coefficient is
`(1/d_γ)^n > 0`. This generalizes `luscher_2site_cascade` and `luscher_3site_cascade` to
arbitrary chain length via Fubini iteration of `luscher_key_identity`. 0 sorries, 0 new axioms. -/
lemma chainIntegral_eq
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (a b : G) (γ₀ : ι) (W₀ : G) (rest : List (ι × G)) :
    chainIntegral μ ι dims ρ a b ((γ₀, W₀) :: rest) =
      if allSameRep γ₀ rest then
        (1 / dims γ₀ : ℂ)^rest.length * repCharacter (ρ γ₀) (a * (W₀ :: rest.map Prod.snd).prod * b⁻¹)
      else 0 := by
  classical
  revert a γ₀ W₀
  induction rest with
  | nil =>
    intro a γ₀ W₀
    have hUnfold : chainIntegral μ ι dims ρ a b [(γ₀, W₀)] = repCharacter (ρ γ₀) (a * W₀ * b⁻¹) := rfl
    rw [hUnfold]
    simp only [allSameRep, List.length_nil, List.map_nil, List.prod_cons, List.prod_nil,
      pow_zero, one_mul, mul_one, if_true]
  | cons x rest' ih =>
    obtain ⟨γ₁, W₁⟩ := x
    intro a γ₀ W₀
    have hUnfold : chainIntegral μ ι dims ρ a b ((γ₀, W₀) :: (γ₁, W₁) :: rest') =
        ∫ g, repCharacter (ρ γ₀) (a * W₀ * g⁻¹) * chainIntegral μ ι dims ρ g b ((γ₁, W₁) :: rest') ∂μ := rfl
    rw [hUnfold]
    by_cases h : allSameRep γ₁ rest'
    · -- True case: inner chainIntegral = (1/d_γ₁)^rest'.length * χ_γ₁(...)
      have hIH : ∀ (g : G), chainIntegral μ ι dims ρ g b ((γ₁, W₁) :: rest') =
          (1 / dims γ₁ : ℂ)^rest'.length *
          repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) := by
        intro g; rw [ih g γ₁ W₁]; simp only [if_pos h]
      simp only [hIH]
      -- Pull constant out of integral
      have hcong : ∫ g, repCharacter (ρ γ₀) (a * W₀ * g⁻¹) *
            ((1 / dims γ₁ : ℂ)^rest'.length * repCharacter (ρ γ₁)
              (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹)) ∂μ =
          ∫ g, (1 / dims γ₁ : ℂ)^rest'.length *
            (repCharacter (ρ γ₀) (a * W₀ * g⁻¹) *
             repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by ring)
      rw [hcong, integral_const_mul]
      -- Cyclic rewrite + rearrange to match luscher_key_identity
      have hcyc : ∀ (g : G),
          repCharacter (ρ γ₀) (a * W₀ * g⁻¹) = repCharacter (ρ γ₀) (g⁻¹ * (a * W₀)) := by
        intro g; rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]
      have h2 : ∫ g, repCharacter (ρ γ₀) (a * W₀ * g⁻¹) *
            repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) ∂μ =
          ∫ g, repCharacter (ρ γ₁) (g * ((W₁ :: rest'.map Prod.snd).prod * b⁻¹)) *
            repCharacter (ρ γ₀) (g⁻¹ * (a * W₀)) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro g
        change repCharacter (ρ γ₀) (a * W₀ * g⁻¹) * repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) =
          repCharacter (ρ γ₁) (g * ((W₁ :: rest'.map Prod.snd).prod * b⁻¹)) * repCharacter (ρ γ₀) (g⁻¹ * (a * W₀))
        rw [hcyc g]
        have hg : g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹ =
            g * ((W₁ :: rest'.map Prod.snd).prod * b⁻¹) := mul_assoc _ _ _
        rw [hg]
        ring
      rw [h2]
      rw [luscher_key_identity μ ι dims hDims ρ hU hIrr γ₁ γ₀
          ((W₁ :: rest'.map Prod.snd).prod * b⁻¹) (a * W₀)]
      by_cases hγ : γ₁ = γ₀
      · -- γ₁ = γ₀
        simp only [if_pos hγ]
        rw [show repCharacter (ρ γ₁) (((W₁ :: rest'.map Prod.snd).prod * b⁻¹) * (a * W₀)) =
            repCharacter (ρ γ₁) (a * W₀ * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) from by
          rw [← mul_assoc, repCharacter_cyclic, ← mul_assoc]]
        have hRHS : allSameRep γ₀ ((γ₁, W₁) :: rest') := by
          rw [allSameRep]; refine ⟨hγ, ?_⟩; rw [← hγ]; exact h
        simp only [hRHS, if_true]
        rw [hγ]
        rw [show ((γ₀, W₁) :: rest').length = rest'.length + 1 from rfl]
        rw [show (W₀ :: ((γ₀, W₁) :: rest').map Prod.snd).prod =
            W₀ * (W₁ :: rest'.map Prod.snd).prod from by
          rw [List.map_cons, List.prod_cons]]
        rw [pow_add, pow_one]
        rw [show a * (W₀ * (W₁ :: rest'.map Prod.snd).prod) * b⁻¹ =
            a * W₀ * (W₁ :: rest'.map Prod.snd).prod * b⁻¹ from by ac_rfl]
        ring
      · -- γ₁ ≠ γ₀
        simp only [if_neg hγ, mul_zero]
        have hRHS : ¬allSameRep γ₀ ((γ₁, W₁) :: rest') := by
          rw [allSameRep]; exact fun hcond => hγ hcond.1
        simp only [if_neg hRHS]
    · -- False case: inner chainIntegral = 0
      have hIH : ∀ (g : G), chainIntegral μ ι dims ρ g b ((γ₁, W₁) :: rest') = 0 := by
        intro g; rw [ih g γ₁ W₁]; simp only [if_neg h]
      simp only [hIH, mul_zero, integral_zero]
      have hRHS : ¬allSameRep γ₀ ((γ₁, W₁) :: rest') := by
        rw [allSameRep]
        intro hcond
        exact h (hcond.1 ▸ hcond.2)
      simp only [if_neg hRHS]

#print axioms chainIntegral_eq

/-- **2-site 2D Lüscher cascade at the character level (Step 3c of the Lüscher roadmap,
§8.11.42).**

For irreducible unitary representations of a compact group with normalized Haar
measure, the 2-site 2D cascade integral — where the two plaquettes at each site
share the same `W` factor (simplification) — evaluates to:

    ∫∫ [χ_{s₁}(g₀·W·g₁⁻¹) · χ_{s₂}(g₀·W·g₁⁻¹)] ·
        [χ_{t₁}(g₁·V·g₀⁻¹) · χ_{t₂}(g₁·V·g₀⁻¹)] dμ(g₁) dμ(g₀)
      = ∑_ν cg s₁ s₂ ν · cg t₁ t₂ ν · (1/d_ν) · χ_ν(W·V)

The proof uses the Clebsch-Gordan character decomposition `hcg_decomp` to rewrite
each product of two characters as a sum over irreps, then exchanges the finite sums
with the inner `g₁` integral (justified by integrability from Schur orthogonality
of matrix elements), and applies `luscher_key_identity` to each inner integral.
The Schur orthogonality forces `ν' = ν`, and the surviving coefficient is
`cg s₁ s₂ ν · cg t₁ t₂ ν · (1/d_ν)`. The `χ_ν(V·W)` from `luscher_key_identity`
is converted to `χ_ν(W·V)` by `trace_mul_comm`.

This is the character-level 2-site 2D cascade: it uses the CG decomposition
`hcg_decomp` (which gives non-negative CG coefficients `cg s t ν ≥ 0` in the
Peter-Weyl axiom) combined with `luscher_key_identity`. The result is a sum of
terms `cg s₁ s₂ ν · cg t₁ t₂ ν · (1/d_ν) · χ_ν(W·V)`, each with a non-negative
coefficient `cg s₁ s₂ ν · cg t₁ t₂ ν ≥ 0` (product of non-negative CG coefficients)
times the positive-definite character `χ_ν`. 0 sorries, 0 new axioms. -/
lemma luscher_2site_2D_cascade_charlevel
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cg : ι → ι → ι → ℝ)
    (hcg_decomp : ∀ s t (g : G),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ ν : ι, (cg s t ν : ℂ) * repCharacter (ρ ν) g)
    (s₁ s₂ t₁ t₂ : ι) (W V : G) :
    ∫ g₀, ∫ g₁,
      (repCharacter (ρ s₁) (g₀ * W * g₁⁻¹) * repCharacter (ρ s₂) (g₀ * W * g₁⁻¹)) *
      (repCharacter (ρ t₁) (g₁ * V * g₀⁻¹) * repCharacter (ρ t₂) (g₁ * V * g₀⁻¹)) ∂μ ∂μ =
    ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
      ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  -- Integrability of character product w.r.t. g₁ (for fixed g₀, ν, ν')
  have hInt_char : ∀ (g₀ : G) (ν ν' : ι),
      Integrable (fun g₁ =>
        repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹)) μ := by
    intro g₀ ν ν'
    have hchar_ν : ∀ (g₁ : G),
        repCharacter (ρ ν) (g₀ * W * g₁⁻¹) =
        ∑ a : Fin (dims ν), ∑ b : Fin (dims ν),
          (ρ ν (g₀ * W)) a b * conj ((ρ ν g₁) a b) := by
      intro g₁
      rw [repCharacter, MonoidHom.map_mul, htrace_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [repMatrixElement_inv (ρ ν) (hU ν) g₁ b a]
    have hchar_ν' : ∀ (g₁ : G),
        repCharacter (ρ ν') (g₁ * V * g₀⁻¹) =
        ∑ c : Fin (dims ν'), ∑ d : Fin (dims ν'),
          (ρ ν' g₁) c d * (ρ ν' (V * g₀⁻¹)) d c := by
      intro g₁
      rw [show g₁ * V * g₀⁻¹ = g₁ * (V * g₀⁻¹) from mul_assoc _ _ _,
          repCharacter, MonoidHom.map_mul, htrace_mul]
    have hprod_expand : ∀ (g₁ : G),
        repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹) =
        ∑ a : Fin (dims ν), ∑ c : Fin (dims ν'),
          ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
            (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
            ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b)) := by
      intro g₁
      rw [hchar_ν, hchar_ν']
      simp only [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      ring
    have hInt_term : ∀ (a : Fin (dims ν)) (b : Fin (dims ν))
        (c : Fin (dims ν')) (d : Fin (dims ν')),
        Integrable (fun g₁ =>
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ := by
      intro a b c d
      have h_gdep : Integrable (fun g₁ => (ρ ν' g₁) c d * conj ((ρ ν g₁) a b)) μ :=
        hInt ν' ν c d a b
      exact (h_gdep.smul ((ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c)).congr
        (Filter.Eventually.of_forall (fun g₁ => by
          simp only [Pi.smul_def, smul_eq_mul]))
    have hInt_d : ∀ (a : Fin (dims ν)) (c : Fin (dims ν')) (b : Fin (dims ν)),
        Integrable (fun g₁ => ∑ d : Fin (dims ν'),
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
    have hInt_b : ∀ (a : Fin (dims ν)) (c : Fin (dims ν')),
        Integrable (fun g₁ => ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
    have hInt_c : ∀ (a : Fin (dims ν)),
        Integrable (fun g₁ => ∑ c : Fin (dims ν'), ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
    have hInt_sum : Integrable (fun g₁ =>
        ∑ a : Fin (dims ν), ∑ c : Fin (dims ν'),
          ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
            (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
            ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      integrable_finsetSum Finset.univ (fun a _ => hInt_c a)
    exact hInt_sum.congr (Filter.Eventually.of_forall (fun g₁ => (hprod_expand g₁).symm))
  -- Integrability of each (ν, ν') term w.r.t. g₁
  have hInt_term_νν' : ∀ (g₀ : G) (ν ν' : ι),
      Integrable (fun g₁ =>
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) μ := by
    intro g₀ ν ν'
    exact ((hInt_char g₀ ν ν').smul ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ))).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_ν' : ∀ (g₀ : G) (ν : ι),
      Integrable (fun g₁ =>
        ∑ ν' : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) μ :=
    fun g₀ ν => integrable_finsetSum Finset.univ (fun ν' _ => hInt_term_νν' g₀ ν ν')
  -- Pointwise identity: integrand = ∑ ν ∑ ν', cg·cg'·χ_ν·χ_{ν'}
  have hprod : ∀ (g₀ g₁ : G),
      (repCharacter (ρ s₁) (g₀ * W * g₁⁻¹) * repCharacter (ρ s₂) (g₀ * W * g₁⁻¹)) *
      (repCharacter (ρ t₁) (g₁ * V * g₀⁻¹) * repCharacter (ρ t₂) (g₁ * V * g₀⁻¹)) =
      ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹)) := by
    intro g₀ g₁
    rw [hcg_decomp s₁ s₂ (g₀ * W * g₁⁻¹), hcg_decomp t₁ t₂ (g₁ * V * g₀⁻¹)]
    simp only [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ν' _
    ring
  -- Inner integral via luscher_key_identity
  have hInner : ∀ (g₀ : G) (ν ν' : ι),
      ∫ g₁, repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹) ∂μ =
      if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0 := by
    intro g₀ ν ν'
    rw [show (∫ g₁, repCharacter (ρ ν) (g₀ * W * g₁⁻¹) *
          repCharacter (ρ ν') (g₁ * V * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ ν') (g₁ * (V * g₀⁻¹)) *
          repCharacter (ρ ν) (g₁⁻¹ * (g₀ * W)) ∂μ from by
      congr 1 with g₁
      rw [show repCharacter (ρ ν) (g₀ * W * g₁⁻¹) = repCharacter (ρ ν) (g₁⁻¹ * (g₀ * W)) from by
        rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]]
      rw [show repCharacter (ρ ν') (g₁ * V * g₀⁻¹) = repCharacter (ρ ν') (g₁ * (V * g₀⁻¹)) from by
        rw [mul_assoc]]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr ν' ν (V * g₀⁻¹) (g₀ * W)]
    by_cases h : ν' = ν
    · rw [if_pos h, if_pos h]
      rw [show (V * g₀⁻¹) * (g₀ * W) = V * W from by
        have hinv : g₀⁻¹ * g₀ = 1 := inv_mul_cancel _
        calc (V * g₀⁻¹) * (g₀ * W) = V * (g₀⁻¹ * (g₀ * W)) := by rw [mul_assoc]
          _ = V * ((g₀⁻¹ * g₀) * W) := by rw [← mul_assoc g₀⁻¹ g₀ W]
          _ = V * (1 * W) := by rw [hinv]
          _ = V * W := by rw [one_mul]]
    · rw [if_neg h, if_neg h]
  -- Inner integral with constants pulled out
  have hInner_full : ∀ (g₀ : G) (ν ν' : ι),
      ∫ g₁, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹)) ∂μ =
      (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
      (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) := by
    intro g₀ ν ν'
    rw [integral_const_mul, hInner g₀ ν ν']
  -- Rewrite integrand using hprod
  rw [show (∫ g₀, ∫ g₁,
        (repCharacter (ρ s₁) (g₀ * W * g₁⁻¹) * repCharacter (ρ s₂) (g₀ * W * g₁⁻¹)) *
        (repCharacter (ρ t₁) (g₁ * V * g₀⁻¹) * repCharacter (ρ t₂) (g₁ * V * g₀⁻¹)) ∂μ ∂μ) =
      ∫ g₀, ∫ g₁,
        (∑ ν : ι, ∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀; congr 1 with g₁; exact hprod g₀ g₁]
  -- Exchange ν sum with g₁ integral
  rw [show (∫ g₀, ∫ g₁,
        (∑ ν : ι, ∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ ν : ι, ∫ g₁,
        (∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    rw [integral_finsetSum Finset.univ (fun ν _ => hInt_ν' g₀ ν)]]
  -- Exchange ν' sum with g₁ integral
  rw [show (∫ g₀, ∑ ν : ι, ∫ g₁,
        (∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ ν : ι, ∑ ν' : ι, ∫ g₁,
        ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro ν _
    rw [integral_finsetSum Finset.univ (fun ν' _ => hInt_term_νν' g₀ ν ν')]]
  -- Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∑ ν : ι, ∑ ν' : ι, ∫ g₁,
        ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ν' _
    exact hInner_full g₀ ν ν']
  -- Pull constant out of g₀ integral (integrand is independent of g₀)
  rw [show (∫ g₀, ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) ∂μ) =
      ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) from by
    haveI : IsFiniteMeasure μ := inferInstance
    simp [integral_const, IsProbabilityMeasure.measure_univ]]
  -- Collapse the if and simplify
  rw [show (∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0)) =
      ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
        ((1 / dims ν : ℂ) * repCharacter (ρ ν) (V * W)) from by
    apply Finset.sum_congr rfl
    intro ν _
    have key : ∑ ν' : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) =
      (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
        (if ν = ν then (1 / dims ν : ℂ) * repCharacter (ρ ν) (V * W) else 0) := by
      refine Finset.sum_eq_single ν ?_ ?_
      · intro ν' _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ ν) h
    rw [key, if_pos rfl]]
  -- χ_ν(V*W) = χ_ν(W*V) by trace_mul_comm
  apply Finset.sum_congr rfl
  intro ν _
  rw [show repCharacter (ρ ν) (V * W) = repCharacter (ρ ν) (W * V) from by
    show Matrix.trace (ρ ν (V * W)) = Matrix.trace (ρ ν (W * V))
    rw [show ρ ν (V * W) = ρ ν V * ρ ν W from MonoidHom.map_mul _ _ _,
        show ρ ν (W * V) = ρ ν W * ρ ν V from MonoidHom.map_mul _ _ _,
        Matrix.trace_mul_comm]]

#print axioms luscher_2site_2D_cascade_charlevel

/-- **Integrability of a character product** `χ_s(A · g⁻¹) · χ_t(g · B)` w.r.t. `g`.

For irreducible unitary representations of a compact group with normalized Haar
measure, the product of two characters `χ_s(A · g⁻¹) · χ_t(g · B)` is integrable
w.r.t. `g` for any fixed `A, B ∈ G` and representations `s, t`. This follows by
expanding both characters into matrix elements (using unitarity `ρ(g⁻¹) = ρ(g)†`
via `repMatrixElement_inv`), distributing the product via `Fintype.sum_mul_sum`,
and applying the matrix-element integrability from `characterOrthogonality`.

This is the standalone generalization of the local `hInt_char` hypothesis in
`luscher_2site_cascade_coeff`, extracted for reuse in the 3-site cascade. -/
lemma char_product_integrable
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (s t : ι) (A B : G) :
    Integrable (fun g =>
      repCharacter (ρ s) (A * g⁻¹) * repCharacter (ρ t) (g * B)) μ := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  have hchar_s : ∀ (g : G),
      repCharacter (ρ s) (A * g⁻¹) =
      ∑ a : Fin (dims s), ∑ b : Fin (dims s),
        (ρ s A) a b * conj ((ρ s g) a b) := by
    intro g
    rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [repMatrixElement_inv (ρ s) (hU s) g b a]
  have hchar_t : ∀ (g : G),
      repCharacter (ρ t) (g * B) =
      ∑ c : Fin (dims t), ∑ d : Fin (dims t),
        (ρ t g) c d * (ρ t B) d c := by
    intro g
    rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  have hprod_expand : ∀ (g : G),
      repCharacter (ρ s) (A * g⁻¹) * repCharacter (ρ t) (g * B) =
      ∑ a : Fin (dims s), ∑ c : Fin (dims t),
        ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s A) a b * (ρ t B) d c *
          ((ρ t g) c d * conj ((ρ s g) a b)) := by
    intro g
    rw [hchar_s, hchar_t]
    simp only [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hInt_term : ∀ (a : Fin (dims s)) (b : Fin (dims s))
      (c : Fin (dims t)) (d : Fin (dims t)),
      Integrable (fun g =>
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ := by
    intro a b c d
    have h_gdep : Integrable (fun g => (ρ t g) c d * conj ((ρ s g) a b)) μ :=
      hInt t s c d a b
    exact (h_gdep.smul ((ρ s A) a b * (ρ t B) d c)).congr
      (Filter.Eventually.of_forall (fun g => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_d : ∀ (a : Fin (dims s)) (c : Fin (dims t)) (b : Fin (dims s)),
      Integrable (fun g => ∑ d : Fin (dims t),
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
  have hInt_b : ∀ (a : Fin (dims s)) (c : Fin (dims t)),
      Integrable (fun g => ∑ b : Fin (dims s), ∑ d : Fin (dims t),
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
  have hInt_c : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ c : Fin (dims t), ∑ b : Fin (dims s), ∑ d : Fin (dims t),
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
  have hInt_sum : Integrable (fun g =>
      ∑ a : Fin (dims s), ∑ c : Fin (dims t),
        ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s A) a b * (ρ t B) d c *
          ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    integrable_finsetSum Finset.univ (fun a _ => hInt_c a)
  exact hInt_sum.congr (Filter.Eventually.of_forall (fun g => (hprod_expand g).symm))

#print axioms char_product_integrable
/-! ## Step 3 bridge lemma: plaquette product expansion → Lüscher cascade

The following lemma is the key bridge connecting the plaquette product expansion
(step 2: `∑_{s,t} F(s,t) · χ_s(·) · χ_t(·)` with `F(s,t) ≥ 0`) to the Lüscher
cascade (step 3: integrating out temporal links `g₀, g₁`).  It takes arbitrary
non-negative coefficients `F : ι → ι → ℝ` and evaluates the 2-site cascade:

    ∫∫ ∑_{s,t} F(s,t) · χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹) dg₁ dg₀
      = ∑_s F(s,s) · (1/d_s) · χ_s(W·V)

The resulting kernel `K(W,V) = ∑_s (F(s,s) · (1/d_s)) · χ_s(W·V)` has non-negative
coefficients `F(s,s) · (1/d_s) ≥ 0` (since `F(s,s) ≥ 0` and `1/d_s > 0`), matching
`character_kernel_integral_nonneg` (step 4).

The proof follows the same pattern as `luscher_2site_2D_cascade_charlevel` but is
simpler: no Clebsch–Gordan decomposition is needed since the integrand is already
a sum of single-character products.  The key steps are:
(1) establish integrability of each character product w.r.t. `g₁` using
    `characterOrthogonality` (matrix-element integrability) and the unitary
    expansion `ρ(g₁⁻¹) = ρ(g₁)†`;
(2) exchange the finite sums with the inner `g₁` integral via `integral_finsetSum`;
(3) apply `luscher_key_identity` to each `(s,t)` term (Schur orthogonality forces
    `s = t`);
(4) integrate out `g₀` (the result is constant, so the integral equals the
    constant over a probability measure);
(5) collapse the `if t = s` to keep only the diagonal `t = s` terms.
See `docs/transfer_matrix_positivity_design.md` §8.11.47. -/

/-- **2-site Lüscher cascade with arbitrary non-negative coefficients (Step 3 bridge).**

For irreducible unitary representations of a compact group with normalized Haar
measure, and arbitrary non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`,
the 2-site cascade with summed character products evaluates to:

    ∫∫ ∑_{s,t} F(s,t) · χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹) dg₁ dg₀
      = ∑_s F(s,s) · (1/d_s) · χ_s(W·V)

The coefficient `F(s,s) · (1/d_s) ≥ 0` (since `F(s,s) ≥ 0` and `1/d_s > 0`),
so the resulting kernel matches `character_kernel_integral_nonneg`.  0 sorries,
0 new axioms. -/
lemma luscher_2site_cascade_coeff
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ℝ) (hF : ∀ s t, 0 ≤ F s t)
    (W V : G) :
    ∫ g₀, ∫ g₁,
      ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ =
    ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ) * repCharacter (ρ s) (W * V)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  -- Integrability of character product w.r.t. g₁ (for fixed g₀, s, t)
  have hInt_char : ∀ (g₀ : G) (s t : ι),
      Integrable (fun g₁ =>
        repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) μ := by
    intro g₀ s t
    have hchar_s : ∀ (g₁ : G),
        repCharacter (ρ s) (g₀ * W * g₁⁻¹) =
        ∑ a : Fin (dims s), ∑ b : Fin (dims s),
          (ρ s (g₀ * W)) a b * conj ((ρ s g₁) a b) := by
      intro g₁
      rw [repCharacter, MonoidHom.map_mul, htrace_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [repMatrixElement_inv (ρ s) (hU s) g₁ b a]
    have hchar_t : ∀ (g₁ : G),
        repCharacter (ρ t) (g₁ * V * g₀⁻¹) =
        ∑ c : Fin (dims t), ∑ d : Fin (dims t),
          (ρ t g₁) c d * (ρ t (V * g₀⁻¹)) d c := by
      intro g₁
      rw [show g₁ * V * g₀⁻¹ = g₁ * (V * g₀⁻¹) from mul_assoc _ _ _,
          repCharacter, MonoidHom.map_mul, htrace_mul]
    have hprod_expand : ∀ (g₁ : G),
        repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹) =
        ∑ a : Fin (dims s), ∑ c : Fin (dims t),
          ∑ b : Fin (dims s), ∑ d : Fin (dims t),
            (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
            ((ρ t g₁) c d * conj ((ρ s g₁) a b)) := by
      intro g₁
      rw [hchar_s, hchar_t]
      simp only [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      ring
    have hInt_term : ∀ (a : Fin (dims s)) (b : Fin (dims s))
        (c : Fin (dims t)) (d : Fin (dims t)),
        Integrable (fun g₁ =>
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ := by
      intro a b c d
      have h_gdep : Integrable (fun g₁ => (ρ t g₁) c d * conj ((ρ s g₁) a b)) μ :=
        hInt t s c d a b
      exact (h_gdep.smul ((ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c)).congr
        (Filter.Eventually.of_forall (fun g₁ => by
          simp only [Pi.smul_def, smul_eq_mul]))
    have hInt_d : ∀ (a : Fin (dims s)) (c : Fin (dims t)) (b : Fin (dims s)),
        Integrable (fun g₁ => ∑ d : Fin (dims t),
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
    have hInt_b : ∀ (a : Fin (dims s)) (c : Fin (dims t)),
        Integrable (fun g₁ => ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
    have hInt_c : ∀ (a : Fin (dims s)),
        Integrable (fun g₁ => ∑ c : Fin (dims t), ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
    have hInt_sum : Integrable (fun g₁ =>
        ∑ a : Fin (dims s), ∑ c : Fin (dims t),
          ∑ b : Fin (dims s), ∑ d : Fin (dims t),
            (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
            ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      integrable_finsetSum Finset.univ (fun a _ => hInt_c a)
    exact hInt_sum.congr (Filter.Eventually.of_forall (fun g₁ => (hprod_expand g₁).symm))
  -- Integrability of each (s, t) term w.r.t. g₁
  have hInt_term_st : ∀ (g₀ : G) (s t : ι),
      Integrable (fun g₁ =>
        (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) μ := by
    intro g₀ s t
    exact ((hInt_char g₀ s t).smul (F s t : ℂ)).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_t : ∀ (g₀ : G) (s : ι),
      Integrable (fun g₁ =>
        ∑ t : ι, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) μ :=
    fun g₀ s => integrable_finsetSum Finset.univ (fun t _ => hInt_term_st g₀ s t)
  -- Inner integral via luscher_key_identity
  have hInner : ∀ (g₀ : G) (s t : ι),
      ∫ g₁, repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹) ∂μ =
      if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0 := by
    intro g₀ s t
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * W * g₁⁻¹) *
          repCharacter (ρ t) (g₁ * V * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ t) (g₁ * (V * g₀⁻¹)) *
          repCharacter (ρ s) (g₁⁻¹ * (g₀ * W)) ∂μ from by
      congr 1 with g₁
      rw [show repCharacter (ρ s) (g₀ * W * g₁⁻¹) = repCharacter (ρ s) (g₁⁻¹ * (g₀ * W)) from by
        rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]]
      rw [show repCharacter (ρ t) (g₁ * V * g₀⁻¹) = repCharacter (ρ t) (g₁ * (V * g₀⁻¹)) from by
        rw [mul_assoc]]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr t s (V * g₀⁻¹) (g₀ * W)]
    by_cases h : t = s
    · rw [if_pos h, if_pos h]
      rw [show (V * g₀⁻¹) * (g₀ * W) = V * W from by
        have hinv : g₀⁻¹ * g₀ = 1 := inv_mul_cancel _
        calc (V * g₀⁻¹) * (g₀ * W) = V * (g₀⁻¹ * (g₀ * W)) := by rw [mul_assoc]
          _ = V * ((g₀⁻¹ * g₀) * W) := by rw [← mul_assoc g₀⁻¹ g₀ W]
          _ = V * (1 * W) := by rw [hinv]
          _ = V * W := by rw [one_mul]]
    · rw [if_neg h, if_neg h]
  -- Inner integral with constants pulled out
  have hInner_full : ∀ (g₀ : G) (s t : ι),
      ∫ g₁, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ =
      (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) := by
    intro g₀ s t
    rw [integral_const_mul, hInner g₀ s t]
  -- Exchange s sum with g₁ integral
  rw [show (∫ g₀, ∫ g₁,
        (∑ s : ι, ∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∫ g₁,
        (∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    rw [integral_finsetSum Finset.univ (fun s _ => hInt_t g₀ s)]]
  -- Exchange t sum with g₁ integral
  rw [show (∫ g₀, ∑ s : ι, ∫ g₁,
        (∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∑ t : ι, ∫ g₁,
        ((F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum Finset.univ (fun t _ => hInt_term_st g₀ s t)]]
  -- Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∑ s : ι, ∑ t : ι, ∫ g₁,
        ((F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    exact hInner_full g₀ s t]
  -- Pull constant out of g₀ integral (integrand is independent of g₀)
  rw [show (∫ g₀, ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) ∂μ) =
      ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) from by
    haveI : IsFiniteMeasure μ := inferInstance
    simp [integral_const, IsProbabilityMeasure.measure_univ]]
  -- Collapse the if and simplify
  rw [show (∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0)) =
      ∑ s : ι, (F s s : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (V * W)) from by
    apply Finset.sum_congr rfl
    intro s _
    have key : ∑ t : ι, (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) =
      (F s s : ℂ) *
        (if s = s then (1 / dims s : ℂ) * repCharacter (ρ s) (V * W) else 0) := by
      refine Finset.sum_eq_single s ?_ ?_
      · intro t _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [key, if_pos rfl]]
  -- χ_s(V*W) = χ_s(W*V) by trace_mul_comm
  apply Finset.sum_congr rfl
  intro s _
  rw [show repCharacter (ρ s) (V * W) = repCharacter (ρ s) (W * V) from by
    show Matrix.trace (ρ s (V * W)) = Matrix.trace (ρ s (W * V))
    rw [show ρ s (V * W) = ρ s V * ρ s W from MonoidHom.map_mul _ _ _,
        show ρ s (W * V) = ρ s W * ρ s V from MonoidHom.map_mul _ _ _,
        Matrix.trace_mul_comm]]

#print axioms luscher_2site_cascade_coeff

/-- **3-site Lüscher cascade with arbitrary non-negative coefficients (Step 3, multi-plaquette).**

For irreducible unitary representations of a compact group with normalized Haar
measure, and arbitrary non-negative coefficients `F : ι → ι → ι → ℝ` with
`F s t u ≥ 0`, the 3-site cascade with summed character products evaluates to:

    ∫∫∫ ∑_{s,t,u} F(s,t,u) · χ_s(g₀·W₀·g₁⁻¹) · χ_t(g₁·W₁·g₂⁻¹) · χ_u(g₂·W₂·g₀⁻¹) dg₁ dg₂ dg₀
      = ∑_s F(s,s,s) · (1/d_s)² · χ_s(W₀·W₁·W₂)

The coefficient `F(s,s,s) · (1/d_s)² ≥ 0` (since `F(s,s,s) ≥ 0` and `(1/d_s)² > 0`),
so the resulting kernel matches `character_kernel_integral_nonneg`. This generalizes
`luscher_2site_cascade_coeff` to the 3-plaquette case (three plaquettes sharing three
temporal links `g₀, g₁, g₂`). 0 sorries, 0 new axioms.

The proof uses an inductive approach: (1) integrate out `g₁` via `luscher_key_identity`
(Schur orthogonality forces `t = s`), producing a 2-site cascade with coefficients
`G(s,u) = F(s,s,u) · (1/d_s) ≥ 0`; (2) apply `luscher_2site_cascade_coeff` to integrate
out `g₂` (Schur orthogonality forces `u = s`), producing the final kernel with
coefficients `F(s,s,s) · (1/d_s)² ≥ 0`. -/
lemma luscher_3site_cascade_coeff
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ι → ℝ) (hF : ∀ s t u, 0 ≤ F s t u)
    (W₀ W₁ W₂ : G) :
    ∫ g₀, ∫ g₂, ∫ g₁,
      ∑ s, ∑ t, ∑ u, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ ∂μ =
    ∑ s, (F s s s : ℂ) * ((1 / dims s : ℂ)^2 * repCharacter (ρ s) (W₀ * W₁ * W₂)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Step 1: Integrability of each (s,t,u) term w.r.t. g₁
  have hInt_stu : ∀ (g₀ g₂ : G) (s t u : ι),
      Integrable (fun g₁ =>
        (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) μ := by
    intro g₀ g₂ s t u
    have hst : Integrable (fun g₁ =>
      repCharacter (ρ s) ((g₀ * W₀) * g₁⁻¹) *
      repCharacter (ρ t) (g₁ * (W₁ * g₂⁻¹))) μ :=
      char_product_integrable μ ι dims hDims ρ hU hIrr s t (g₀ * W₀) (W₁ * g₂⁻¹)
    exact (hst.smul ((F s t u : ℂ) * repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]
        rw [show g₁ * W₁ * g₂⁻¹ = g₁ * (W₁ * g₂⁻¹) from mul_assoc g₁ W₁ g₂⁻¹]
        ring))
  have hInt_tu : ∀ (g₀ g₂ : G) (s t : ι),
      Integrable (fun g₁ =>
        ∑ u : ι, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) μ :=
    fun g₀ g₂ s t => integrable_finsetSum Finset.univ (fun u _ => hInt_stu g₀ g₂ s t u)
  have hInt_u : ∀ (g₀ g₂ : G) (s : ι),
      Integrable (fun g₁ =>
        ∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) μ :=
    fun g₀ g₂ s => integrable_finsetSum Finset.univ (fun t _ => hInt_tu g₀ g₂ s t)
  -- Step 2: Inner integral via luscher_key_identity (following luscher_3site_cascade pattern)
  have hInner : ∀ (g₀ g₂ : G) (s t u : ι),
      ∫ g₁, repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
             repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
             repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) ∂μ =
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
        repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) := by
    intro g₀ g₂ s t u
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
          repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) * repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹)) ∂μ from by
      congr 1 with g₁; ring]
    rw [integral_const_mul]
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ t) (g₁ * (W₁ * g₂⁻¹)) *
          repCharacter (ρ s) (g₁⁻¹ * (g₀ * W₀)) ∂μ from by
      congr 1 with g₁
      rw [show repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) = repCharacter (ρ s) (g₁⁻¹ * (g₀ * W₀)) from by
        rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]]
      rw [show repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) = repCharacter (ρ t) (g₁ * (W₁ * g₂⁻¹)) from by
        rw [mul_assoc]]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr t s (W₁ * g₂⁻¹) (g₀ * W₀)]
    by_cases h : t = s
    · rw [if_pos h, if_pos h]
      rw [show repCharacter (ρ t) ((W₁ * g₂⁻¹) * (g₀ * W₀)) =
            repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) from by
        rw [← mul_assoc (W₁ * g₂⁻¹) g₀ W₀, repCharacter_cyclic, ← mul_assoc (g₀ * W₀) W₁ g₂⁻¹]]
      ring
    · rw [if_neg h, if_neg h]
      ring
  have hInner_full : ∀ (g₀ g₂ : G) (s t u : ι),
      ∫ g₁, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ =
      (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) := by
    intro g₀ g₂ s t u
    rw [integral_const_mul, hInner g₀ g₂ s t u]
  -- Step 3: Exchange ∑_s with ∫ g₁
  rw [show (∫ g₀, ∫ g₂, ∫ g₁,
        (∑ s : ι, ∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∫ g₁,
        (∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    rw [integral_finsetSum Finset.univ (fun s _ => hInt_u g₀ g₂ s)]]
  -- Step 4: Exchange ∑_t with ∫ g₁
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∫ g₁,
        (∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∫ g₁,
        (∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum Finset.univ (fun t _ => hInt_tu g₀ g₂ s t)]]
  -- Step 5: Exchange ∑_u with ∫ g₁
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∫ g₁,
        (∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∫ g₁,
        ((F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum Finset.univ (fun u _ => hInt_stu g₀ g₂ s t u)]]
  -- Step 6: Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∫ g₁,
        ((F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι,
        (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    exact hInner_full g₀ g₂ s t u]
  -- Step 7: Collapse the if t = s (keep only t = s terms)
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι,
        (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ u : ι,
        (F s s u : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (g₀ * W₀ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have key : ∑ t : ι, (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) =
      (F s s u : ℂ) *
        ((if s = s then (1 / dims s : ℂ) * repCharacter (ρ s) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) := by
      refine Finset.sum_eq_single s ?_ ?_
      · intro t _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [key, if_pos rfl]]
  -- Step 8: Apply luscher_2site_cascade_coeff
  let G : ι → ι → ℝ := fun s u => F s s u / dims s
  have hG : ∀ s u, 0 ≤ G s u := fun s u => div_nonneg (hF s s u) (Nat.cast_nonneg _)
  have hG_eq : ∀ s u, (G s u : ℂ) = (F s s u : ℂ) * (1 / (dims s : ℂ)) := by
    intro s u
    rw [show G s u = F s s u / dims s from rfl]
    push_cast
    field_simp
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ u : ι,
        (F s s u : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (g₀ * W₀ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ u : ι,
        (G s u : ℂ) *
        (repCharacter (ρ s) (g₀ * (W₀ * W₁) * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro u _
    rw [hG_eq s u]
    rw [show g₀ * W₀ * W₁ * g₂⁻¹ = g₀ * (W₀ * W₁) * g₂⁻¹ from by rw [mul_assoc g₀ W₀ W₁]]
    ring]
  rw [luscher_2site_cascade_coeff μ ι dims hDims ρ hU hIrr G hG (W₀ * W₁) W₂]
  -- Step 9: Simplify to final form
  apply Finset.sum_congr rfl
  intro s _
  rw [show repCharacter (ρ s) ((W₀ * W₁) * W₂) = repCharacter (ρ s) (W₀ * W₁ * W₂) from rfl]
  rw [hG_eq s s]
  push_cast
  ring

#print axioms luscher_3site_cascade_coeff
end UnitaryRepresentation
