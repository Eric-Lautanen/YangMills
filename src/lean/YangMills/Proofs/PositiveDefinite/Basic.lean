/-
# Positive Definite: Basic Properties
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
lemma PositiveDefinite.matrix_posSemidef (hφ : PositiveDefinite φ) (s : Finset G) :
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
