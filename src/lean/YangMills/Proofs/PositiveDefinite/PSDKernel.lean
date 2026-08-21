/-
# Positive Definite: PSD Kernels and the Crossing-Plaquette Kernel

This file formalizes the **group-level content of the Osterwalder–Seiler
crossing-plaquette argument** (design doc §8.11.97): the kernel produced by the
crossing plaquettes of the Wilson action is positive-semidefinite.

The key points:

1. `IsPSDKernel K`: a kernel `K : X → X → ℂ` is Hermitian and
   positive-semidefinite (sum form, mirroring `PositiveDefinite`).
2. `PositiveDefinite.isPSDKernel_pullback`: a positive-definite function
   `k : G → ℂ` pulls back along ANY map `g : X → G` to a PSD kernel
   `K(x, y) = k((g x)⁻¹ · g y)`.  **No homomorphism property of `g` is
   needed** — this resolves the §8.11.95 worry that "PD does not transfer
   through the non-homomorphic plaquette map": PD is required only in the
   plaquette-word variable, and the word map enters through the group
   operation `(x, y) ↦ (g x)⁻¹ · g y` on the pair.
3. `IsPSDKernel.mul` / `isPSDKernel_prod`: products of PSD kernels are PSD
   (Schur product theorem, mirroring `PositiveDefinite.mul`).
4. `crossingPlaquette_kernel_psd`: the crossing-plaquette kernel
   `K(x, y) = ∏_p k_p((W_p x)⁻¹ · W_p y)` is PSD whenever each `k_p` is PD
   (e.g. a non-negative character sum, by
   `positiveDefinite_finset_sum_repCharacter`).

0 sorries, 0 new axioms.
-/

import YangMills.Proofs.PositiveDefinite.Basic

open Finset
open Complex
open Matrix
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills

/-- A kernel `K : X → X → ℂ` is positive-semidefinite: it is Hermitian
(`K y x = conj (K x y)`) and for every finite `s : Finset X` and coefficients
`c : X → ℂ`, the quadratic form `∑ x ∈ s, ∑ y ∈ s, c x · conj (c y) · K x y`
is non-negative.  This is the kernel analogue of `PositiveDefinite`. -/
def IsPSDKernel {X : Type*} (K : X → X → ℂ) : Prop :=
  (∀ x y, K y x = conj (K x y)) ∧
  ∀ (s : Finset X) (c : X → ℂ),
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * K x y

lemma IsPSDKernel.congr {X : Type*} {K₁ K₂ : X → X → ℂ}
    (h : ∀ x y, K₁ x y = K₂ x y) (h1 : IsPSDKernel K₁) : IsPSDKernel K₂ := by
  refine ⟨fun x y => ?_, fun s c => ?_⟩
  · rw [← h y x, ← h x y]; exact h1.1 x y
  · have h2 := h1.2 s c
    have heq : (∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * K₂ x y) =
        ∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * K₁ x y :=
      Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by rw [h x y]))
    rwa [heq]

/-- The constant-one kernel is PSD. -/
lemma isPSDKernel_one {X : Type*} : IsPSDKernel (fun _ _ : X => (1 : ℂ)) := by
  refine ⟨fun _ _ => by simp, fun s c => ?_⟩
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * 1) =
      conj (∑ i ∈ s, c i) * (∑ i ∈ s, c i) := by
    simp only [mul_one]
    rw [← Finset.sum_mul_sum, ← map_sum (starRingEnd ℂ) c s, mul_comm]
  rw [hsum, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- A PSD kernel gives a positive-semidefinite matrix on any finite subset.
Mirrors `PositiveDefinite.matrix_posSemidef`. -/
lemma IsPSDKernel.matrix_posSemidef {X : Type*} {K : X → X → ℂ}
    (hK : IsPSDKernel K) (s : Finset X) :
    Matrix.PosSemidef (fun (i j : ↥s) => K i.val j.val : Matrix ↥s ↥s ℂ) := by
  haveI : DecidableEq ↥s := Classical.decEq _
  classical
  refine (Matrix.posSemidef_iff_dotProduct_mulVec
    (M := (fun (i j : ↥s) => K i.val j.val : Matrix ↥s ↥s ℂ))).mpr ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    show conj (K j.val i.val) = K i.val j.val
    rw [hK.1 i.val j.val, Complex.conj_conj]
  · intro x
    let c' : X → ℂ := fun i => if hi : i ∈ s then conj (x ⟨i, hi⟩) else 0
    have hPD := hK.2 s c'
    have hc'val : ∀ i : ↥s, c' i.val = conj (x i) := by
      intro i
      simp only [c', dif_pos i.property]
    have hc'conj : ∀ j : ↥s, conj (c' j.val) = x j := by
      intro j
      rw [hc'val j]
      exact star_star _
    let M : Matrix ↥s ↥s ℂ := fun i j => K i.val j.val
    have hdot : star x ⬝ᵥ (M *ᵥ x) =
        (∑ i ∈ s, ∑ j ∈ s, c' i * conj (c' j) * K i j) := by
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

/-- Pointwise product of two PSD kernels is PSD (Schur product theorem).
Mirrors `PositiveDefinite.mul`. -/
lemma IsPSDKernel.mul {X : Type*} {K₁ K₂ : X → X → ℂ}
    (h1 : IsPSDKernel K₁) (h2 : IsPSDKernel K₂) :
    IsPSDKernel (fun x y => K₁ x y * K₂ x y) := by
  refine ⟨fun x y => ?_, fun s c => ?_⟩
  · show K₁ y x * K₂ y x = conj (K₁ x y * K₂ x y)
    rw [h1.1 x y, h2.1 x y, map_mul]
  · classical
    haveI : DecidableEq ↥s := Classical.decEq _
    let A : Matrix ↥s ↥s ℂ := fun i j => K₁ i.val j.val
    let B : Matrix ↥s ↥s ℂ := fun i j => K₂ i.val j.val
    let v : ↥s → ℂ := fun i => c i.val
    have hA : Matrix.PosSemidef A := h1.matrix_posSemidef s
    have hB : Matrix.PosSemidef B := h2.matrix_posSemidef s
    have hAB : Matrix.PosSemidef (A ⊙ B) := Matrix.PosSemidef.hadamard hA hB
    let w : ↥s → ℂ := fun i => conj (v i)
    have hquad : 0 ≤ star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := Matrix.PosSemidef.dotProduct_mulVec_nonneg hAB w
    have htarget : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (K₁ i j * K₂ i j)) =
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

/-- A finite product of PSD kernels is PSD. -/
lemma isPSDKernel_prod {X P : Type*} (sP : Finset P) (K : P → X → X → ℂ)
    (hK : ∀ p ∈ sP, IsPSDKernel (K p)) :
    IsPSDKernel (fun x y => ∏ p ∈ sP, K p x y) := by
  classical
  induction sP using Finset.induction with
  | empty =>
    apply IsPSDKernel.congr (fun _ _ => (Finset.prod_empty).symm)
    exact isPSDKernel_one
  | insert a s ha ih =>
    apply IsPSDKernel.congr (fun x y => (Finset.prod_insert ha (f := fun p => K p x y)).symm)
    exact IsPSDKernel.mul (hK a (Finset.mem_insert_self a s))
      (ih (fun p hp => hK p (Finset.mem_insert_of_mem hp)))

/-- **PD pulls back along any map to a PSD kernel (sum form).**  If
`k : G → ℂ` is positive-definite and `g : X → G` is ANY function (no
homomorphism property required), then the kernel
`K(x, y) = k((g x)⁻¹ · g y)` satisfies the PSD quadratic-form inequality.

The proof partitions the double sum over `s` into fibers of `g`
(`Finset.sum_fiberwise_of_maps_to` applied twice), groups the coefficients as
`d a = ∑_{x : g x = a} c x`, and applies the PD property of `k` on the image
`s.image g`. -/
lemma PositiveDefinite.pullback_sum {G : Type*} [Group G] {X : Type*}
    {k : G → ℂ} (hk : PositiveDefinite k) (g : X → G)
    (s : Finset X) (c : X → ℂ) :
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * k ((g x)⁻¹ * g y) := by
  classical
  have hmaps : ∀ x ∈ s, g x ∈ s.image g := fun x hx => Finset.mem_image_of_mem g hx
  -- Fiber the inner sum over `y`.
  have hinner : ∀ x ∈ s,
      (∑ y ∈ s, c x * conj (c y) * k ((g x)⁻¹ * g y)) =
        ∑ b ∈ s.image g, c x * conj (∑ i ∈ s.filter (fun i => g i = b), c i) *
          k ((g x)⁻¹ * b) := by
    intro x _
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
      (f := fun y => c x * conj (c y) * k ((g x)⁻¹ * g y)) hmaps]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [map_sum (starRingEnd ℂ) _ _, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.mem_filter] at hy
    rw [hy.2]
  -- Fiber the outer sum over `x`.
  have houter : (∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * k ((g x)⁻¹ * g y)) =
      ∑ a ∈ s.image g, ∑ b ∈ s.image g,
        (∑ i ∈ s.filter (fun i => g i = a), c i) *
          conj (∑ i ∈ s.filter (fun i => g i = b), c i) * k (a⁻¹ * b) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
      (f := fun x => ∑ y ∈ s, c x * conj (c y) * k ((g x)⁻¹ * g y)) hmaps]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hstep : ∀ x ∈ s.filter (fun x => g x = a),
        (∑ y ∈ s, c x * conj (c y) * k ((g x)⁻¹ * g y)) =
          ∑ b ∈ s.image g, c x *
            conj (∑ i ∈ s.filter (fun i => g i = b), c i) * k (a⁻¹ * b) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hinner x hx.1, hx.2]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have he : ∀ x ∈ s.filter (fun x => g x = a),
        c x * conj (∑ i ∈ s.filter (fun i => g i = b), c i) * k (a⁻¹ * b) =
        c x * (conj (∑ i ∈ s.filter (fun i => g i = b), c i) * k (a⁻¹ * b)) :=
      fun x _ => mul_assoc _ _ _
    rw [Finset.sum_congr rfl he, ← Finset.sum_mul, mul_assoc]
  rw [houter]
  exact hk (s.image g) (fun a => ∑ x ∈ s.filter (fun x => g x = a), c x)

/-- **PD pulls back along any map to a PSD kernel.**  If `k : G → ℂ` is
positive-definite and `g : X → G` is any function, the kernel
`K(x, y) = k((g x)⁻¹ · g y)` is PSD.  Hermiticity follows from
`PositiveDefinite.conj_inv` (`k(h⁻¹) = conj (k h)`) and
`((g x)⁻¹ · g y)⁻¹ = (g y)⁻¹ · g x`. -/
lemma PositiveDefinite.isPSDKernel_pullback {G : Type*} [Group G] {X : Type*}
    {k : G → ℂ} (hk : PositiveDefinite k) (g : X → G) :
    IsPSDKernel (fun x y => k ((g x)⁻¹ * g y)) := by
  refine ⟨fun x y => ?_, fun s c => hk.pullback_sum g s c⟩
  show k ((g y)⁻¹ * g x) = conj (k ((g x)⁻¹ * g y))
  rw [← hk.conj_inv ((g x)⁻¹ * g y), _root_.mul_inv_rev, inv_inv]

#print axioms PositiveDefinite.isPSDKernel_pullback

/-- **The crossing-plaquette kernel is PSD (group-level OS argument).**
Given a finite set of crossing plaquettes `sP`, a PD function `k p : G → ℂ`
for each (e.g. the plaquette Boltzmann factor `exp(β·ReTr(·))`, PD by its
non-negative character expansion via `positiveDefinite_finset_sum_repCharacter`),
and for each plaquette a word map `W p : X → G` extracting the plaquette word
from a half-configuration, the kernel

    K(x, y) = ∏ p ∈ sP, k p ((W p x)⁻¹ · W p y)

is positive-semidefinite.  This is the exact group-level content of the
Osterwalder–Seiler crossing-plaquette argument: the lattice reflection maps
the negative-side plaquette word to the inverse of the positive-side word, so
the crossing factor is a PD function evaluated at `(W⁻)⁻¹ · W⁺` — the PD
kernel form.  No homomorphism property of the word maps is needed. -/
lemma crossingPlaquette_kernel_psd {G : Type*} [Group G] {X P : Type*}
    (sP : Finset P) (k : P → G → ℂ) (hk : ∀ p ∈ sP, PositiveDefinite (k p))
    (W : P → X → G) :
    IsPSDKernel (fun x y => ∏ p ∈ sP, k p ((W p x)⁻¹ * W p y)) :=
  isPSDKernel_prod sP (fun p x y => k p ((W p x)⁻¹ * W p y))
    (fun p hp => (hk p hp).isPSDKernel_pullback (W p))

#print axioms crossingPlaquette_kernel_psd

end YangMills
