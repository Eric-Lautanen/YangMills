/-
# Positive Definite Integral: Cascade Non-Negativity

Step 4/5 cascade integral non-negativity: 2-site and shared-variable
cascade kernels, factorization lemmas, and connection to the
non-negativity kernel form.
-/

import YangMills.Proofs.PositiveDefiniteIntegral.CharacterExpansionPositivity

open Finset MeasureTheory Complex Metric Matrix

open scoped ComplexConjugate ComplexOrder Function

namespace YangMills

variable {G : Type*} [Group G]
/-! ## Step 4: cascade integral non-negativity

The 2D character-level cascade `luscher_2site_2D_cascade_charlevel`
(`PositiveDefinite.lean`) reduces the 2-site integral to
`∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)`.  The following
lemma shows this kernel, integrated against `f(W)·f(V⁻¹)`, is
non-negative.  The key is the trace expansion
`χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})` (unitarity),
which puts the kernel into the separable form required by
`character_expansion_nonneg` with `θ = inv` (measure-preserving by
`IsInvInvariant`).  The coefficients
`cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν) ≥ 0` come from `hcg` and
`hDims`. -/

/-- Helper: trace expansion of `χ_ν(W·V)` using unitarity.
`χ_ν(W·V) = Tr(ρ_ν(W)·ρ_ν(V)) = ∑_{a,b} (ρ_ν W)_{ab}·(ρ_ν V)_{ba}`,
and `(ρ_ν V)_{ba} = conj((ρ_ν V⁻¹)_{ab})` by `repMatrixElement_inv`. -/
lemma repCharacter_trace_expand
    {G : Type*} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitaryRepresentation ρ) (W V : G) :
    repCharacter ρ (W * V) =
      ∑ a : Fin n, ∑ b : Fin n, (ρ W) a b * conj ((ρ V⁻¹) a b) := by
  have htrace_mul : ∀ (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro A B; simp [Matrix.trace, Matrix.mul_apply]
  rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h := repMatrixElement_inv ρ hU V a b
  rw [h, Complex.conj_conj]

/-- **Step 4: the cascade integral is non-negative.**  The kernel
`K(W,V) = ∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)` (the output
of `luscher_2site_2D_cascade_charlevel`) integrated against
`f(W)·f(V⁻¹)` is non-negative, since `χ_ν(W·V)` expands via unitarity
into a separable form `∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})` with
non-negative coefficients `cg·cg·(1/dims ν) ≥ 0`, and `θ = inv` is
measure-preserving (`IsInvInvariant`). -/
lemma cascade_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ)
    (hcg : ∀ s t w, 0 ≤ cg s t w)
    (s₁ s₂ t₁ t₂ : ι)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hρ_meas : ∀ ν (a b : Fin (dims ν)), AEStronglyMeasurable (fun g => (ρ ν g) a b) μ)
    (hfρ_int : ∀ ν (a b : Fin (dims ν)), Integrable (fun g => (f g : ℂ) * (ρ ν g) a b) μ) :
    0 ≤ ∫ W, ∫ V,
      (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
        ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V)) ∂μ ∂μ := by
  -- Sigma index type: ι' = Σ ν, Fin(dims ν) × Fin(dims ν)
  -- Use the sigma type directly (no let/set binding) so Finset.univ_sigma_univ
  -- and the Fintype instance from inferInstance agree.
  set_option maxHeartbeats 400000 in
  letI : Fintype (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := inferInstance
  haveI : DecidableEq (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := Classical.decEq _
  -- Coefficients: a'(i) = cg(s₁,s₂,i.1)·cg(t₁,t₂,i.1)/dims(i.1) ≥ 0
  let a' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → ℝ :=
    fun i => cg s₁ s₂ i.1 * cg t₁ t₂ i.1 / dims i.1
  -- Basis: Φ'(i)(g) = (ρ_{i.1} g)_{i.2.1, i.2.2}
  let Φ' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → G → ℂ :=
    fun i g => (ρ i.1) g i.2.1 i.2.2
  -- Kernel: K(W,V) = ∑_ν cg·cg·(1/dims)·χ_ν(W·V)
  let K : G → G → ℂ := fun W V =>
    ∑ ν, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
      ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V))
  -- Non-negativity of coefficients
  have ha' : ∀ i, 0 ≤ a' i := by
    intro i
    exact div_nonneg (mul_nonneg (hcg s₁ s₂ i.1) (hcg t₁ t₂ i.1)) (Nat.cast_nonneg _)
  -- Kernel expansion: K(W,V) = ∑_i a'(i)·Φ'(i)(W)·conj(Φ'(i)(V⁻¹))
  have hK : ∀ W V, K W V =
      ∑ i : Σ ν : ι, Fin (dims ν) × Fin (dims ν), (a' i : ℂ) * (Φ' i W * conj (Φ' i (V⁻¹))) := by
    intro W V
    -- Step 1: Expand K to nested form ∑ ν, ∑ a, ∑ b, ...
    have hK_nested : K W V = ∑ ν, ∑ a, ∑ b,
        (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) * ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b)) := by
      show ∑ ν, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
          ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V)) =
        ∑ ν, ∑ a, ∑ b,
          (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) * ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))
      apply Finset.sum_congr rfl
      intro ν _
      rw [repCharacter_trace_expand (ρ ν) (hU ν) W V]
      rw [show ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) * ((1 / dims ν : ℂ) *
            (∑ a, ∑ b, (ρ ν W) a b * conj ((ρ ν V⁻¹) a b)))) =
          ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) * (1 / dims ν : ℂ)) *
            (∑ a, ∑ b, (ρ ν W) a b * conj ((ρ ν V⁻¹) a b)) from by ring]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    -- Step 2: Convert nested form to sigma form
    rw [hK_nested]
    have hstep1 : (∑ ν, ∑ a, ∑ b, (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) *
          ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))) =
        ∑ ν, ∑ p ∈ (Finset.univ : Finset (Fin (dims ν) × Fin (dims ν))),
          (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) *
          ((ρ ν W) p.1 p.2 * conj ((ρ ν (V⁻¹)) p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [← Finset.sum_product', Finset.univ_product_univ]
    rw [hstep1, Finset.sum_sigma', Finset.univ_sigma_univ]
    apply Finset.sum_congr rfl
    rintro i _
    simp only [a', Φ']
    push_cast [Complex.ofReal_div, Complex.ofReal_mul]
    ring
  -- Measurability of basis functions
  have hΦ'_meas : ∀ i, AEStronglyMeasurable (Φ' i) μ := by
    intro i
    exact hρ_meas i.1 i.2.1 i.2.2
  -- Integrability of f · basis functions
  have hfΦ'_int : ∀ i, Integrable (fun g => (f g : ℂ) * Φ' i g) μ := by
    intro i
    exact hfρ_int i.1 i.2.1 i.2.2
  -- Apply character_expansion_nonneg with θ = Inv.inv (measure-preserving by hθ)
  exact character_expansion_nonneg μ μ (Inv.inv : G → G) hθ _ a' ha' Φ' f
    hΦ'_meas hf_meas hfΦ'_int K hK

#print axioms cascade_integral_nonneg

/-! ## Step 4 (generalized): character-kernel integral non-negativity

The following lemma generalizes `cascade_integral_nonneg` to arbitrary non-negative
coefficients `coeff : ι → ℝ` (instead of the specific `cg s₁ s₂ ν · cg t₁ t₂ ν · (1/dims ν)`
form from the 2-character CG cascade).  This is the key non-negativity lemma for the
Lüscher mechanism (step 4 of the formalization plan, §8.11.45): after the Lüscher cascade
integrates out the temporal links, the resulting kernel has the form
`∑_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`, and this lemma gives the non-negativity of the
integral `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0`.

The proof is identical in structure to `cascade_integral_nonneg`: expand `χ_ν(W·V)` via
`repCharacter_trace_expand` (unitarity) into the separable form
`∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`, then apply `character_expansion_nonneg`
with `θ = inv` (measure-preserving by `hθ`).  The only difference is the coefficient:
`a'(i) = coeff(i.1)` instead of `cg s₁ s₂ i.1 · cg t₁ t₂ i.1 / dims i.1`. -/

/-- **Generalized character-kernel integral non-negativity.** For a compact group `G`
with probability measure `μ` (invariant under inversion), a finite family of irreducible
unitary reps `ρ_ν` of dimension `dims ν`, and non-negative coefficients `coeff : ι → ℝ`
with `coeff ν ≥ 0`, the integral

    ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) * ∑_ν (coeff ν : ℂ) * χ_ν(W * V) ∂μ ∂μ

is non-negative.  The key is the trace expansion
`χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})` (unitarity),
which puts the kernel into the separable form required by
`character_expansion_nonneg` with `θ = inv` (measure-preserving by `hθ`).

This generalizes `cascade_integral_nonneg` (which has the specific coefficient
`cg s₁ s₂ ν · cg t₁ t₂ ν · (1/dims ν)`) to arbitrary non-negative coefficients. -/
lemma character_kernel_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (coeff : ι → ℝ) (hcoeff : ∀ ν, 0 ≤ coeff ν)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hρ_meas : ∀ ν (a b : Fin (dims ν)), AEStronglyMeasurable (fun g => (ρ ν g) a b) μ)
    (hfρ_int : ∀ ν (a b : Fin (dims ν)), Integrable (fun g => (f g : ℂ) * (ρ ν g) a b) μ) :
    0 ≤ ∫ W, ∫ V,
      (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∑ ν : ι, (coeff ν : ℂ) * repCharacter (ρ ν) (W * V) ∂μ ∂μ := by
  set_option maxHeartbeats 400000 in
  letI : Fintype (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := inferInstance
  haveI : DecidableEq (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := Classical.decEq _
  let a' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → ℝ :=
    fun i => coeff i.1
  let Φ' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → G → ℂ :=
    fun i g => (ρ i.1) g i.2.1 i.2.2
  let K : G → G → ℂ := fun W V =>
    ∑ ν, (coeff ν : ℂ) * repCharacter (ρ ν) (W * V)
  have ha' : ∀ i, 0 ≤ a' i := fun i => hcoeff i.1
  have hK : ∀ W V, K W V =
      ∑ i : Σ ν : ι, Fin (dims ν) × Fin (dims ν), (a' i : ℂ) * (Φ' i W * conj (Φ' i (V⁻¹))) := by
    intro W V
    have hK_nested : K W V = ∑ ν, ∑ c, ∑ d,
        (coeff ν : ℂ) * ((ρ ν W) c d * conj ((ρ ν (V⁻¹)) c d)) := by
      show ∑ ν, (coeff ν : ℂ) * repCharacter (ρ ν) (W * V) =
        ∑ ν, ∑ c, ∑ d,
          (coeff ν : ℂ) * ((ρ ν W) c d * conj ((ρ ν (V⁻¹)) c d))
      apply Finset.sum_congr rfl
      intro ν _
      rw [repCharacter_trace_expand (ρ ν) (hU ν) W V]
      rw [show ((coeff ν : ℂ) *
            (∑ a, ∑ b, (ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))) =
          (∑ a, ∑ b, (coeff ν : ℂ) *
            ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]]
    rw [hK_nested]
    have hstep1 : (∑ ν, ∑ c, ∑ d, (coeff ν : ℂ) *
          ((ρ ν W) c d * conj ((ρ ν (V⁻¹)) c d))) =
        ∑ ν, ∑ p ∈ (Finset.univ : Finset (Fin (dims ν) × Fin (dims ν))),
          (coeff ν : ℂ) *
          ((ρ ν W) p.1 p.2 * conj ((ρ ν (V⁻¹)) p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [← Finset.sum_product', Finset.univ_product_univ]
    rw [hstep1, Finset.sum_sigma', Finset.univ_sigma_univ]
  have hΦ'_meas : ∀ i, AEStronglyMeasurable (Φ' i) μ := fun i => hρ_meas i.1 i.2.1 i.2.2
  have hfΦ'_int : ∀ i, Integrable (fun g => (f g : ℂ) * Φ' i g) μ := fun i => hfρ_int i.1 i.2.1 i.2.2
  exact character_expansion_nonneg μ μ (Inv.inv : G → G) hθ _ a' ha' Φ' f
    hΦ'_meas hf_meas hfΦ'_int K hK

#print axioms character_kernel_integral_nonneg

/-! ## Step 3+4 combination: cascade kernel integral non-negativity

The following lemma combines `luscher_2site_cascade_coeff` (step 3: the Lüscher cascade
integrates out temporal links `g₀, g₁`, producing a kernel `∑_s F(s,s)·(1/d_s)·χ_s(W·V)`)
with `character_kernel_integral_nonneg` (step 4: non-negativity of `∫∫ f(W)·f(V⁻¹)·K(W,V)` for
any kernel `K(W,V) = ∑_ν a_ν·χ_ν(W·V)` with `a_ν ≥ 0`).

The result: for arbitrary non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`, the
full 4-fold integral (outer `W, V` × inner cascade `g₀, g₁`) is non-negative:

    0 ≤ ∫ W ∫ V (f W)·(f V⁻¹)·[∫ g₀ ∫ g₁ ∑_{s,t} F(s,t)·χ_s(g₀·W·g₁⁻¹)·χ_t(g₁·V·g₀⁻¹)] ∂μ ∂μ ∂μ ∂μ

The proof: (1) the inner cascade equals `∑_s (F s s / dims s)·χ_s(W·V)` by
`luscher_2site_cascade_coeff` + coefficient conversion; (2) the coefficient
`F s s / dims s ≥ 0` (since `F s s ≥ 0` and `dims s > 0`); (3) apply
`character_kernel_integral_nonneg` with `coeff s = F s s / dims s`. 0 sorries, 0 new axioms. -/
lemma luscher_2site_cascade_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ℝ) (hF : ∀ s t, 0 ≤ F s t)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hρ_meas : ∀ ν (a b : Fin (dims ν)), AEStronglyMeasurable (fun g => (ρ ν g) a b) μ)
    (hfρ_int : ∀ ν (a b : Fin (dims ν)), Integrable (fun g => (f g : ℂ) * (ρ ν g) a b) μ) :
    0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ ∂μ ∂μ := by
  let coeff : ι → ℝ := fun s => F s s / dims s
  have hcoeff : ∀ s, 0 ≤ coeff s := fun s => div_nonneg (hF s s) (Nat.cast_nonneg _)
  have hKernel : ∀ W V,
      (∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ) =
      ∑ s, (coeff s : ℂ) * repCharacter (ρ s) (W * V) := by
    intro W V
    rw [luscher_2site_cascade_coeff μ ι dims hDims ρ hU hIrr F hF W V]
    apply Finset.sum_congr rfl
    intro s _
    have hne : (dims s : ℂ) ≠ 0 := by
      have h : 0 < (dims s : ℂ) := by exact mod_cast (hDims s)
      exact ne_of_gt h
    rw [show coeff s = F s s / dims s from rfl]
    push_cast
    field_simp
  rw [show (∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
        (∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ) ∂μ ∂μ) =
      (∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
        (∑ s, (coeff s : ℂ) * repCharacter (ρ s) (W * V)) ∂μ ∂μ) from by
    congr 1 with W
    congr 1 with V
    rw [hKernel]]
  exact character_kernel_integral_nonneg μ hθ ι dims hDims ρ hU coeff hcoeff
    f hf_meas hρ_meas hfρ_int

#print axioms luscher_2site_cascade_integral_nonneg
#print axioms luscher_2site_cascade_integral_nonneg

/-! ## Step 3d: separable character kernel non-negativity

The following lemma is the non-negativity result for the **separable** kernel
`K(W,V) = Σ_s coeff_s · χ_s(W) · χ_s(V)` produced by
`luscher_2site_cascade_separable` (step 3c).  By `repCharacter_inv`
(`χ_s(V) = conj(χ_s(V⁻¹))` for unitary representations), the kernel becomes
`Σ_s coeff_s · χ_s(W) · conj(χ_s(V⁻¹))`, which is a positive-definite kernel
in the Mercer sense (sum of rank-1 PD kernels with non-negative coefficients).
The non-negativity follows from `character_expansion_nonneg` with `θ = inv`.
0 sorries, 0 new axioms.  This is the L=2 case where the reversal obstruction
(§8.11.71 Finding 2) does NOT appear.  The `hIrr` hypothesis is NOT needed
here — the separable kernel non-negativity is a general PD-kernel result.  -/

lemma separable_character_kernel_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hχ_meas : ∀ s, AEStronglyMeasurable (fun g => repCharacter (ρ s) g) μ)
    (hfχ_int : ∀ s, Integrable (fun g => (f g : ℂ) * repCharacter (ρ s) g) μ) :
    0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∑ s, (coeff s : ℂ) * repCharacter (ρ s) W * repCharacter (ρ s) V ∂μ ∂μ := by
  let K : G → G → ℂ := fun W V =>
    ∑ s, (coeff s : ℂ) * repCharacter (ρ s) W * repCharacter (ρ s) V
  have hK : ∀ W V,
      K W V = ∑ s, (coeff s : ℂ) * (repCharacter (ρ s) W * conj (repCharacter (ρ s) (V⁻¹))) := by
    intro W V
    apply Finset.sum_congr rfl
    intro s _
    have h := repCharacter_inv (ρ s) (hU s) V
    have h2 : repCharacter (ρ s) V = conj (repCharacter (ρ s) (V⁻¹)) := by
      rw [h, Complex.conj_conj]
    rw [h2]
    ring
  exact character_expansion_nonneg μ μ (Inv.inv : G → G) hθ ι coeff hcoeff
    (fun s => repCharacter (ρ s)) f hχ_meas hf_meas hfχ_int K hK

#print axioms separable_character_kernel_integral_nonneg

/-! ## Helper lemmas: deriving character-level hypotheses from matrix-element measurability

The `luscher_2site_factorization_nonneg` lemma (below) takes character-level
hypotheses `hΦ_meas`, `hf_meas`, `hfΦ_int` on the product group `G × G`. These
helpers derive `hΦ_meas` (and later `hfΦ_int`) from the more primitive
matrix-element measurability `hρ_meas`, which is the natural hypothesis in the
Peter-Weyl setting (matrix elements of continuous representations are continuous,
hence Borel measurable). -/

/-- Helper: trace expansion of `χ_s(W₀·W₁)` (without inversion).
`χ_s(W₀·W₁) = Tr(ρ_s(W₀)·ρ_s(W₁)) = ∑_{a,b} (ρ_s W₀)_{ab}·(ρ_s W₁)_{ba}`.
This is the plain (non-unitary) version of `repCharacter_trace_expand` (which
uses `V⁻¹` and unitarity to replace `(ρ V)_{ba}` by `conj((ρ V⁻¹)_{ab})`). -/
lemma repCharacter_trace_expand_prod
    {G : Type*} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (W₀ W₁ : G) :
    repCharacter ρ (W₀ * W₁) =
      ∑ a : Fin n, ∑ b : Fin n, (ρ W₀) a b * (ρ W₁) b a := by
  have htrace_mul : ∀ (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro A B; simp [Matrix.trace, Matrix.mul_apply]
  rw [repCharacter, MonoidHom.map_mul, htrace_mul]

set_option maxHeartbeats 400000 in
/-- Helper: `AEStronglyMeasurable` of `χ_s(W₀·W₁)` on the product group `G × G`,
derived from matrix-element measurability `hρ_meas`.

The character `χ_s(W₀·W₁)` expands via `repCharacter_trace_expand_prod` into a
finite sum of products of matrix elements `(ρ_s W₀)_{ab}·(ρ_s W₁)_{ba}`. Each
matrix element is lifted to the product group `G × G` via
`AEStronglyMeasurable.comp_quasiMeasurePreserving` with `quasiMeasurePreserving_fst`
(for `W₀ = Prod.fst W`) and `quasiMeasurePreserving_snd` (for `W₁ = Prod.snd W`).
Products (`AEStronglyMeasurable.mul`) and finite sums
(`Finset.aestronglyMeasurable_fun_sum`) preserve `AEStronglyMeasurable`. -/
lemma repCharacter_product_aestronglyMeasurable
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ)
    (s : ι) :
    AEStronglyMeasurable (fun W => repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ) := by
  -- Step 1: Lift each matrix element to the product group G × G
  have hW1 : ∀ (a b : Fin (dims s)),
      AEStronglyMeasurable (fun W => (ρ s W.1) a b) (μ.prod μ) := fun a b =>
    (hρ_meas s a b).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hW2 : ∀ (a b : Fin (dims s)),
      AEStronglyMeasurable (fun W => (ρ s W.2) a b) (μ.prod μ) := fun a b =>
    (hρ_meas s a b).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  -- Step 2: Each product (ρ W.1)_{ab} · (ρ W.2)_{ba} is AEStronglyMeasurable
  have hprod : ∀ (a b : Fin (dims s)),
      AEStronglyMeasurable (fun W => (ρ s W.1) a b * (ρ s W.2) b a) (μ.prod μ) :=
    fun a b => (hW1 a b).mul (hW2 b a)
  -- Step 3: Inner sum over b is AEStronglyMeasurable (via Finset.aestronglyMeasurable_fun_sum)
  have hinner : ∀ (a : Fin (dims s)),
      AEStronglyMeasurable (fun W => ∑ b : Fin (dims s), (ρ s W.1) a b * (ρ s W.2) b a)
        (μ.prod μ) := fun a =>
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun b _ => hprod a b)
  -- Step 4: Outer sum over a is AEStronglyMeasurable
  have hsum : AEStronglyMeasurable
      (fun W => ∑ a : Fin (dims s), ∑ b : Fin (dims s), (ρ s W.1) a b * (ρ s W.2) b a)
      (μ.prod μ) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun a _ => hinner a)
  -- Step 5: Rewrite to character form via a.e. equality (everywhere equality)
  refine hsum.congr ?_
  filter_upwards with W
  exact (repCharacter_trace_expand_prod (ρ s) W.1 W.2).symm

#print axioms repCharacter_trace_expand_prod
#print axioms repCharacter_product_aestronglyMeasurable

/-- Helper: `Integrable` of `f · χ_s(W₀·W₁)` on the product group `G × G`, derived
from integrability of `f` and the character bound `‖χ_s(g)‖ ≤ dims s` (unitarity).

For a unitary representation, `‖χ_s(g)‖ ≤ dims s` (trace of a unitary matrix, each
diagonal entry `‖·‖ ≤ 1`). So `‖f(W) · χ_s(W₀·W₁)‖ ≤ dims s · ‖f(W)‖`, and `f`
integrable implies `f · χ_s` integrable via `Integrable.mono'`. -/
lemma repCharacter_product_integrable
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ)
    (f : G × G → ℝ)
    (hf_int : Integrable (fun W => (f W : ℂ)) (μ.prod μ))
    (s : ι) :
    Integrable (fun W => (f W : ℂ) * repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ) := by
  -- Measurability of f · χ_s (from hf_int.aestronglyMeasurable and hΦ_meas)
  have hΦ_meas := repCharacter_product_aestronglyMeasurable μ ι dims ρ hρ_meas s
  have hfΦ_meas : AEStronglyMeasurable
      (fun W => (f W : ℂ) * repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ) :=
    hf_int.aestronglyMeasurable.mul hΦ_meas
  -- Dominating function: (dims s : ℝ) * ‖f‖ is integrable
  have hg : Integrable (fun W => (dims s : ℝ) * ‖(f W : ℂ)‖) (μ.prod μ) :=
    (Integrable.norm hf_int).const_mul _
  -- Norm bound: ‖f · χ_s‖ ≤ dims s * ‖f‖, then apply Integrable.mono'
  refine Integrable.mono' hg hfΦ_meas ?_
  filter_upwards with W
  calc ‖(f W : ℂ) * repCharacter (ρ s) (W.1 * W.2)‖
      ≤ ‖(f W : ℂ)‖ * ‖repCharacter (ρ s) (W.1 * W.2)‖ := norm_mul_le _ _
    _ ≤ ‖(f W : ℂ)‖ * (dims s : ℝ) := mul_le_mul_of_nonneg_left
        (repCharacter_norm_le_dim (ρ s) (hU s) (W.1 * W.2)) (norm_nonneg _)
    _ = (dims s : ℝ) * ‖(f W : ℂ)‖ := mul_comm _ _

#print axioms repCharacter_product_integrable

/-! ## Step 4 (factorization): 2-site cascade kernel non-negativity on the product group G²

The 2-site temporal cascade (`luscher_2site_cascade_separable` in `PositiveDefinite.lean`)
produces the separable kernel
  `K(W,V) = Σ_s c_s · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)`  with  `c_s = F(s,s)·(1/d_s)² ≥ 0`.

By `repCharacter_inv`, `χ_s(W₁⁻¹·W₀⁻¹) = χ_s((W₀·W₁)⁻¹) = conj(χ_s(W₀·W₁))`, so
  `conj(K(W,V)) = Σ_s c_s · χ_s(W₀·W₁) · conj(χ_s(V₀·V₁))`.

This is the `character_expansion_nonneg` form with **θ = id** (not inv),
`Φ_s(W₀,W₁) = χ_s(W₀·W₁)`, `a_s = c_s ≥ 0`, on the product group `G² = G × G`
with product measure `μ × μ`.

The result: `0 ≤ ∫∫ f(W)·f(V)·conj(K(W,V)) d(μ×μ) d(μ×μ) = Σ_s c_s · |E_s|² ≥ 0`
where `E_s = ∫ f(W)·χ_s(W₀·W₁) d(μ×μ)`.

This is the **inner-product form** (θ = id, conj(K)), NOT the reflection-positivity
form (θ = inv) used in `separable_character_kernel_integral_nonneg`. The conj on the
V-part (from conj(K)) combined with the real-valued f gives `|E_s|²`, not `A_s · B_s`.
See §8.11.75 of the design doc for the corrected analysis. -/

/-- **Step 4 (factorization): the 2-site cascade kernel gives a non-negative integral
on the product group G².**

Given the cascade coefficients `c_s = F(s,s)·(1/d_s)² ≥ 0` and a real-valued test
function `f : G × G → ℝ`, the integral of `f(W)·f(V)` against `conj(K(W,V))` is
non-negative, where `K` is the 2-site cascade kernel. This follows from
`character_expansion_nonneg` with `θ = id` on the product group `G²`. -/
lemma luscher_2site_factorization_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (F : ι → ι → ℝ) (hF : ∀ s t, 0 ≤ F s t)
    (f : G × G → ℝ)
    (hΦ_meas : ∀ s, AEStronglyMeasurable (fun W => repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ))
    (hf_meas : AEStronglyMeasurable (fun W => (f W : ℂ)) (μ.prod μ))
    (hfΦ_int : ∀ s, Integrable (fun W => (f W : ℂ) * repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ)) :
    0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V : ℂ) *
      ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ)^2 *
        repCharacter (ρ s) (W.1 * W.2) * conj (repCharacter (ρ s) (V.1 * V.2)))
      ∂(μ.prod μ) ∂(μ.prod μ) := by
  -- Coefficient a_s = F(s,s) * (1/d_s)^2 ≥ 0
  have ha : ∀ s, 0 ≤ F s s * (1 / (dims s : ℝ))^2 := fun s =>
    mul_nonneg (hF s s) (sq_nonneg _)
  -- The kernel K(W,V) in the statement matches the character_expansion_nonneg form
  -- K(W,V) = Σ_s (a_s : ℂ) * (Φ_s(W) * conj(Φ_s(V)))
  -- where a_s = F(s,s)*(1/d_s)^2 and Φ_s(W) = χ_s(W.1*W.2)
  exact character_expansion_nonneg (μ.prod μ) (μ.prod μ) id (MeasurePreserving.id _)
    ι (fun s => F s s * (1 / (dims s : ℝ))^2) ha
    (fun s W => repCharacter (ρ s) (W.1 * W.2)) f
    hΦ_meas hf_meas hfΦ_int
    (fun W V => ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ)^2 *
      repCharacter (ρ s) (W.1 * W.2) * conj (repCharacter (ρ s) (V.1 * V.2))))
    (fun W V => by
      apply Finset.sum_congr rfl
      intro s _
      push_cast
      simp only [id]
      ring)

#print axioms luscher_2site_factorization_nonneg
/-! ## Key finding: 3-site cascade does NOT directly combine with character_kernel_integral_nonneg

The 3-site cascade (`luscher_3site_cascade_coeff` in `PositiveDefinite.lean`) evaluates to
`∑_s F(s,s,s) · (1/d_s)² · χ_s(W₀·W₁·W₂)` — a CONSTANT (not a kernel in W, V).
The outer integral `∫ W ∫ V f(W)·f(V⁻¹)·[constant]` = `[constant]·|∫f|²`,
and the constant is a sum of characters (complex in general), so the product is
NOT necessarily non-negative.

This contrasts with the 2-site case, where the cascade produces a KERNEL
`K(W,V) = ∑_s coeff_s · χ_s(W·V)` (a function of W·V), which matches
`character_kernel_integral_nonneg` directly.

The 3-site cascade coefficient lemma is correct and useful for evaluating cascades,
but the non-negativity combination requires a different approach: either (a) a generalized
non-negativity lemma for kernels of the form `χ_s(W·M·V)` with a fixed bridge M, (b) the
specific lattice structure where the cascade produces `χ_s(W·V)` directly, or (c) pairwise
decomposition using the 2-site cascade repeatedly. See §8.11.49 of the design doc. -/

/-! ## Step 5 (shared-variable): helper lemmas for Φ_s(z, x) = χ_s(z * x)

These helpers generalize `repCharacter_product_aestronglyMeasurable` and
`repCharacter_product_integrable` to the shared-variable form needed for the
transfer matrix positivity proof (§8.11.78). In the transfer matrix, the
spatial interface links `z = u⁰_s` are shared between the positive and
reflected-negative configs, and the character takes the form
`Φ_s(z, x) = χ_s(z * x)` (product of the shared link and the positive links).

The key difference from the product-group helpers: the first factor `(ρ_s z)_{ab}`
is a CONSTANT (z is fixed), so we use `AEStronglyMeasurable.const_mul` instead of
`comp_quasiMeasurePreserving` to lift it. -/

set_option maxHeartbeats 400000 in
/-- Helper: `AEStronglyMeasurable` of `χ_s(z * x)` in `x` for fixed `z`.

The character `χ_s(z * x)` expands via `repCharacter_trace_expand_prod` into a
finite sum of products `(ρ_s z)_{ab} · (ρ_s x)_{ba}`. For fixed `z`, each
`(ρ_s z)_{ab}` is a constant, and `(ρ_s x)_{ba}` is AESM from `hρ_meas`.
`AEStronglyMeasurable.const_mul` lifts the constant, and
`Finset.aestronglyMeasurable_fun_sum` handles the finite sums. -/
lemma repCharacter_leftmul_aestronglyMeasurable
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ)
    (s : ι) (z : G) :
    AEStronglyMeasurable (fun x => repCharacter (ρ s) (z * x)) μ := by
  -- Step 1: Each (ρ s x) b a is AESM from hρ_meas
  have hME : ∀ (a b : Fin (dims s)),
      AEStronglyMeasurable (fun x => (ρ s x) b a) μ := fun a b => hρ_meas s b a
  -- Step 2: Each (ρ s z) a b * (ρ s x) b a is AESM (const_mul)
  have hprod : ∀ (a b : Fin (dims s)),
      AEStronglyMeasurable (fun x => (ρ s z) a b * (ρ s x) b a) μ :=
    fun a b => (hME a b).const_mul ((ρ s z) a b)
  -- Step 3: Inner sum over b is AEStronglyMeasurable
  have hinner : ∀ (a : Fin (dims s)),
      AEStronglyMeasurable (fun x => ∑ b : Fin (dims s), (ρ s z) a b * (ρ s x) b a) μ :=
    fun a => Finset.aestronglyMeasurable_fun_sum Finset.univ (fun b _ => hprod a b)
  -- Step 4: Outer sum over a is AEStronglyMeasurable
  have hsum : AEStronglyMeasurable
      (fun x => ∑ a : Fin (dims s), ∑ b : Fin (dims s), (ρ s z) a b * (ρ s x) b a) μ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun a _ => hinner a)
  -- Step 5: Rewrite to character form via a.e. equality
  refine hsum.congr ?_
  filter_upwards with x
  exact (repCharacter_trace_expand_prod (ρ s) z x).symm

#print axioms repCharacter_leftmul_aestronglyMeasurable

/-- Helper: `Integrable` of `g(x, z) · χ_s(z * x)` in `x` for fixed `z`, derived
from integrability of `g(·, z)` and the character bound `‖χ_s(g)‖ ≤ dims s`.

For a unitary representation, `‖χ_s(z * x)‖ ≤ dims s` (trace of a unitary matrix,
each diagonal entry `‖·‖ ≤ 1`). So `‖g(x,z) · χ_s(z * x)‖ ≤ dims s · ‖g(x,z)‖`,
and `g(·, z)` integrable implies `g(·, z) · χ_s(z · ·)` integrable via
`Integrable.mono'`. -/
lemma repCharacter_leftmul_integrable
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ)
    (g : G → G → ℝ)
    (hg_int : ∀ z, Integrable (fun x => (g x z : ℂ)) μ)
    (s : ι) (z : G) :
    Integrable (fun x => (g x z : ℂ) * repCharacter (ρ s) (z * x)) μ := by
  -- Measurability of g · χ_s (from hg_int.aestronglyMeasurable and hΦ_meas)
  have hΦ_meas := repCharacter_leftmul_aestronglyMeasurable μ ι dims ρ hρ_meas s z
  have hgΦ_meas : AEStronglyMeasurable
      (fun x => (g x z : ℂ) * repCharacter (ρ s) (z * x)) μ :=
    (hg_int z).aestronglyMeasurable.mul hΦ_meas
  -- Dominating function: (dims s : ℝ) * ‖g‖ is integrable
  have hg : Integrable (fun x => (dims s : ℝ) * ‖(g x z : ℂ)‖) μ :=
    (Integrable.norm (hg_int z)).const_mul _
  -- Norm bound: ‖g · χ_s‖ ≤ dims s * ‖g‖, then apply Integrable.mono'
  refine Integrable.mono' hg hgΦ_meas ?_
  filter_upwards with x
  calc ‖(g x z : ℂ) * repCharacter (ρ s) (z * x)‖
      ≤ ‖(g x z : ℂ)‖ * ‖repCharacter (ρ s) (z * x)‖ := norm_mul_le _ _
    _ ≤ ‖(g x z : ℂ)‖ * (dims s : ℝ) := mul_le_mul_of_nonneg_left
        (repCharacter_norm_le_dim (ρ s) (hU s) (z * x)) (norm_nonneg _)
    _ = (dims s : ℝ) * ‖(g x z : ℂ)‖ := mul_comm _ _

#print axioms repCharacter_leftmul_integrable

/-! ## Step 5 (shared-variable): cascade kernel non-negativity with shared interface links

The transfer matrix has a shared interface structure: the spatial interface links
`z = u⁰_s` appear in both the positive and reflected-negative configs. After the
cascade (integrating out temporal links), the kernel has the form
  `K(x, y, z) = Σ_s c_s · χ_s(z * x) · conj(χ_s(z * y))`
where `c_s ≥ 0` is a CONSTANT (from Schur orthogonality, independent of z).

This matches `character_expansion_nonneg_shared` with `a(z, s) = c_s` (constant,
so `∀ z i, 0 ≤ a z i` is satisfied) and `Φ_s(z, x) = χ_s(z * x)`.

The crucial point: the cascade coefficient `c_s` is constant (from Schur
orthogonality `δ_{st} · (1/d_s)`), NOT depending on the shared variable `z`.
This is why `character_expansion_nonneg_shared` works where the non-shared
`character_expansion_nonneg` does not. See §8.11.78 of the design doc. -/

/-- **Step 5 (shared-variable): the cascade kernel with shared interface links
gives a non-negative integral.**

Given non-negative coefficients `c_s ≥ 0` (constant, independent of the shared
variable `z`) and a real-valued test function `g : G → G → ℝ` (where `g x z`
depends on the positive links `x` and the shared interface links `z`), the
integral of `g(x,z) · g(y,z)` against the shared-variable cascade kernel is
non-negative:
  `0 ≤ ∫_z ∫_x ∫_y g(x,z) · g(y,z) · Σ_s c_s · χ_s(z·x) · conj(χ_s(z·y))`

This follows from `character_expansion_nonneg_shared` with `a(z, s) = c_s`
(constant, so `∀ z i, 0 ≤ a z i`) and `Φ_s(z, x) = χ_s(z * x)`. The key point
is that the cascade coefficient `c_s` is constant (from Schur orthogonality),
NOT depending on the shared variable `z`. -/
lemma shared_cascade_factorization_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ)
    (c : ι → ℝ) (hc : ∀ s, 0 ≤ c s)
    (g : G → G → ℝ)
    (hg_meas : ∀ z, AEStronglyMeasurable (fun x => (g x z : ℂ)) μ)
    (hg_int : ∀ z, Integrable (fun x => (g x z : ℂ)) μ) :
    0 ≤ ∫ z, ∫ x, ∫ y, (g x z : ℂ) * (g y z : ℂ) *
      ∑ s, (c s : ℂ) * (repCharacter (ρ s) (z * x) * conj (repCharacter (ρ s) (z * y)))
      ∂μ ∂μ ∂μ := by
  -- Measurability of Φ_s(z, x) = χ_s(z * x) for each fixed z
  have hΦ_meas : ∀ s z, AEStronglyMeasurable (fun x => repCharacter (ρ s) (z * x)) μ :=
    fun s z => repCharacter_leftmul_aestronglyMeasurable μ ι dims ρ hρ_meas s z
  -- Integrability of g(x, z) · χ_s(z * x) for each fixed z, s
  have hgΦ_int : ∀ z s, Integrable (fun x => (g x z : ℂ) * repCharacter (ρ s) (z * x)) μ :=
    fun z s => repCharacter_leftmul_integrable μ ι dims ρ hU hρ_meas g hg_int s z
  -- Apply character_expansion_nonneg_shared with constant coefficient a(z, s) = c s
  exact character_expansion_nonneg_shared μ μ ι
    (fun _ s => c s) (fun _ s => hc s)
    (fun s z x => repCharacter (ρ s) (z * x)) g
    hΦ_meas hg_meas hgΦ_int
    (fun x y z => ∑ s, (c s : ℂ) *
      (repCharacter (ρ s) (z * x) * conj (repCharacter (ρ s) (z * y))))
    (fun x y z => by
      apply Finset.sum_congr rfl
      intro s _
      rfl)

#print axioms shared_cascade_factorization_nonneg

/-! ## Step 5 (shared-variable, conjugated form)

The cascade `luscher_2site_cascade_separable` (PositiveDefinite.lean) produces the
kernel `Σ_s c_s · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)`. When the shared interface link
appears in both the W and V configs (W₀ = V₀ = z), this becomes
`Σ_s c_s · conj(χ_s(z·x)) · χ_s(z·y)` (using `χ_s(x⁻¹·z⁻¹) = conj(χ_s(z·x))`).

This is the CONJUGATED form of the kernel in `shared_cascade_factorization_nonneg`.
The non-negativity still holds: apply `character_expansion_nonneg_shared` with
`Φ_s(z, x) = conj(χ_s(z·x))`. The measurability follows from
`AEStronglyMeasurable.star`, and the integrability bound is the same
(`‖conj(χ_s(g))‖ = ‖χ_s(g)‖ ≤ dims s`). -/

/-- **Step 5 (shared-variable, conjugated form): the cascade kernel with shared
interface links gives a non-negative integral (conjugated form).**

This is the variant of `shared_cascade_factorization_nonneg` for the conjugated
kernel `K(x, y, z) = Σ_s c_s · conj(χ_s(z·x)) · χ_s(z·y)`, which is the form
produced by `luscher_2site_cascade_separable` when the shared interface link
appears in both the W and V configs (W₀ = V₀ = z). -/
lemma shared_cascade_factorization_nonneg_conj
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ)
    (c : ι → ℝ) (hc : ∀ s, 0 ≤ c s)
    (g : G → G → ℝ)
    (hg_meas : ∀ z, AEStronglyMeasurable (fun x => (g x z : ℂ)) μ)
    (hg_int : ∀ z, Integrable (fun x => (g x z : ℂ)) μ) :
    0 ≤ ∫ z, ∫ x, ∫ y, (g x z : ℂ) * (g y z : ℂ) *
      ∑ s, (c s : ℂ) * (conj (repCharacter (ρ s) (z * x)) * repCharacter (ρ s) (z * y))
      ∂μ ∂μ ∂μ := by
  -- Measurability of Φ_s(z, x) = conj(χ_s(z * x)) for each fixed z
  have hΦ_meas : ∀ s z, AEStronglyMeasurable (fun x => conj (repCharacter (ρ s) (z * x))) μ :=
    fun s z => (repCharacter_leftmul_aestronglyMeasurable μ ι dims ρ hρ_meas s z).star
  -- Integrability of g(x, z) · conj(χ_s(z * x)) for each fixed z, s
  have hgΦ_int : ∀ z s, Integrable
      (fun x => (g x z : ℂ) * conj (repCharacter (ρ s) (z * x))) μ := by
    intro z s
    have hΦ_meas' := hΦ_meas s z
    have hgΦ_meas : AEStronglyMeasurable
        (fun x => (g x z : ℂ) * conj (repCharacter (ρ s) (z * x))) μ :=
      (hg_int z).aestronglyMeasurable.mul hΦ_meas'
    have hg : Integrable (fun x => (dims s : ℝ) * ‖(g x z : ℂ)‖) μ :=
      (Integrable.norm (hg_int z)).const_mul _
    refine Integrable.mono' hg hgΦ_meas ?_
    filter_upwards with x
    calc ‖(g x z : ℂ) * conj (repCharacter (ρ s) (z * x))‖
        ≤ ‖(g x z : ℂ)‖ * ‖conj (repCharacter (ρ s) (z * x))‖ := norm_mul_le _ _
      _ = ‖(g x z : ℂ)‖ * ‖repCharacter (ρ s) (z * x)‖ := by rw [Complex.norm_conj]
      _ ≤ ‖(g x z : ℂ)‖ * (dims s : ℝ) := mul_le_mul_of_nonneg_left
          (repCharacter_norm_le_dim (ρ s) (hU s) (z * x)) (norm_nonneg _)
      _ = (dims s : ℝ) * ‖(g x z : ℂ)‖ := mul_comm _ _
  -- Apply character_expansion_nonneg_shared with Φ_s(z, x) = conj(χ_s(z * x))
  exact character_expansion_nonneg_shared μ μ ι
    (fun _ s => c s) (fun _ s => hc s)
    (fun s z x => conj (repCharacter (ρ s) (z * x))) g
    hΦ_meas hg_meas hgΦ_int
    (fun x y z => ∑ s, (c s : ℂ) *
      (conj (repCharacter (ρ s) (z * x)) * repCharacter (ρ s) (z * y)))
    (fun x y z => by
      apply Finset.sum_congr rfl
      intro s _
      rw [Complex.conj_conj])

#print axioms shared_cascade_factorization_nonneg_conj

/-! ## Step 5: connecting the cascade result to the non-negativity kernel form

The cascade `luscher_2site_cascade_separable` (PositiveDefinite.lean) produces
`Σ_s F(s,s)·(1/d_s)² · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)`. When the shared interface
link appears in both W and V (W₀ = V₀ = z, W₁ = x, V₁ = y), this becomes
`Σ_s F(s,s)·(1/d_s)² · χ_s(x⁻¹·z⁻¹) · χ_s(z·y)`.

By `mul_inv`, `x⁻¹·z⁻¹ = (z·x)⁻¹`, and by `repCharacter_inv`,
`χ_s((z·x)⁻¹) = conj(χ_s(z·x))`. So the cascade result equals
`Σ_s c_s · conj(χ_s(z·x)) · χ_s(z·y)` with `c_s = F(s,s)·(1/d_s)² ≥ 0`,
which is exactly the `shared_cascade_factorization_nonneg_conj` kernel form.

This lemma makes the connection explicit. -/

/-- The 2-site cascade result (with shared interface link z) matches the
`shared_cascade_factorization_nonneg_conj` kernel form.

`χ_s(x⁻¹·z⁻¹) = χ_s((z·x)⁻¹) = conj(χ_s(z·x))` by `mul_inv` and `repCharacter_inv`. -/
lemma cascade_shared_kernel_form
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (F : ι → ι → ℝ)
    (z x y : G) :
    ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ)^2 *
      repCharacter (ρ s) (x⁻¹ * z⁻¹) * repCharacter (ρ s) (z * y)) =
    ∑ s, ((F s s * (1 / (dims s : ℝ))^2) : ℂ) *
      (conj (repCharacter (ρ s) (z * x)) * repCharacter (ρ s) (z * y)) := by
  apply Finset.sum_congr rfl
  intro s _
  -- χ_s(x⁻¹·z⁻¹) = χ_s((z·x)⁻¹) = conj(χ_s(z·x))
  -- In a general (non-abelian) group, (z * x)⁻¹ = x⁻¹ * z⁻¹  (mul_inv_rev).
  have hinv : repCharacter (ρ s) (x⁻¹ * z⁻¹) = conj (repCharacter (ρ s) (z * x)) := by
    rw [show x⁻¹ * z⁻¹ = (z * x)⁻¹ from (mul_inv_rev z x).symm,
        repCharacter_inv (ρ s) (hU s) (z * x)]
  rw [hinv]
  push_cast
  ring

#print axioms cascade_shared_kernel_form


end YangMills
