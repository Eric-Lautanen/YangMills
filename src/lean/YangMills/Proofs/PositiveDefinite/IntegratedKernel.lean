/-
# Positive Definite: Integrated Separable Kernel is PSD

This file formalizes the **provable core** of Step B.2e.2 of the
`transferMatrixPositivity_axiom` closure plan (§8.11.96 of
`docs/transfer_matrix_positivity_design.md`): the abstract lemma
"PD kernel from separable expansion + integration."

**Statement.**  If `φ` has a separable character expansion
`φ(x, t) = ∑_{w₁,w₂} F(w₁,w₂)·(∏_a χ_{w₁(a)}(x_a))·(∏_b χ_{w₂(b)}(t_b))` with
`F ≥ 0` (where `x` ranges over the "kept" links `A` and `t` over the
"integrated" links `B`), then the integrated kernel
`K(x, y) = ∫ φ(x, t)·conj(φ(y, t)) dμ(t)` is positive-semidefinite:
`∑_{x,y} c_x·conj(c_y)·K(x,y) ≥ 0`.

**Proof idea.**  Expand both factors, integrate over `B` by character
orthogonality (`∫ χ_a·conj(χ_b) = δ_{a,b}`, lemma
`integral_prod_repCharacter_conj` below), which forces `w₂ = w₂'`.  Grouping by
`w₂` gives `K(x,y) = ∑_{w₂} B_{w₂}(x)·conj(B_{w₂}(y))` — a sum of rank-1 PSD
kernels, hence PSD (a Gram matrix / sum of squares).

**IMPORTANT CAVEAT (§8.11.96, Findings 2–3).**  This abstract lemma is TRUE and
provable, but it is NOT by itself sufficient to close
`transferMatrixPositivity_axiom`.  Its kernel is the DOUBLE integral
`∫ φ(x,t)·conj(φ(y,t)) dμ(t)`; reflection positivity is the SINGLE integral
`∫ f(U)·f(θU)·K(U) dμ(U)` with the geometric reflection `θ`.  Bridging the two
requires resolving the `c' ≠ conj(c)` obstacle (the reflection pairs mode `w`
with its temporal-dual `w*`, breaking the naive rank-1 structure).  This file
isolates exactly the part that IS handled by the separable expansion +
character orthogonality, so the remaining work is sharply localized.

0 sorries.  Uses the `characterOrthogonality` axiom (via
`character_orthogonality_from_schur`); no new axioms.
-/

import YangMills.Proofs.PeterWeyl.TripleProduct

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Finset
open MeasureTheory
open Complex
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills

/-- **Paired character orthogonality for product measures.**  For irreducible
unitary representations `ρ` of a compact group with normalized Haar measure `μ`,
and two assignments `w w' : L → ι` of irrep labels to a finite link set `L`, the
integral of the product `∏_l χ_{w(l)}(x_l)·conj(χ_{w'(l)}(x_l))` over the product
Haar measure factors (Fubini) into a product of single-link character
orthogonality integrals, each of which is `δ_{w(l), w'(l)}`.  Hence the whole
integral is `1` if `w = w'` and `0` otherwise.

This is the paired analogue of `integral_prod_repCharacter_trivial` (which has
no `conj` and gives `δ_{w, trivial}`).  It is the key integration step in the
"integrated separable kernel is PSD" lemma. -/
lemma integral_prod_repCharacter_conj
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (L : Type) [Fintype L] [DecidableEq L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (w w' : L → ι) :
    ∫ x : L → G, ∏ l : L, (repCharacter (ρ (w l)) (x l) *
        conj (repCharacter (ρ (w' l)) (x l))) ∂(Measure.pi (fun _ => μ)) =
      ∏ l : L, (if w l = w' l then (1 : ℂ) else 0) := by
  -- Factor the integral using Fubini for finite products.
  rw [integral_fintype_prod_eq_prod
    (fun (l : L) (g : G) => repCharacter (ρ (w l)) g * conj (repCharacter (ρ (w' l)) g))]
  -- Each single-link integral: ∫ χ_{w(l)}·conj(χ_{w'(l)}) dμ = δ_{w(l), w'(l)}.
  refine Finset.prod_congr rfl (fun l _ => ?_)
  exact character_orthogonality_from_schur μ ι dims hDims ρ hU hIrr (w l) (w' l)

#print axioms integral_prod_repCharacter_conj

/-- **Integrated kernel is PSD (kernel of positive type).**  For any function
`φ : X → T → ℂ` and measure `μ` on `T`, the "integrated kernel"
`K(x, y) = ∫ φ(x, t)·conj(φ(y, t)) dμ(t)` is positive-semidefinite: for any
finite `s : Finset X` and coefficients `c : X → ℂ`,
`∑_{x∈s} ∑_{y∈s} c x·conj(c y)·K x y ≥ 0`.

The proof is the Gram-matrix / sum-of-squares argument: exchanging the finite
sum with the integral,
`∑_{x,y} c_x·conj(c_y)·K(x,y) = ∫ |∑_x c_x·φ(x,t)|² dμ(t) ≥ 0`.

**This is the general abstract fact** — it does NOT require `φ` to have a
character expansion or `F ≥ 0`.  Any "Gram / covariance" kernel
`∫ φ(x,t)·conj(φ(y,t)) dμ(t)` is PSD.  The character expansion
(`integral_prod_repCharacter_conj`) is what CONNECTS the transfer-matrix kernel
to this form; the PSD property itself is this lemma.

Hypothesis `hφ_int`: integrability of each product `φ x · conj(φ y)` (needed to
exchange the finite sum with the integral).  This holds automatically when `φ`
is continuous in `t` on a compact space with a finite measure (as for character
products). -/
lemma integrated_kernel_psd
    {X : Type*} {T : Type*} [MeasurableSpace T]
    (μ : Measure T)
    (φ : X → T → ℂ)
    (s : Finset X) (c : X → ℂ)
    (hφ_int : ∀ x ∈ s, ∀ y ∈ s, Integrable (fun t => φ x t * conj (φ y t)) μ) :
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) *
        (∫ t, φ x t * conj (φ y t) ∂μ) := by
  classical
  -- Each summand `c x · conj(c y) · (φ x · conj(φ y))` is integrable.
  have hterm_int : ∀ x ∈ s, ∀ y ∈ s,
      Integrable (fun t => c x * conj (c y) * (φ x t * conj (φ y t))) μ :=
    fun x hx y hy => (hφ_int x hx y hy).const_mul _
  -- Pointwise: the summed integrand is `(∑ c·φ) · conj(∑ c·φ)`.
  have hintegrand : ∀ t, (∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * (φ x t * conj (φ y t))) =
      (∑ x ∈ s, c x * φ x t) * conj (∑ y ∈ s, c y * φ y t) := by
    intro t
    rw [map_sum (starRingEnd ℂ) _ s, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    simp only [starRingEnd_apply, star_mul, star_star]
    ring
  -- Exchange the finite sum with the integral.
  have hexchange : (∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) *
        (∫ t, φ x t * conj (φ y t) ∂μ)) =
      ∫ t, (∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * (φ x t * conj (φ y t))) ∂μ := by
    rw [integral_finset_sum s (fun x hx =>
      integrable_finsetSum s (fun y hy => hterm_int x hx y hy))]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [integral_finset_sum s (fun y hy => hterm_int x hx y hy)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [integral_const_mul]
  -- The summed integrand equals `↑(normSq (∑ c·φ))`, a coerced nonneg real.
  have h2 : (∫ t, (∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * (φ x t * conj (φ y t))) ∂μ) =
      ((∫ t, Complex.normSq (∑ x ∈ s, c x * φ x t) ∂μ : ℝ) : ℂ) := by
    rw [show (fun t => ∑ x ∈ s, ∑ y ∈ s, c x * conj (c y) * (φ x t * conj (φ y t))) =
        fun t => ((Complex.normSq (∑ x ∈ s, c x * φ x t) : ℝ) : ℂ) from by
      funext t
      rw [hintegrand t, Complex.mul_conj]]
    exact integral_ofReal
  rw [hexchange, h2, Complex.zero_le_real]
  exact integral_nonneg (fun t => Complex.normSq_nonneg _)

#print axioms integrated_kernel_psd

end YangMills
