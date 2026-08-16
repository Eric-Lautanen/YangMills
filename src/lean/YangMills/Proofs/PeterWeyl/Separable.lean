/-
# Peter-Weyl: Separable Decomposition of Plaquette Boltzmann Products
-/

import YangMills.Proofs.PeterWeyl.CGDecomp

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
/-! ## Separable decomposition of the product of plaquette Boltzmann factors

The following is the key algebraic ingredient for sub-step (a) of the
`transferMatrixPositivity_axiom` closure plan (see
`docs/transfer_matrix_positivity_design.md`).  It shows that a product of
plaquette Boltzmann factors (each with inverted 3rd/4th links, as in the lattice
plaquette product) admits a **separable character decomposition** with
non-negative coefficients.

The proof combines:
1. The Peter-Weyl character expansion of each plaquette factor (axiom
   `hexp4`), with `repCharacter_inv` converting `χ(g⁻¹)` to `conj(χ(g))` for
   the inverted 3rd/4th links.
2. The product-of-sums expansion (distributive law): a product of finite sums
   equals a sum over choice functions of the product of the individual terms.
3. Per-term application of `charProduct_mixed_link_separable_decomp`: for each
   choice of expansion index per plaquette, the product of characters (some
   conjugated) grouped by link decomposes as a non-negative-weighted sum of
   products of single characters.
4. Summing over all choices: the total coefficient for each separable term is
   a sum of products of non-negative reals, hence non-negative.

This lemma is stated abstractly (parameterized by a finite plaquette type `P`,
a finite link type `L`, and a link assignment `links : P → Fin 4 → L`) so that
it can be instantiated for the concrete interface plaquette structure later.
-/

/-- Convert a 5-fold nested `Fintype` sum to a single sum over the
right-nested product type `ι × ι × ι × ι × ι`.  This is `Fintype.sum_prod_type`
applied four times, from innermost to outermost. -/
lemma sum_fin5_to_single {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ι → ℂ) :
    ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι, f r s t u v =
    ∑ idx : ι × ι × ι × ι × ι,
      f idx.1 idx.2.1 idx.2.2.1 idx.2.2.2.1 idx.2.2.2.2 := by
  simp only [Fintype.sum_prod_type]

/-- Convert `∏ j : Fin 4, f j` to the explicit 4-fold product `f 0 * f 1 * f 2 * f 3`. -/
lemma fin4_prod_eq (f : Fin 4 → ℂ) :
    ∏ j : Fin 4, f j = f 0 * f 1 * f 2 * f 3 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp
  ring

/-- Extract the character index for link position `j` from a Peter-Weyl
expansion index `(r, s, t, u, v)`.  Position 0 → `s`, 1 → `t`, 2 → `u`, 3 → `v`.
(The `r` component is the Peter-Weyl heat-kernel expansion index and does not
correspond to a link.) -/
def pwCharIdx {ι : Type*} (idx : ι × ι × ι × ι × ι) (j : Fin 4) : ι :=
  match j with
  | 0 => idx.2.1
  | 1 => idx.2.2.1
  | 2 => idx.2.2.2.1
  | 3 => idx.2.2.2.2

/-- Conjugation flag for link position `j` in the plaquette product: `true`
for positions 2 and 3 (the inverted links `g₃⁻¹, g₄⁻¹`). -/
def pwIsConj (j : Fin 4) : Bool :=
  match j with
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true

/-- **Character expansion of a single plaquette Boltzmann factor with inverted
3rd/4th links.**  For `c ≥ 0`, the function
`exp(c · Re Tr(g₁ · g₂ · g₃⁻¹ · g₄⁻¹))` expands as a 5-fold sum over
Peter-Weyl indices `(r, s, t, u, v)` of `coeff(r,s,t,u,v) · χ_s(g₁) · χ_t(g₂) ·
conj(χ_u(g₃)) · conj(χ_v(g₄))`, with `conj` arising from `repCharacter_inv`
applied to the inverted links `g₃⁻¹, g₄⁻¹`. -/
lemma plaquette_factor_char_expansion
    {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (coeff : ι → ι → ι → ι → ι → ℝ)
    (c : ℝ)
    (hexp4 : ∀ g₁ g₂ g₃ g₄ : SU N,
      (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃ * g₄ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
          (coeff r s t u v : ℂ) *
          (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
           repCharacter (ρ u) g₃ * repCharacter (ρ v) g₄))
    (g₁ g₂ g₃ g₄ : SU N) :
    (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃⁻¹ * g₄⁻¹ : SU N) :
        Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
      ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) *
        (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
         conj (repCharacter (ρ u) g₃) * conj (repCharacter (ρ v) g₄)) := by
  rw [hexp4 g₁ g₂ g₃⁻¹ g₄⁻¹]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun s _ => ?_)
  refine Finset.sum_congr rfl (fun t _ => ?_)
  refine Finset.sum_congr rfl (fun u _ => ?_)
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [repCharacter_inv (ρ u) (hU u) g₃, repCharacter_inv (ρ v) (hU v) g₄]

/-- **Single-index character expansion of a plaquette Boltzmann factor.**

For `c ≥ 0`, the plaquette Boltzmann factor `exp(c · Re Tr(g₁ · g₂ · g₃⁻¹ · g₄⁻¹))`
expands as a single-index sum over characters of the plaquette product:

    exp(c · Re Tr(g₁ · g₂ · g₃⁻¹ · g₄⁻¹)) = ∑_s c'_s · χ_s(g₁ · g₂ · g₃⁻¹ · g₄⁻¹)

with `c'_s ≥ 0`.  This is derived from the 5-index expansion `hexp4` by setting
three of the four links to the identity: `χ_t(1) = dim(t)`, so
`c'_s = ∑_{r,t,u,v} coeff(r,s,t,u,v) · dim(t) · dim(u) · dim(v) ≥ 0`.

This is the key bridge between the 5-index expansion (characters at individual links)
and the Lüscher cascade (which operates on characters at plaquette products).
See `docs/transfer_matrix_positivity_design.md` §8.11.44 for the analysis. -/
lemma plaquette_boltzmann_single_char_expansion
    {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (coeff : ι → ι → ι → ι → ι → ℝ) (hcoeff : ∀ r s t u v, 0 ≤ coeff r s t u v)
    (c : ℝ)
    (hexp4 : ∀ g₁ g₂ g₃ g₄ : SU N,
      (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃ * g₄ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
          (coeff r s t u v : ℂ) *
          (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
           repCharacter (ρ u) g₃ * repCharacter (ρ v) g₄))
    (g₁ g₂ g₃ g₄ : SU N) :
    ∃ (c' : ι → ℝ) (hc' : ∀ s, 0 ≤ c' s),
      (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃⁻¹ * g₄⁻¹ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ s : ι, (c' s : ℂ) * repCharacter (ρ s) (g₁ * g₂ * g₃⁻¹ * g₄⁻¹) := by
  -- Character at identity = dimension: χ_i(1) = Tr(ρ_i(1)) = Tr(I_{d_i}) = d_i
  have h_char_one : ∀ i, repCharacter (ρ i) 1 = (dims i : ℂ) := by
    intro i
    show Matrix.trace (ρ i 1) = (dims i : ℂ)
    rw [MonoidHom.map_one, Matrix.trace_one, Fintype.card_fin]
  -- Define c'_s = ∑_{r,t,u,v} coeff(r,s,t,u,v) · dim(t) · dim(u) · dim(v) ≥ 0
  refine ⟨fun s => ∑ r, ∑ t, ∑ u, ∑ v, coeff r s t u v * dims t * dims u * dims v, ?_, ?_⟩
  · -- Non-negativity: each term coeff ≥ 0, dims ≥ 0 (ℕ), product ≥ 0
    intro s
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
      Finset.sum_nonneg (fun v _ => mul_nonneg (mul_nonneg (mul_nonneg
        (hcoeff r s t u v) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))))
  · -- Equality: apply hexp4 with plaquette product and three identities
    have h := hexp4 (g₁ * g₂ * g₃⁻¹ * g₄⁻¹) 1 1 1
    -- Simplify LHS: (g₁ * g₂ * g₃⁻¹ * g₄⁻¹) * 1 * 1 * 1 = g₁ * g₂ * g₃⁻¹ * g₄⁻¹
    simp only [mul_one] at h
    -- Simplify RHS: χ_t(1) = dims t, χ_u(1) = dims u, χ_v(1) = dims v
    simp only [h_char_one] at h
    -- Now h : exp(c·Re Tr(g₁·g₂·g₃⁻¹·g₄⁻¹)) = ∑ r s t u v, coeff·χ_s(g)·(dims t)·(dims u)·(dims v)
    -- Goal: exp(...) = ∑ s, (c' s : ℂ) · χ_s(g)
    rw [h, Finset.sum_comm]
    -- Goal: ∑ s, ∑ r t u v, coeff·χ_s(g)·dims_t·dims_u·dims_v = ∑ s, (c' s : ℂ)·χ_s(g)
    refine Finset.sum_congr rfl (fun s hs => ?_)
    -- Goal: ∑ r t u v, (coeff : ℂ)·(χ_s(g)·(dims t : ℂ)·(dims u : ℂ)·(dims v : ℂ)) = (c' s : ℂ)·χ_s(g)
    -- Rearrange each summand to put χ_s(g) on the right, then factor it out
    have h_rearr : ∀ r t u v,
        (coeff r s t u v : ℂ) * (repCharacter (ρ s) (g₁ * g₂ * g₃⁻¹ * g₄⁻¹) *
          (dims t : ℂ) * (dims u : ℂ) * (dims v : ℂ)) =
        ((coeff r s t u v * dims t * dims u * dims v : ℝ) : ℂ) *
          repCharacter (ρ s) (g₁ * g₂ * g₃⁻¹ * g₄⁻¹) := by
      intro r t u v
      push_cast
      ring
    -- Apply the rearrangement to each summand
    rw [Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ =>
        Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => h_rearr r t u v))))]
    -- Factor out χ_s(g) (constant w.r.t. r,t,u,v) from each sum level
    simp only [← Finset.sum_mul]
    -- Now: (∑ r t u v, ((coeff·dims_t·dims_u·dims_v : ℝ) : ℂ)) · χ_s(g) = (c' s : ℂ) · χ_s(g)
    congr 1
    -- ∑ r t u v, ((coeff·dims_t·dims_u·dims_v : ℝ) : ℂ) = (c' s : ℂ) by ofReal_sum + def of c'
    simp only [Complex.ofReal_sum]

#print axioms plaquette_boltzmann_single_char_expansion

/-- **Uniform single-character expansion of the plaquette Boltzmann factor
(full Peter-Weyl package).**

For `c ≥ 0`, the function `g ↦ exp(c · Re Tr(g))` on `SU(N)` admits a finite
character expansion
    exp(c · Re Tr(g)) = Σ_s coeff_s · χ_s(g)     (for ALL g : SU N)
with `coeff_s ≥ 0`, together with the full Peter-Weyl / Clebsch-Gordan package
(`ι`, `dims`, `ρ`, `hU`, `hMeas`, `hIrr`, `hDims`).

This is the **uniform** (`∀ g`) version of `plaquette_boltzmann_single_char_expansion`
(which is parametric in the expansion data and concludes for a specific plaquette
product).  It is derived from `peterWeyl_clebschGordan_plaquette` Part 1 by setting
`g₂ = g₃ = g₄ = 1`, using `χ_i(1) = dims(i)`, and collecting the `s`-index.  The
coefficient is `coeff_s = Σ_{r,t,u,v} coeff(r,s,t,u,v) · dims(t) · dims(u) · dims(v)`,
which is non-negative and INDEPENDENT of `g` (so the same `coeff` works for all `g`).

This is the key input for the **plaquette-level interface expansion** (STEP 5): it
provides the `hexp1 : ∀ g, exp(c·Re Tr(g)) = Σ_s coeff_s · χ_s(g)` hypothesis needed
by `plaquette_product_single_char_decomp`, which expands the product of interface
plaquette Boltzmann factors as `Σ_{w : P → ι} F(w) · ∏_p χ_{w(p)}(plaquetteProduct p)`
with `F(w) ≥ 0` — one character per PLAQUETTE (not per link).  At the plaquette level,
each temporal link appears in two plaquette characters, so the Lüscher cascade forces
matching (not triviality), producing constant non-negative coefficients — exactly the
`a(z, i) = c_i ≥ 0` structure required by `character_expansion_nonneg_shared`. -/
lemma plaquette_boltzmann_character_expansion_single (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (hIrr : ∀ i, IsIrreducible (ρ i))
      (hDims : ∀ i, 0 < dims i)
      (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s),
      ∀ (g : SU N),
      (Real.exp (c * (Matrix.trace ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ s : ι, (coeff s : ℂ) * repCharacter (ρ s) g := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, σ_0, hσ_0_dims, hσ_0_trivial, coeff4, hcoeff4, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary, hcgME_cross_rep,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ,
      cgMEΛ, hcgMEΛ_support, hexp4, hL2, hSchurΛ, hcgMEΛ_parts⟩ :=
    peterWeyl_clebschGordan_plaquette N c hc
  letI : Fintype ι := hι
  -- Character at identity = dimension: χ_i(1) = Tr(ρ_i(1)) = Tr(I_{d_i}) = d_i
  have hchar_one : ∀ i, repCharacter (ρ i) 1 = (dims i : ℂ) := by
    intro i
    show Matrix.trace (ρ i 1) = (dims i : ℂ)
    rw [MonoidHom.map_one, Matrix.trace_one, Fintype.card_fin]
  -- Single coefficient: coeff_single s = Σ_{r,t,u,v} coeff4(r,s,t,u,v)·dims(t)·dims(u)·dims(v)
  refine ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims,
      (fun s => ∑ r, ∑ t, ∑ u, ∑ v, coeff4 r s t u v * dims t * dims u * dims v),
      fun s => ?_, fun g => ?_⟩
  · -- Non-negativity: each term coeff4 ≥ 0, dims ≥ 0 (ℕ), product ≥ 0
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
      Finset.sum_nonneg (fun v _ => mul_nonneg (mul_nonneg (mul_nonneg
        (hcoeff4 r s t u v) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))))
  · -- Equality: apply hexp4 with g and three identities
    have h := hexp4 g 1 1 1
    -- LHS: g * 1 * 1 * 1 = g
    simp only [mul_one] at h
    -- RHS: χ_t(1) = dims t, χ_u(1) = dims u, χ_v(1) = dims v
    simp only [hchar_one] at h
    -- h : exp(c·Re Tr(g)) = Σ_r Σ_s Σ_t Σ_u Σ_v, coeff4·χ_s(g)·(dims t)·(dims u)·(dims v)
    -- Goal: exp(c·Re Tr(g)) = Σ_s, (coeff_single s : ℂ) · χ_s(g)
    rw [h, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    -- Rearrange each summand to put χ_s(g) on the right, then factor it out
    have h_rearr : ∀ r t u v,
        (coeff4 r s t u v : ℂ) * (repCharacter (ρ s) g *
          (dims t : ℂ) * (dims u : ℂ) * (dims v : ℂ)) =
        ((coeff4 r s t u v * dims t * dims u * dims v : ℝ) : ℂ) *
          repCharacter (ρ s) g := by
      intro r t u v
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ =>
        Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => h_rearr r t u v))))]
    simp only [← Finset.sum_mul]
    congr 1
    simp only [Complex.ofReal_sum]

#print axioms plaquette_boltzmann_character_expansion_single

/-- **Multi-plaquette single-index character expansion (product-of-sums).**

Given a single-index character expansion `exp(c·Re Tr(g)) = ∑_s c'_s · χ_s(g)` with
`c'_s ≥ 0` (e.g. from `plaquette_boltzmann_single_char_expansion`), and a finite type `P`
of plaquettes with plaquette products `gP : P → SU N`, the product of plaquette Boltzmann
factors expands as

    ∏_p exp(c·Re Tr(gP p)) = ∑_{w : P → ι} F(w) · ∏_p χ_{w(p)}(gP p)

with `F(w) = ∏_p c'_{w(p)} ≥ 0`.  This is the product-of-sums identity (`Fintype.prod_sum`
+ `Finset.prod_mul_distrib`) applied to the single-index expansion.  Each character
`χ_{w(p)}(gP p)` is evaluated at the plaquette product `gP p = g₁·g₂·g₃⁻¹·g₄⁻¹`, which
is the form the Lüscher cascade operates on.  See `docs/transfer_matrix_positivity_design.md`
§8.11.45. -/
lemma plaquette_product_single_char_decomp
    {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (c' : ι → ℝ) (hc' : ∀ s, 0 ≤ c' s)
    (c : ℝ)
    (hexp1 : ∀ g : SU N,
      (Real.exp (c * (Matrix.trace ((g : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ s : ι, (c' s : ℂ) * repCharacter (ρ s) g)
    (P : Type*) [Fintype P] [DecidableEq P]
    (gP : P → SU N) :
    ∃ (F : (P → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      (∏ p : P, (Real.exp (c * (Matrix.trace ((gP p) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) =
        ∑ w : P → ι, (F w : ℂ) * ∏ p : P, repCharacter (ρ (w p)) (gP p) := by
  refine ⟨fun w => ∏ p : P, c' (w p), fun w => Finset.prod_nonneg (fun p _ => hc' (w p)), ?_⟩
  -- Step 1: rewrite each factor using hexp1
  rw [Finset.prod_congr rfl (fun p _ => hexp1 (gP p))]
  -- Step 2: product of sums = sum of products
  rw [Fintype.prod_sum (fun p s => (c' s : ℂ) * repCharacter (ρ s) (gP p))]
  -- Step 3: split each product (c' · χ) into (∏ c') · (∏ χ) via prod_mul_distrib
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib]
  -- Rewrite ↑(∏ c') to ∏ ↑(c') via Complex.ofReal_prod, then ring handles commutativity
  simp only [Complex.ofReal_prod]

#print axioms plaquette_product_single_char_decomp

/-- **Separable decomposition of the product of plaquette Boltzmann factors.**

Given the Peter-Weyl / Clebsch-Gordan axiom data, a finite type `P` of
plaquettes, a finite type `L` of links, a surjective link assignment
`links : P → Fin 4 → L` (every link appears in at least one plaquette), and
link variables `g : L → SU N`, the product of plaquette Boltzmann factors

    ∏_{p ∈ P} exp(c · Re Tr(g₁ · g₂ · g₃⁻¹ · g₄⁻¹))

(where `g_i = g(links p i)`) decomposes as a **separable character
decomposition**

    ∑_{w : L → ι} F(w) · ∏_{l ∈ L} χ_{w(l)}(g_l)

with `F(w) ≥ 0`.

This is the key algebraic ingredient for the interface Boltzmann factor
decomposition (sub-step (a) of the `transferMatrixPositivity_axiom` closure
plan).  The proof combines the Peter-Weyl character expansion of each
plaquette factor, the product-of-sums distributive expansion, per-term
application of `charProduct_mixed_link_separable_decomp` (using the dual map
to handle inverted links), and summation of non-negative coefficients.

See `docs/transfer_matrix_positivity_design.md` for the full plan. -/
lemma plaquette_product_separable_decomp
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (coeff : ι → ι → ι → ι → ι → ℝ) (hcoeff : ∀ r s t u v, 0 ≤ coeff r s t u v)
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (c : ℝ) (hc : 0 ≤ c)
    (hexp4 : ∀ g₁ g₂ g₃ g₄ : SU N,
      (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃ * g₄ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
          (coeff r s t u v : ℂ) *
          (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
           repCharacter (ρ u) g₃ * repCharacter (ρ v) g₄))
    (P : Type*) [Fintype P] [DecidableEq P]
    (L : Type*) [Fintype L] [DecidableEq L]
    (links : P → Fin 4 → L)
    (hlinks_surj : ∀ l, ∃ p j, links p j = l) :
    ∃ (F : (L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (g : L → SU N),
      (∏ p : P, (Real.exp (c * (Matrix.trace
          ((g (links p 0) * g (links p 1) * (g (links p 2))⁻¹ *
           (g (links p 3))⁻¹ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) =
        ∑ w : L → ι, (F w : ℂ) * ∏ l : L, repCharacter (ρ (w l)) (g l) := by
  classical
  -- Define the link partition: S l = {(p,j) : links p j = l}
  let S : L → Finset (P × Fin 4) := fun l =>
    (Finset.univ : Finset (P × Fin 4)).filter (fun x => links x.1 x.2 = l)
  -- S l is nonempty (surjectivity of links)
  have hS_nonempty : ∀ l, (S l).Nonempty := by
    intro l
    obtain ⟨p, j, hj⟩ := hlinks_surj l
    refine ⟨(p, j), ?_⟩
    show (p, j) ∈ (Finset.univ : Finset (P × Fin 4)).filter (fun x => links x.1 x.2 = l)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  -- S l are pairwise disjoint
  have hS_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset L)) S := by
    intro l _ m _ hlm
    refine Finset.disjoint_left.mpr (fun x hx => ?_)
    obtain ⟨p, j⟩ := x
    intro h
    have hx2 := Finset.mem_filter.1 hx
    have h2 := Finset.mem_filter.1 h
    have hxl : links p j = l := hx2.2
    have hxm : links p j = m := h2.2
    rw [hxl] at hxm
    exact hlm hxm
  -- biUnion S = univ
  have hS_biUnion : (Finset.univ : Finset L).biUnion S = Finset.univ := by
    ext x
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      obtain ⟨p, j, hj⟩ := hlinks_surj (links x.1 x.2)
      rw [Finset.mem_biUnion]
      refine ⟨links p j, Finset.mem_univ _, ?_⟩
      show x ∈ (Finset.univ : Finset (P × Fin 4)).filter (fun x => links x.1 x.2 = links p j)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.symm⟩
  -- Per-α separable decomposition via charProduct_mixed_link_separable_decomp
  have hdecomp_α : ∀ (α : P → ι × ι × ι × ι × ι),
      ∃ (F : (L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
        ∀ (g : L → SU N),
          (∏ l, ∏ a ∈ S l,
            (if pwIsConj a.2 then conj (repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l))
             else repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l))) =
          ∑ w : L → ι, (F w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l) := by
    intro α
    exact charProduct_mixed_link_separable_decomp ρ hU cg hcg hcg_decomp dual hdual
      S (fun _ a => pwCharIdx (α a.1) a.2) (fun _ a => pwIsConj a.2) hS_nonempty
  let F_α : (P → ι × ι × ι × ι × ι) → (L → ι) → ℝ := fun α => (hdecomp_α α).choose
  have hF_α : ∀ α w, 0 ≤ F_α α w := fun α w => (hdecomp_α α).choose_spec.choose w
  have hF_α_decomp : ∀ α (g : L → SU N),
      (∏ l, ∏ a ∈ S l,
        (if pwIsConj a.2 then conj (repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l))
         else repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l))) =
      ∑ w : L → ι, (F_α α w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l) :=
    fun α g => (hdecomp_α α).choose_spec.choose_spec g
  -- Coefficient extraction helper
  let coeffIdx (idx : ι × ι × ι × ι × ι) : ℝ :=
    coeff idx.1 idx.2.1 idx.2.2.1 idx.2.2.2.1 idx.2.2.2.2
  have hcoeffIdx : ∀ idx, 0 ≤ coeffIdx idx := fun idx =>
    hcoeff idx.1 idx.2.1 idx.2.2.1 idx.2.2.2.1 idx.2.2.2.2
  -- Product of sums = sum of products (Stage 2)
  -- Define the overall coefficient F(w) = ∑ α, (∏ p, coeffIdx (α p)) * F_α α w
  refine ⟨fun w => ∑ α : P → ι × ι × ι × ι × ι,
            (∏ p : P, coeffIdx (α p)) * F_α α w,
          fun w => ?_, fun g => ?_⟩
  · -- Non-negativity: F(w) = ∑ α, (∏ p, coeffIdx (α p)) * F_α α w ≥ 0
    exact Finset.sum_nonneg (fun α _ => mul_nonneg
      (Finset.prod_nonneg (fun p _ => hcoeffIdx (α p)))
      (hF_α α w))
  · -- Equality: ∏ p, exp(...) = ∑ w, (F w : ℂ) * ∏ l, χ_{w(l)}(g_l)
    -- The explicit 4-fold character product for plaquette p with expansion index idx
    let charProd (p : P) (idx : ι × ι × ι × ι × ι) : ℂ :=
      repCharacter (ρ idx.2.1) (g (links p 0)) * repCharacter (ρ idx.2.2.1) (g (links p 1)) *
      conj (repCharacter (ρ idx.2.2.2.1) (g (links p 2))) *
      conj (repCharacter (ρ idx.2.2.2.2) (g (links p 3)))
    -- charProd = ∏_j form (Fin 4 enumeration)
    have h_charProd_fin4 : ∀ p idx,
        charProd p idx =
        ∏ j : Fin 4, (if pwIsConj j then conj (repCharacter (ρ (pwCharIdx idx j)) (g (links p j)))
                       else repCharacter (ρ (pwCharIdx idx j)) (g (links p j))) := by
      intro p idx
      rw [fin4_prod_eq]
      show charProd p idx =
        repCharacter (ρ (pwCharIdx idx 0)) (g (links p 0)) *
        repCharacter (ρ (pwCharIdx idx 1)) (g (links p 1)) *
        (if pwIsConj 2 then conj (repCharacter (ρ (pwCharIdx idx 2)) (g (links p 2)))
         else repCharacter (ρ (pwCharIdx idx 2)) (g (links p 2))) *
        (if pwIsConj 3 then conj (repCharacter (ρ (pwCharIdx idx 3)) (g (links p 3)))
         else repCharacter (ρ (pwCharIdx idx 3)) (g (links p 3)))
      simp [pwCharIdx, pwIsConj, charProd]
    -- Per-plaquette expansion: exp(...) = ∑ idx, (coeffIdx idx : ℂ) * charProd p idx
    have h_plaq_exp : ∀ p,
        (Real.exp (c * (Matrix.trace
            ((g (links p 0) * g (links p 1) * (g (links p 2))⁻¹ *
             (g (links p 3))⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ idx : ι × ι × ι × ι × ι, (coeffIdx idx : ℂ) * charProd p idx := by
      intro p
      have h := plaquette_factor_char_expansion ρ hU coeff c hexp4
        (g (links p 0)) (g (links p 1)) (g (links p 2)) (g (links p 3))
      rw [h, sum_fin5_to_single]
    -- Regroup by link: ∏ p, charProd p (α p) = ∏ l, ∏ a ∈ S l, (...) (Stage 3+4)
    have h_regroup : ∀ (α : P → ι × ι × ι × ι × ι),
        ∏ p : P, charProd p (α p) =
        ∏ l : L, ∏ a ∈ S l,
          (if pwIsConj a.2 then conj (repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l))
           else repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l)) := by
      intro α
      -- Step a: charProd p (α p) = ∏_j form
      have h1 : ∏ p : P, charProd p (α p) =
          ∏ p : P, ∏ j : Fin 4,
            (if pwIsConj j then conj (repCharacter (ρ (pwCharIdx (α p) j)) (g (links p j)))
             else repCharacter (ρ (pwCharIdx (α p) j)) (g (links p j))) := by
        refine Finset.prod_congr rfl (fun p _ => h_charProd_fin4 p (α p))
      -- Step b: ∏ p, ∏ j = ∏ (p,j) : P × Fin 4
      have h2 : ∏ p : P, ∏ j : Fin 4,
            (if pwIsConj j then conj (repCharacter (ρ (pwCharIdx (α p) j)) (g (links p j)))
             else repCharacter (ρ (pwCharIdx (α p) j)) (g (links p j))) =
          ∏ x : P × Fin 4,
            (if pwIsConj x.2 then conj (repCharacter (ρ (pwCharIdx (α x.1) x.2)) (g (links x.1 x.2)))
             else repCharacter (ρ (pwCharIdx (α x.1) x.2)) (g (links x.1 x.2))) := by
        exact (Fintype.prod_prod_type' (fun p j =>
          (if pwIsConj j then conj (repCharacter (ρ (pwCharIdx (α p) j)) (g (links p j)))
           else repCharacter (ρ (pwCharIdx (α p) j)) (g (links p j))))).symm
      -- Step c: ∏ (p,j) = ∏ l, ∏ a ∈ S l
      have h3 : ∏ x : P × Fin 4,
            (if pwIsConj x.2 then conj (repCharacter (ρ (pwCharIdx (α x.1) x.2)) (g (links x.1 x.2)))
             else repCharacter (ρ (pwCharIdx (α x.1) x.2)) (g (links x.1 x.2))) =
          ∏ l : L, ∏ a ∈ S l,
            (if pwIsConj a.2 then conj (repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l))
             else repCharacter (ρ (pwCharIdx (α a.1) a.2)) (g l)) := by
        rw [← hS_biUnion, Finset.prod_biUnion hS_disj]
        refine Finset.prod_congr rfl (fun l _ => ?_)
        refine Finset.prod_congr rfl (fun a ha => ?_)
        have ha' : links a.1 a.2 = l := (Finset.mem_filter.1 ha).2
        rw [ha']
      rw [h1, h2, h3]
    -- Step 1: per-plaquette expansion
    rw [show (∏ p : P, (Real.exp (c * (Matrix.trace
        ((g (links p 0) * g (links p 1) * (g (links p 2))⁻¹ *
         (g (links p 3))⁻¹ : SU N) :
        Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) =
      ∏ p : P, ∑ idx, (coeffIdx idx : ℂ) * charProd p idx from
      Finset.prod_congr rfl (fun p _ => h_plaq_exp p)]
    -- Step 2: product of sums = sum of products (Fintype.prod_sum)
    rw [Fintype.prod_sum (fun p idx => (coeffIdx idx : ℂ) * charProd p idx)]
    -- Per-α: split product + regroup by link + separable decomposition
    have h_per_α : ∀ (α : P → ι × ι × ι × ι × ι),
        ∏ p : P, (coeffIdx (α p) : ℂ) * charProd p (α p) =
        (∏ p : P, (coeffIdx (α p) : ℂ)) *
        ∑ w : L → ι, (F_α α w : ℂ) * ∏ l : L, repCharacter (ρ (w l)) (g l) := by
      intro α
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [h_regroup α, hF_α_decomp α g]
    -- Apply per-α transformation
    simp only [h_per_α]
    -- Stage 5: sum and collect
    -- Step 1: distribute product over inner sum
    have h1 : (∑ α, (∏ p, (coeffIdx (α p) : ℂ)) *
        ∑ w, (F_α α w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l)) =
        ∑ α, ∑ w, (∏ p, (coeffIdx (α p) : ℂ)) *
          ((F_α α w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l)) := by
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [Finset.mul_sum]
    -- Step 2: exchange sums
    have h2 : (∑ α, ∑ w, (∏ p, (coeffIdx (α p) : ℂ)) *
          ((F_α α w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l))) =
        ∑ w, ∑ α, (∏ p, (coeffIdx (α p) : ℂ)) *
          ((F_α α w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l)) := by
      exact Finset.sum_comm
    -- Step 3: factor out ∏ l, χ_{w(l)}(g_l)
    have h3 : (∑ w, ∑ α, (∏ p, (coeffIdx (α p) : ℂ)) *
          ((F_α α w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l))) =
        ∑ w, (∑ α, (∏ p, (coeffIdx (α p) : ℂ)) * (F_α α w : ℂ)) *
          ∏ l, repCharacter (ρ (w l)) (g l) := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      ring
    -- Combine: after h1, h2, h3 the LHS is ∑ w, (∑ α, (∏ p, ↑coeff) * ↑F_α) * ∏ l, χ
    -- and the RHS is ∑ w, (F w : ℂ) * ∏ l, χ where F w beta-reduces to
    -- ∑ α, (∏ p, coeffIdx (α p)) * F_α α w.  The coercion (F w : ℂ) = ↑(∑ α, ...)
    -- unfolds via Complex.ofReal_sum/mul/prod to match the distributed LHS.
    rw [h1, h2, h3]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]

/-- **V⁺ conjugation via the dual map.** For a product of characters
`∏_l χ_{w(l)}(g_l)` over a finite link set `L`, and a Finset `L_V` of "V⁺
links", the product can be rewritten as

    (∏_{l ∉ L_V} χ_{w(l)}(g_l)) · conj(∏_{l ∈ L_V} χ_{dual(w(l))}(g_l))

using the dual (contragredient) map: `χ_i(g) = conj(χ_{dual(i)}(g))` (from
`hdual` + `conj_conj`).  This is the key identity that separates the V⁺
links (which appear with conjugated characters after the reflection/change of
variables) from the U⁺ and u⁰ links (which appear with unconjugated
characters).  See `docs/transfer_matrix_positivity_design.md` §8.1. -/
lemma prod_conj_partition_dual
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (L : Type*) [Fintype L] [DecidableEq L]
    (L_V : Finset L)
    (w : L → ι) (g : L → SU N) :
    ∏ l : L, repCharacter (ρ (w l)) (g l) =
    (∏ l ∈ (Finset.univ : Finset L) \ L_V, repCharacter (ρ (w l)) (g l)) *
    conj (∏ l ∈ L_V, repCharacter (ρ (dual (w l))) (g l)) := by
  -- `conj` distributes over the `L_V` product, and `χ_{dual i} = conj(χ_i)` (hdual)
  -- turns each conjugated dual character back into the original character.
  have h_conj : conj (∏ l ∈ L_V, repCharacter (ρ (dual (w l))) (g l)) =
      ∏ l ∈ L_V, repCharacter (ρ (w l)) (g l) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun l hl => by rw [hdual, Complex.conj_conj]
  -- `univ` is the disjoint union of `univ \ L_V` and `L_V`.
  have h_disj : Disjoint ((Finset.univ : Finset L) \ L_V) L_V :=
    Finset.disjoint_left.mpr fun _ ha => (Finset.mem_sdiff.mp ha).2
  have h_eq : ((Finset.univ : Finset L) \ L_V) ∪ L_V = Finset.univ := by
    ext x; simp
  rw [h_conj, ← Finset.prod_union h_disj, h_eq]

#print axioms prod_conj_partition_dual
#print axioms plaquetteBoltzmannPD_inv
#print axioms charProduct_PD
#print axioms plaquette_product_separable_decomp

/-- **Interface kernel character expansion (separable form).** Given a product of
plaquette Boltzmann factors `∏_p exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` over a finite set of
interface plaquettes (with `c ≥ 0`), and a partition of the link set `L` into three
disjoint Finsets `L_U` (positive-time "U⁺" links), `L_0` (interface "u⁰" links), and
`L_V` (the "V⁺" links that appear conjugated after the reflection / change of
variables), the product admits the *separable* character expansion

    ∏_p exp(c·Re Tr(…)) = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))

with `F(w) ≥ 0`, where `Φ_w(U⁺) = ∏_{l ∈ L_U} χ_{w(l)}(g_l)`,
`Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(g_l)`, and the V⁺ factor uses the dual
(contragredient) map: `conj(Φ_w(V⁺)) = conj(∏_{l ∈ L_V} χ_{dual(w(l))}(g_l))`.

This is the key input to the reflection-positivity argument (§8.1 of
`docs/transfer_matrix_positivity_design.md`): the V⁺ links always appear with
conjugated characters, so the kernel factors as a positive-coefficient sum of
separated U⁺/u⁰/V⁺ character products. The proof composes
`plaquette_product_separable_decomp` (which gives `∑_w F(w)·∏_l χ_{w(l)}(g_l)`)
with `prod_conj_partition_dual` (which separates the V⁺ links with conjugated
dual characters) and the disjoint union split `univ \ L_V = L_U ∪ L_0`. -/
lemma interface_kernel_character_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (coeff : ι → ι → ι → ι → ι → ℝ) (hcoeff : ∀ r s t u v, 0 ≤ coeff r s t u v)
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (c : ℝ) (hc : 0 ≤ c)
    (hexp4 : ∀ g₁ g₂ g₃ g₄ : SU N,
      (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃ * g₄ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
        ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
          (coeff r s t u v : ℂ) *
          (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
           repCharacter (ρ u) g₃ * repCharacter (ρ v) g₄))
    (P : Type*) [Fintype P] [DecidableEq P]
    (L : Type*) [Fintype L] [DecidableEq L]
    (links : P → Fin 4 → L)
    (hlinks_surj : ∀ l, ∃ p j, links p j = l)
    (L_U L_0 L_V : Finset L)
    (hdisj : Disjoint L_U L_0 ∧ Disjoint (L_U ∪ L_0) L_V)
    (hcover : L_U ∪ L_0 ∪ L_V = Finset.univ) :
    ∃ (F : (L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (g : L → SU N),
      (∏ p : P, (Real.exp (c * (Matrix.trace
          ((g (links p 0) * g (links p 1) * (g (links p 2))⁻¹ *
           (g (links p 3))⁻¹ : SU N) :
          Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) =
        ∑ w : L → ι, (F w : ℂ) *
          (∏ l ∈ L_U, repCharacter (ρ (w l)) (g l)) *
          (∏ l ∈ L_0, repCharacter (ρ (w l)) (g l)) *
          conj (∏ l ∈ L_V, repCharacter (ρ (dual (w l))) (g l)) := by
  -- Step 1: the plain separable decomposition (all links unconjugated).
  obtain ⟨F, hF, hF_decomp⟩ := plaquette_product_separable_decomp
    ρ hU coeff hcoeff cg hcg hcg_decomp dual hdual c hc hexp4 P L links hlinks_surj
  refine ⟨F, hF, fun g => ?_⟩
  rw [hF_decomp g]
  refine Finset.sum_congr rfl fun w hw => ?_
  -- Step 2: separate the V⁺ links with conjugated dual characters.
  rw [prod_conj_partition_dual ρ hU dual hdual L L_V w g]
  -- Step 3: the remaining links `univ \ L_V` are exactly `L_U ∪ L_0`.
  have h_split : (Finset.univ : Finset L) \ L_V = L_U ∪ L_0 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hV
      by_contra h
      push_neg at h
      obtain ⟨hU, h0⟩ := h
      have hxu : x ∈ L_U ∪ L_0 ∪ L_V := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hxu with h01 | hV'
      · rcases Finset.mem_union.mp h01 with hU' | h0'
        · exact hU hU'
        · exact h0 h0'
      · exact hV hV'
    · rintro (hU | h0)
      · exact (Finset.disjoint_left.mp hdisj.2) (Finset.mem_union.mpr (Or.inl hU))
      · exact (Finset.disjoint_left.mp hdisj.2) (Finset.mem_union.mpr (Or.inr h0))
  rw [h_split, Finset.prod_union hdisj.1]
  ring

#print axioms interface_kernel_character_expansion

set_option maxHeartbeats 1000000 in
open scoped ComplexOrder in
/-- **Gram matrix positive-semidefiniteness.** For any matrix `A : ι → α → ℂ`
and vector `d : α → ℂ`, the quadratic form
`∑_{x,y} d_x · conj(d_y) · ∑_a A_{a,x} · conj(A_{a,y})` is non-negative.

This equals `∑_a |∑_x d_x · A_{a,x}|² ≥ 0`, the standard fact that the Gram matrix
`M_{xy} = ∑_a A_{a,x} · conj(A_{a,y})` is positive-semidefinite (it is `C^T · C̄`
where `C_{a,x} = A_{a,x}`, and `∑_{x,y} d_x · conj(d_y) · M_{xy} = ‖C · d‖² ≥ 0`).

This is the key PSD property (Lemma 5, Step 2) needed to reorganize the
reflection-positivity integral as `∑ |Fourier coefficient|² ≥ 0`. -/
lemma gram_matrix_psd_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : ι → α → ℂ) (d : α → ℂ) :
    0 ≤ ∑ x : α, ∑ y : α, d x * conj (d y) * ∑ a : ι, A a x * conj (A a y) := by
  -- Helper: conj pushes through products (conj = starRingEnd ℂ, map_mul)
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  -- Helper: conj pushes through sums (conj = starRingEnd ℂ, map_sum)
  have hconj_sum : ∀ (f : α → ℂ), conj (∑ y : α, f y) = ∑ y : α, conj (f y) :=
    fun f => map_sum (starRingEnd ℂ) f Finset.univ
  -- Key identity: the quadratic form equals ∑_a normSq(∑_x d x * A a x)
  have hkey : (∑ x : α, ∑ y : α, d x * conj (d y) * ∑ a : ι, A a x * conj (A a y)) =
      ∑ a : ι, (Complex.normSq (∑ x : α, d x * A a x) : ℂ) := by
    -- Step 1: pull ∑_a out of each (x,y) term
    have h_pull : (∑ x : α, ∑ y : α, d x * conj (d y) * ∑ a : ι, A a x * conj (A a y)) =
        ∑ x : α, ∑ y : α, ∑ a : ι, d x * conj (d y) * (A a x * conj (A a y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.mul_sum]
    rw [h_pull]
    -- Step 2: reorder ∑_x ∑_y ∑_a → ∑_a ∑_x ∑_y
    have h_swap_ya : ∀ x : α,
        (∑ y : α, ∑ a : ι, d x * conj (d y) * (A a x * conj (A a y))) =
        (∑ a : ι, ∑ y : α, d x * conj (d y) * (A a x * conj (A a y))) := by
      intro x
      rw [Finset.sum_comm]
    have h_reorder : (∑ x : α, ∑ y : α, ∑ a : ι,
        d x * conj (d y) * (A a x * conj (A a y))) =
        ∑ a : ι, ∑ x : α, ∑ y : α,
        d x * conj (d y) * (A a x * conj (A a y)) := by
      rw [Finset.sum_congr rfl (fun x _ => h_swap_ya x)]
      rw [Finset.sum_comm]
    rw [h_reorder]
    -- Step 3: for each a, factor as (∑_x d x * A a x) * conj(∑_y d y * A a y) = normSq
    apply Finset.sum_congr rfl
    intro a _
    -- Regroup: d x * conj(d y) * (A a x * conj(A a y)) = (d x * A a x) * conj(d y * A a y)
    rw [show (∑ x : α, ∑ y : α,
          d x * conj (d y) * (A a x * conj (A a y))) =
        ∑ x : α, ∑ y : α, (d x * A a x) * conj (d y * A a y) from
      Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by
        rw [hconj_mul (d y) (A a y)]; ring))]
    -- Factor: (∑_x d x * A a x) * (∑_y conj(d y * A a y)) = (∑_x ...) * conj(∑_y ...)
    rw [← Finset.sum_mul_sum, ← hconj_sum (fun y => d y * A a y)]
    -- conj(∑_y d y * A a y) = conj(∑_x d x * A a x) by alpha-equivalence
    rw [show conj (∑ y : α, d y * A a y) = conj (∑ x : α, d x * A a x) from rfl]
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  rw [hkey]
  -- Each normSq term is ≥ 0; sum of nonneg ℂ terms is nonneg
  exact Finset.sum_nonneg (fun a _ => Complex.zero_le_real.mpr (Complex.normSq_nonneg _))

#print axioms gram_matrix_psd_nonneg

open scoped ComplexOrder in
/-- **Multi-link Gram matrix PSD (Lemma 5, Step 3).** For a finite type `L` of links,
and for each link `l`, finite types `ι_l` (CG index) and `α_l` (matrix element index),
matrices `A^{(l)} : ι_l → α_l → ℂ`, and a function `d : (Π l, α_l) → ℂ`:

    0 ≤ ∑_{x : Π l, α_l} ∑_{y : Π l, α_l} d(x) · conj(d(y)) ·
          ∑_{g : Π l, ι_l} ∏_l A^{(l)}(g_l, x_l) · conj(A^{(l)}(g_l, y_l))

This is the multi-link extension of `gram_matrix_psd_nonneg`: the product of per-link Gram
matrices is PSD. Proof: rewrite `∏_l (A_l · conj(A_l))` as `(∏_l A_l) · conj(∏_l A_l)` via
`Finset.prod_mul_distrib` + `map_prod (starRingEnd ℂ)`, then inline the Gram matrix PSD
argument (pull ∑_g out, factor per-g as normSq, conclude nonneg) — inlining avoids the
`whnf` timeout from passing the large `∏_l` lambda as an explicit argument to
`gram_matrix_psd_nonneg`.

This is the key PSD property for the reflection-positivity reorganization (Lemma 5): after
the L² expansion and Fubini factorization, the reflection-positivity integral becomes a
sum of such multi-link Gram matrix quadratic forms, each of which is non-negative. -/
lemma multi_link_gram_psd_nonneg
    {L : Type*} [Fintype L] [DecidableEq L]
    {ι : L → Type*} [∀ l, Fintype (ι l)] [∀ l, DecidableEq (ι l)]
    {α : L → Type*} [∀ l, Fintype (α l)] [∀ l, DecidableEq (α l)]
    (A : ∀ l, ι l → α l → ℂ)
    (d : (Π l, α l) → ℂ) :
    0 ≤ ∑ x : (Π l, α l), ∑ y : (Π l, α l),
        d x * conj (d y) * ∑ g : (Π l, ι l), ∏ l : L, A l (g l) (x l) * conj (A l (g l) (y l)) := by
  -- conj distributes over products: conj(∏ f) = ∏ conj(f)
  have hconj_prod : ∀ (f : L → ℂ), conj (∏ l : L, f l) = ∏ l : L, conj (f l) :=
    fun f => map_prod (starRingEnd ℂ) f Finset.univ
  -- Helpers for inlined gram_matrix_psd_nonneg (avoids whnf timeout from passing large lambda)
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  have hconj_sum : ∀ (f : (Π l, α l) → ℂ), conj (∑ y : (Π l, α l), f y) = ∑ y, conj (f y) :=
    fun f => map_sum (starRingEnd ℂ) f Finset.univ
  -- Step 1: rewrite ∏_l (A_l · conj(A_l)) → (∏_l A_l) · conj(∏_l A_l) under all binders
  have hstep1 : ∀ (g : Π l, ι l) (x y : Π l, α l),
      (∏ l : L, A l (g l) (x l) * conj (A l (g l) (y l))) =
      (∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l)) := by
    intro g x y
    rw [Finset.prod_mul_distrib, ← hconj_prod (fun l => A l (g l) (y l))]
  simp only [hstep1]
  -- Step 2: pull ∑_g out of each (x,y) term (Finset.mul_sum under binders)
  have hstep2 : ∀ (x y : Π l, α l),
      (d x * conj (d y) * ∑ g : (Π l, ι l),
        (∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l))) =
      (∑ g : (Π l, ι l),
        d x * conj (d y) * ((∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l)))) := by
    intro x y
    simp only [Finset.mul_sum]
  simp only [hstep2]
  -- Step 3: reorder ∑_x ∑_y ∑_g → ∑_g ∑_x ∑_y (two sum_comm swaps)
  have hstep3 : ∀ (x : Π l, α l),
      (∑ y : (Π l, α l), ∑ g : (Π l, ι l),
        d x * conj (d y) * ((∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l)))) =
      (∑ g : (Π l, ι l), ∑ y : (Π l, α l),
        d x * conj (d y) * ((∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l)))) := by
    intro x
    rw [Finset.sum_comm]
  simp only [hstep3]
  rw [Finset.sum_comm]
  -- Step 4: for each g, factor as normSq(∑_x d x * ∏_l A_l)
  have hstep4 : ∀ (g : Π l, ι l),
      (∑ x : (Π l, α l), ∑ y : (Π l, α l),
        d x * conj (d y) * ((∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l)))) =
      (Complex.normSq (∑ x : (Π l, α l), d x * ∏ l : L, A l (g l) (x l)) : ℂ) := by
    intro g
    -- Regroup: d x * conj(d y) * (B gx * conj(B gy)) = (d x * B gx) * conj(d y * B gy)
    have hregroup : ∀ (x y : Π l, α l),
        (d x * conj (d y) * ((∏ l : L, A l (g l) (x l)) * conj (∏ l : L, A l (g l) (y l)))) =
        ((d x * ∏ l : L, A l (g l) (x l)) * conj (d y * ∏ l : L, A l (g l) (y l))) := by
      intro x y
      rw [hconj_mul (d y) (∏ l : L, A l (g l) (y l))]; ring
    simp only [hregroup]
    -- Factor: (∑_x d x * B gx) * (∑_y conj(d y * B gy)) = (∑_x ...) * conj(∑_y ...)
    rw [← Finset.sum_mul_sum, ← hconj_sum (fun y => d y * ∏ l : L, A l (g l) (y l))]
    -- conj(∑_y ...) = conj(∑_x ...) by alpha-equivalence
    rw [show conj (∑ y : (Π l, α l), d y * ∏ l : L, A l (g l) (y l)) =
          conj (∑ x : (Π l, α l), d x * ∏ l : L, A l (g l) (x l)) from rfl]
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  simp only [hstep4]
  -- Each normSq term is ≥ 0; sum of nonneg ℂ terms is nonneg
  exact Finset.sum_nonneg (fun g _ => Complex.zero_le_real.mpr (Complex.normSq_nonneg _))

#print axioms multi_link_gram_psd_nonneg

open scoped ComplexOrder in
/-- **Reflection positivity reorganization (Lemma 5, Step 4b).** For a finite type `W` of
Fourier modes, a finite type `L` of links, per-link matrices `A^{(w,l)} : ι_l → α_l → ℂ`,
per-mode coefficients `d_w : (Π l, α_l) → ℂ`, and non-negative weights `F : W → ℝ`:

    0 ≤ ∑_{w : W} F(w) · ∑_{x : Π l, α_l} ∑_{y : Π l, α_l}
          d_w(x) · conj(d_w(y)) · ∑_{g : Π l, ι_l} ∏_l A^{(w,l)}(g_l, x_l) · conj(A^{(w,l)}(g_l, y_l))

This is the weighted multi-link Gram matrix PSD property: each per-mode term is a multi-link
Gram matrix quadratic form (≥ 0 by `multi_link_gram_psd_nonneg`), and the weights `F(w) ≥ 0`
preserve non-negativity (since `F(w)` is real and the Gram matrix term is real and non-negative,
their product is real and non-negative). This is the "assembly" part of Lemma 5 — it shows that
IF the reflection-positivity integral has the multi-link Gram matrix form (after L² expansion +
Fubini factorization + triple product evaluation), THEN it is non-negative. -/
lemma reflection_positivity_reorganization
    {L : Type*} [Fintype L] [DecidableEq L]
    {W : Type*} [Fintype W] [DecidableEq W]
    {ι : L → Type*} [∀ l, Fintype (ι l)] [∀ l, DecidableEq (ι l)]
    {α : L → Type*} [∀ l, Fintype (α l)] [∀ l, DecidableEq (α l)]
    (A : W → ∀ l, ι l → α l → ℂ)
    (d : W → (Π l, α l) → ℂ)
    (F : W → ℝ) (hF : ∀ w, 0 ≤ F w) :
    0 ≤ ∑ w : W, (F w : ℂ) * ∑ x : (Π l, α l), ∑ y : (Π l, α l),
        d w x * conj (d w y) * ∑ g : (Π l, ι l),
          ∏ l : L, A w l (g l) (x l) * conj (A w l (g l) (y l)) := by
  apply Finset.sum_nonneg
  intro w _
  have hgram : 0 ≤ ∑ x : (Π l, α l), ∑ y : (Π l, α l),
      d w x * conj (d w y) * ∑ g : (Π l, ι l),
        ∏ l : L, A w l (g l) (x l) * conj (A w l (g l) (y l)) :=
    multi_link_gram_psd_nonneg (A w) (d w)
  have hgram_rc := Complex.nonneg_iff.mp hgram
  refine Complex.le_def.mpr ?_
  constructor
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (hF w) hgram_rc.1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add]
    rw [hgram_rc.2.symm]; simp

#print axioms reflection_positivity_reorganization
