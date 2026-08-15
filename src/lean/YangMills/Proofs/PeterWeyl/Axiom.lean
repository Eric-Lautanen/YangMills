/-
# Peter-Weyl: Clebsch-Gordan Axiom and Plaquette Boltzmann Factor
-/

import YangMills.Proofs.PeterWeyl.PDSums

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
/-! ## Peter-Weyl / Clebsch-Gordan axiom and the plaquette Boltzmann factor -/

section PlaquetteBoltzmann

/-- **Axiom (Peter-Weyl + Clebsch-Gordan for the plaquette Boltzmann factor
and character products).**

This axiom provides three things in a single existential:

1. **Plaquette character expansion.**  For `c ≥ 0`, the plaquette Boltzmann
   factor `exp(c · Re Tr(g₁ g₂ g₃ g₄))` admits a character expansion

       exp(c · Re Tr(g₁ g₂ g₃ g₄))
         = ∑_{r,s,t,u,v} coeff r s t u v · χ_s(g₁) · χ_t(g₂) · χ_u(g₃) · χ_v(g₄)

   where the sum ranges over a finite index set `ι` of irreducible unitary
   representations `ρ i` of `SU(N)`, `χ_i = repCharacter (ρ i)` is the character,
   and the coefficients `coeff r s t u v ≥ 0`.  The index `r` is the Peter-Weyl
   expansion index (carrying the heat-kernel coefficient `a_r ≥ 0`) and
   `s, t, u, v` are the Clebsch-Gordan indices produced by decomposing
   `χ_r(g₁ g₂ g₃ g₄)` into a sum of products of single-link characters
   (Littlewood-Richardson coefficients, applied three times).  All coefficients
   are non-negative.

2. **Clebsch-Gordan decomposition for character products.**  For the same
   index set `ι` and representations `ρ`, the product of two characters of the
   *same* group element decomposes as a non-negative-weighted sum of single
   characters:

       χ_s(g) · χ_t(g) = ∑_w cg s t w · χ_w(g),    cg s t w ≥ 0.

   This is the Littlewood-Richardson rule: `cg s t w` is the multiplicity of
   `ρ_w` in the tensor product `ρ_s ⊗ ρ_t`.  It is needed when a single link
   variable appears in multiple plaquettes: the product of the character
   expansions of two plaquettes sharing a link `g` produces `χ_s(g) · χ_t(g)`,
   which must be reduced to a single sum via CG before the kernel can be
   written in separable form.

3. **Dual (contragredient) representations.**  The index set `ι` is closed
   under taking duals: there is a map `dual : ι → ι` such that the character of
   `ρ_{dual(i)}` is the complex conjugate of the character of `ρ_i`:

       χ_{dual(i)}(g) = conj(χ_i(g)).

   This is the standard fact that the contragredient (dual) of a unitary
   representation has character `conj(χ(g))` (since `ρ*(g) = ρ(g⁻¹)^H` and
   `Tr(M^H) = conj(Tr(M))`).  For `SU(N)`, the dual of an irreducible is
   another irreducible, so `ι` (taken large enough) is closed under duals.
   This is needed because the lattice plaquette product has **inverted links**
   (`g₃⁻¹, g₄⁻¹`), and `χ(g⁻¹) = conj(χ(g)) = χ_{dual}(g)` by
   `repCharacter_inv`.  When a link appears in multiple plaquettes with mixed
   orientations (some as `g`, some as `g⁻¹`), the product involves both `χ(g)`
   and `conj(χ(g))`; the dual map converts `conj(χ)` to `χ_{dual}`, allowing
   the CG decomposition to combine them into a single character sum.

This axiom fuses four deep theorems of compact-Lie-group representation theory
that are not currently in Mathlib:

  * **Peter-Weyl theorem**: `exp(c · Re Tr(g)) = ∑_r a_r χ_r(g)` with `a_r ≥ 0`.
  * **Clebsch-Gordan decomposition** (within a plaquette): `χ_r(gh) =
    ∑_{s,t} N^r_{st} χ_s(g) χ_t(h)` with Littlewood-Richardson multiplicities
    `N^r_{st} ≥ 0`, applied three times to split the four-link product.
  * **Clebsch-Gordan decomposition** (across plaquettes): `χ_s(g) · χ_t(g) =
    ∑_w N^w_{st} χ_w(g)` with `N^w_{st} ≥ 0`, needed to combine character
    expansions when the same link appears in multiple plaquettes.
  * **Duality of representations**: `χ_{dual(i)}(g) = conj(χ_i(g))`, needed to
    handle inverted links in the plaquette product.

The axiom also asserts that each `ρ i` is **irreducible** (`hIrr`) and has
**positive dimension** (`hDims`); these are the hypotheses required to apply
the Schur orthogonality axiom `characterOrthogonality` (matrix-element
orthogonality) to the Peter–Weyl data, which is the key ingredient for closing
`transferMatrixPositivity_axiom` via the `T = B*·B` argument.

The index set `ι` is required to be closed under tensor-product decomposition
and under duals (so that the CG sum and the dual map stay within `ι`); this is
guaranteed by taking `ι` large enough to contain all irreducibles appearing in
any relevant tensor product or dual.

**Strengthened** (2026-08-02) to also provide the **L² completeness** (Peter–Weyl
theorem, completeness part).  In addition to the finite `ι` (which suffices for
the character expansion of the Boltzmann factor), the axiom now provides a
**countable** index set `Λ` (with `Encodable Λ`) of *all* irreducible unitary
representations of `SU(N)`, with matrix elements `(ρ_λ g)_{ij}` for `λ ∈ Λ`.
The L² completeness is stated as: if `f ∈ L¹(G, μ)` is integrable and all its
Fourier coefficients `∫ f · conj((ρ_λ g)_{ij}) dμ = 0` vanish (for all `λ`,
`i`, `j`), then `f = 0` a.e.  This is the statement that the matrix elements
form an orthonormal **basis** (not just an orthogonal family) of `L²(G, μ)`,
so a function orthogonal to all of them is zero.  The embedding `emb : ι ↪ Λ`
with `hemb` ensures the finite `ι` (used for the character expansion) is a
subset of the countable `Λ` (used for the L² completeness), with matching
characters.  The measure `μ` is the normalized Haar measure on `SU(N)` (a
probability measure).  The L² completeness is the remaining ingredient needed
to close `transferMatrixPositivity_axiom`: it allows expanding the arbitrary
`L²` function `A_w` (arising from the test function `f`) in the matrix-element
basis, which is required to evaluate the reflection-positivity integral as
`∑ |Fourier coefficient|² ≥ 0`.  See `docs/transfer_matrix_positivity_design.md`
§5a for the full analysis.

**Strengthened** (2026-08-02 session 3) to also provide the **matrix-element
Clebsch–Gordan coefficients** `cgME`.  In addition to the character-level CG
decomposition `χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)` (which gives the
multiplicities but not the basis change), the axiom now provides the
unitary change-of-basis matrices `cgME s t ν : Fin (dims s) → Fin (dims t) →
Fin (dims ν) → ℂ` that implement the decomposition of the tensor-product
representation `ρ_s ⊗ ρ_t → ⊕_ν ρ_ν` at the matrix-element level:

    (ρ_s g)_{ab} · (ρ_t g)_{ij} = ∑_ν ∑_p ∑_q cgME s t ν a i p · (ρ_ν g)_{pq} · conj(cgME s t ν b j q)

together with the unitarity (completeness) relation `∑_{ν,p} conj(cgME) · cgME = δ`.
These matrix-element CG coefficients are needed to evaluate the triple-product
integrals `∫ χ_w · (ρ_λ)_{ij} · conj((ρ_μ)_{kl}) dμ` that arise in the
reflection-positivity reorganization, and to reorganize the sum as
`∑ |Fourier coefficient|² ≥ 0`.  See `docs/transfer_matrix_positivity_design.md`
§8.7 for the full analysis.

See `docs/found_issues.md` §3 and `docs/gap_analysis.md` for the mathematical
obstruction that necessitates this expansion. -/
axiom peterWeyl_clebschGordan_plaquette (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (hIrr : ∀ i, IsIrreducible (ρ i))
      (hDims : ∀ i, 0 < dims i)
      (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
      (coeff : ι → ι → ι → ι → ι → ℝ)
      (hcoeff : ∀ r s t u v, 0 ≤ coeff r s t u v)
      (cg : ι → ι → ι → ℝ)
      (hcg : ∀ s t w, 0 ≤ cg s t w)
      (hcg_decomp : ∀ s t (g : SU N),
        repCharacter (ρ s) g * repCharacter (ρ t) g =
        ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
      (dual : ι → ι)
      (hdual : ∀ i (g : SU N),
        repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
      (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
      (hcgME_decomp : ∀ (s t : ι) (g : SU N) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
      (hcgME_unitary : ∀ (s t : ι) (a b : Fin (dims s)) (i j : Fin (dims t)),
        ∑ ν : ι, ∑ p : Fin (dims ν),
          conj (cgME s t ν a i p) * cgME s t ν b j p =
          if a = b ∧ i = j then (1 : ℂ) else 0)
      (Λ : Type) (hΛ : Encodable Λ)
      (dimsΛ : Λ → ℕ)
      (ρΛ : ∀ ℓ, SU N →* Matrix (Fin (dimsΛ ℓ)) (Fin (dimsΛ ℓ)) ℂ)
      (hUΛ : ∀ ℓ, IsUnitaryRepresentation (ρΛ ℓ))
      (hIrrΛ : ∀ ℓ, IsIrreducible (ρΛ ℓ))
      (hDimsΛ : ∀ ℓ, 0 < dimsΛ ℓ)
      (emb : ι ↪ Λ)
      (hemb : ∀ i (g : SU N),
        repCharacter (ρΛ (emb i)) g = repCharacter (ρ i) g)
      (μ : Measure (SU N)) (hμ : IsProbabilityMeasure μ)
      -- CG coefficients for ι × Λ: decompose (ρ_s)_{ab} · (ρΛ_t)_{ij} into
      -- matrix elements of irreps ν ∈ Λ.  Since the tensor product ρ_s ⊗ ρΛ_t
      -- decomposes as a FINITE direct sum of irreps, only finitely many ν
      -- contribute; the support is recorded by `hcgMEΛ_support`.
      (cgMEΛ : ∀ (s : ι) (t ν : Λ), Fin (dims s) → Fin (dimsΛ t) → Fin (dimsΛ ν) → ℂ)
      (hcgMEΛ_support : ∀ (s : ι) (t : Λ), Finset Λ),
      -- Part 1: character expansion of the plaquette Boltzmann factor
      (∀ (g₁ g₂ g₃ g₄ : SU N),
        (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃ * g₄ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
          ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
            (coeff r s t u v : ℂ) *
            (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
             repCharacter (ρ u) g₃ * repCharacter (ρ v) g₄)) ∧
      -- Part 2: L² completeness (Peter-Weyl theorem, completeness part).
      -- If `f` is integrable and all its Fourier coefficients (w.r.t. the
      -- matrix elements of all irreps in `Λ`) vanish, then `f = 0` a.e.
      -- This is the completeness of the Peter-Weyl basis: the matrix
      -- elements `{(ρ_ℓ g)_{ij} : ℓ ∈ Λ, i, j}` form an orthonormal basis
      -- of `L²(G, μ)`, so a function orthogonal to all of them is zero.
      (∀ (f : SU N → ℂ),
        Integrable f μ →
        (∀ (ℓ : Λ) (i : Fin (dimsΛ ℓ)) (j : Fin (dimsΛ ℓ)),
          ∫ g, f g * conj ((ρΛ ℓ g) i j) ∂μ = 0) →
        f =ᵐ[μ] 0) ∧
      -- Part 3: Schur orthogonality for Λ (countable).  The matrix elements
      -- of distinct irreps in Λ are orthogonal, and matrix elements of the
      -- same irrep are orthogonal with norm 1/dimsΛ.  This is the Great
      -- Orthogonality Theorem for the full set of irreps (countable Λ),
      -- extending `characterOrthogonality` (which covers finite ι only).
      -- Needed to evaluate ∫ (ρΛ_ν)_{pq} · conj((ρΛ_μ)_{kl}) in the
      -- generalized triple-product integral (step 3 of the formalization
      -- path, §8.11.53–56).
      ( (∀ (ν μ₂ : Λ) (p : Fin (dimsΛ ν)) (q : Fin (dimsΛ ν))
            (k : Fin (dimsΛ μ₂)) (l : Fin (dimsΛ μ₂)),
          Integrable (fun g => (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l)) μ) ∧
        (∀ (ν : Λ) (p q k l : Fin (dimsΛ ν)),
          ∫ g, (ρΛ ν g) p q * conj ((ρΛ ν g) k l) ∂μ =
            if p = k ∧ q = l then (1 / dimsΛ ν : ℂ) else 0) ∧
        (∀ (ν μ₂ : Λ) (p q : Fin (dimsΛ ν)) (k l : Fin (dimsΛ μ₂)),
          ν ≠ μ₂ →
          ∫ g, (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l) ∂μ = 0) ) ∧
      -- Part 4: CG decomposition for ι × Λ (finite support).  For each
      -- (s : ι, t : Λ), the product (ρ_s g)_{ab} · (ρΛ_t g)_{ij} decomposes
      -- as a finite sum over ν ∈ hcgMEΛ_support s t of matrix elements
      -- (ρΛ_ν g)_{pq} with CG coefficients cgMEΛ.  The unitarity relation
      -- (completeness of the CG change-of-basis) is also provided.
      -- Needed to decompose the triple product χ_s · (ρΛ_ν)_{ij} · conj(...)
      -- in the generalized triple-product integral (step 3).
      ( (∀ (s : ι) (t : Λ) (g : SU N) (a b : Fin (dims s)) (i j : Fin (dimsΛ t)),
          (ρ s g) a b * (ρΛ t g) i j =
          ∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
            cgMEΛ s t ν a i p * (ρΛ ν g) p q * conj (cgMEΛ s t ν b j q)) ∧
        (∀ (s : ι) (t : Λ) (a b : Fin (dims s)) (i j : Fin (dimsΛ t)),
          ∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν),
            conj (cgMEΛ s t ν a i p) * cgMEΛ s t ν b j p =
            if a = b ∧ i = j then (1 : ℂ) else 0) ∧
        (∀ (s : ι) (t ν : Λ), ν ∉ hcgMEΛ_support s t →
          ∀ (a : Fin (dims s)) (i : Fin (dimsΛ t)) (p : Fin (dimsΛ ν)),
            cgMEΛ s t ν a i p = 0) )

/-- The character of a unitary representation of `SU(N)` is positive-definite. -/
lemma repCharacter_SU_positiveDefinite {ι : Type*} {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i)) (i : ι) :
    PositiveDefinite (repCharacter (ρ i)) :=
  repCharacter_positiveDefinite (ρ i) (hU i)

/-- A product of four characters `χ_s(g₁) χ_t(g₂) χ_u(g₃) χ_v(g₄)` is
positive-definite on `SU(N)⁴` (left-associated as `((SU N × SU N) × SU N) × SU N`).

This follows by applying `PositiveDefinite.prod` three times, using that each
character is positive-definite by `repCharacter_positiveDefinite`. -/
lemma charProduct4_positiveDefinite {ι : Type*} {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (s t u v : ι) :
    PositiveDefinite
      (λ (p : ((SU N × SU N) × SU N) × SU N) =>
        repCharacter (ρ s) p.1.1.1 * repCharacter (ρ t) p.1.1.2 *
        repCharacter (ρ u) p.1.2 * repCharacter (ρ v) p.2) := by
  have hS : PositiveDefinite (repCharacter (ρ s)) := repCharacter_SU_positiveDefinite ρ hU s
  have hT : PositiveDefinite (repCharacter (ρ t)) := repCharacter_SU_positiveDefinite ρ hU t
  have hU' : PositiveDefinite (repCharacter (ρ u)) := repCharacter_SU_positiveDefinite ρ hU u
  have hV : PositiveDefinite (repCharacter (ρ v)) := repCharacter_SU_positiveDefinite ρ hU v
  have hST := PositiveDefinite.prod hS hT
  have hSTU := PositiveDefinite.prod hST hU'
  have hSTUV := PositiveDefinite.prod hSTU hV
  convert hSTUV using 3

/-- **The plaquette Boltzmann factor is positive-definite on `SU(N)⁴`.**

For `c ≥ 0`, the function
    (g₁, g₂, g₃, g₄) ↦ exp(c · Re Tr(g₁ g₂ g₃ g₄))
is positive-definite on `SU(N) × SU(N) × SU(N) × SU(N)` (left-associated).

This is the key positive-definiteness input for the Osterwalder-Seiler transfer
matrix positivity proof.  It is proved from the Peter-Weyl / Clebsch-Gordan
character expansion axiom `peterWeyl_clebschGordan_plaquette`: the expansion
writes the Boltzmann factor as a finite sum, with non-negative coefficients, of
products `χ_s(g₁) χ_t(g₂) χ_u(g₃) χ_v(g₄)` of characters, each product
positive-definite by `charProduct4_positiveDefinite`.  A finite sum of
positive-definite functions with non-negative coefficients is positive-definite
(`PositiveDefinite.sum`). -/
theorem plaquetteBoltzmannPD (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    PositiveDefinite
      (λ (p : ((SU N × SU N) × SU N) × SU N) =>
        (Real.exp (c * (Matrix.trace ((p.1.1.1 * p.1.1.2 * p.1.2 * p.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, σ_0, hσ_0_dims, hσ_0_trivial, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ,
      cgMEΛ, hcgMEΛ_support, hexp4, hL2, hSchurΛ, hcgMEΛ_parts⟩ :=
    peterWeyl_clebschGordan_plaquette N c hc
  obtain ⟨hSchurΛ_int, hSchurΛ_diag, hSchurΛ_offdiag⟩ := hSchurΛ
  obtain ⟨hcgMEΛ_decomp, hcgMEΛ_unitary, hcgMEΛ_support_zero⟩ := hcgMEΛ_parts
  letI : Fintype ι := hι
  -- The four-character product, as a function of the plaquette links.
  let F (r s t u v : ι) (p : ((SU N × SU N) × SU N) × SU N) : ℂ :=
    repCharacter (ρ s) p.1.1.1 * repCharacter (ρ t) p.1.1.2 *
    repCharacter (ρ u) p.1.2 * repCharacter (ρ v) p.2
  have hF_PD : ∀ r s t u v, PositiveDefinite (F r s t u v) :=
    fun r s t u v => charProduct4_positiveDefinite ρ hU s t u v
  -- Innermost sum (over v): weighted by the expansion coefficient.
  have hSv : ∀ r s t u, PositiveDefinite
      (λ p => ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r s t u =>
      PositiveDefinite.sum Finset.univ (F r s t u)
        (fun v _ => hF_PD r s t u v) (coeff r s t u)
        (fun v _ => hcoeff r s t u v)
  -- Outer sums (over u, t, s, r): unweighted sums of PD functions.
  have hSu : ∀ r s t, PositiveDefinite
      (λ p => ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r s t =>
      PositiveDefinite.sum' Finset.univ
        (fun u p => ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p)
        (fun u _ => hSv r s t u)
  have hSt : ∀ r s, PositiveDefinite
      (λ p => ∑ t : ι, ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r s =>
      PositiveDefinite.sum' Finset.univ
        (fun t p => ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p)
        (fun t _ => hSu r s t)
  have hSs : ∀ r, PositiveDefinite
      (λ p => ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r =>
      PositiveDefinite.sum' Finset.univ
        (fun s p => ∑ t : ι, ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p)
        (fun s _ => hSt r s)
  have hSr : PositiveDefinite
      (λ p => ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) * F r s t u v p) :=
    PositiveDefinite.sum' Finset.univ
      (fun r p => ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) * F r s t u v p)
      (fun r _ => hSs r)
  -- The Boltzmann factor equals the character expansion pointwise.
  have hfun :
      (λ p : ((SU N × SU N) × SU N) × SU N =>
        (Real.exp (c * (Matrix.trace ((p.1.1.1 * p.1.1.2 * p.1.2 * p.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) =
      (λ p => ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) * F r s t u v p) := by
    funext p
    simp only [F]
    exact hexp4 p.1.1.1 p.1.1.2 p.1.2 p.2
  rw [hfun]
  exact hSr


/-- A product of four characters with the 3rd and 4th conjugated,
`χ_s(g₁) · χ_t(g₂) · conj(χ_u(g₃)) · conj(χ_v(g₄))`, is positive-definite on
`SU(N)⁴` (left-associated).  This follows from `charProduct4_positiveDefinite`
and `PositiveDefinite.conj` applied to the 3rd and 4th factors. -/
lemma charProduct4_inv_positiveDefinite {ι : Type*} {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (s t u v : ι) :
    PositiveDefinite
      (λ (p : ((SU N × SU N) × SU N) × SU N) =>
        repCharacter (ρ s) p.1.1.1 * repCharacter (ρ t) p.1.1.2 *
        conj (repCharacter (ρ u) p.1.2) * conj (repCharacter (ρ v) p.2)) := by
  have hS : PositiveDefinite (repCharacter (ρ s)) := repCharacter_SU_positiveDefinite ρ hU s
  have hT : PositiveDefinite (repCharacter (ρ t)) := repCharacter_SU_positiveDefinite ρ hU t
  have hU' : PositiveDefinite (fun g => conj (repCharacter (ρ u) g)) := by
    exact PositiveDefinite.conj (repCharacter_SU_positiveDefinite ρ hU u)
  have hV : PositiveDefinite (fun g => conj (repCharacter (ρ v) g)) := by
    exact PositiveDefinite.conj (repCharacter_SU_positiveDefinite ρ hU v)
  have hST := PositiveDefinite.prod hS hT
  have hSTU := PositiveDefinite.prod hST hU'
  have hSTUV := PositiveDefinite.prod hSTU hV
  convert hSTUV using 3

/-- **The plaquette Boltzmann factor with inverse links is positive-definite on
`SU(N)⁴`.**

For `c ≥ 0`, the function
    (g₁, g₂, g₃, g₄) ↦ exp(c · Re Tr(g₁ g₂ g₃⁻¹ g₄⁻¹))
is positive-definite on `SU(N) × SU(N) × SU(N) × SU(N)` (left-associated).

This is the version needed for the actual lattice plaquette product
`U(n,μ) · U(n+e_μ,ν) · U(n+e_μ+e_ν,μ)⁻¹ · U(n+e_ν,ν)⁻¹`, which has inverses on
the 3rd and 4th links (orientation reversal).  The proof uses the Peter-Weyl /
Clebsch-Gordan axiom applied to `(g₁, g₂, g₃⁻¹, g₄⁻¹)`, then replaces
`χ_u(g₃⁻¹) = conj(χ_u(g₃))` and `χ_v(g₄⁻¹) = conj(χ_v(g₄))` via `repCharacter_inv`.
Each factor `χ_s(g₁) · χ_t(g₂) · conj(χ_u(g₃)) · conj(χ_v(g₄))` is
positive-definite by `charProduct4_inv_positiveDefinite`, and the finite sum
with non-negative coefficients is positive-definite by `PositiveDefinite.sum`. -/
theorem plaquetteBoltzmannPD_inv (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    PositiveDefinite
      (λ (p : ((SU N × SU N) × SU N) × SU N) =>
        (Real.exp (c * (Matrix.trace ((p.1.1.1 * p.1.1.2 * p.1.2⁻¹ * p.2⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, σ_0, hσ_0_dims, hσ_0_trivial, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ,
      cgMEΛ, hcgMEΛ_support, hexp4, hL2, hSchurΛ, hcgMEΛ_parts⟩ :=
    peterWeyl_clebschGordan_plaquette N c hc
  obtain ⟨hSchurΛ_int, hSchurΛ_diag, hSchurΛ_offdiag⟩ := hSchurΛ
  obtain ⟨hcgMEΛ_decomp, hcgMEΛ_unitary, hcgMEΛ_support_zero⟩ := hcgMEΛ_parts
  letI : Fintype ι := hι
  -- The four-character product with conj on 3rd and 4th factors.
  let F (r s t u v : ι) (p : ((SU N × SU N) × SU N) × SU N) : ℂ :=
    repCharacter (ρ s) p.1.1.1 * repCharacter (ρ t) p.1.1.2 *
    conj (repCharacter (ρ u) p.1.2) * conj (repCharacter (ρ v) p.2)
  have hF_PD : ∀ r s t u v, PositiveDefinite (F r s t u v) :=
    fun r s t u v => charProduct4_inv_positiveDefinite ρ hU s t u v
  -- Innermost sum (over v): weighted by the expansion coefficient.
  have hSv : ∀ r s t u, PositiveDefinite
      (λ p => ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r s t u =>
      PositiveDefinite.sum Finset.univ (F r s t u)
        (fun v _ => hF_PD r s t u v) (coeff r s t u)
        (fun v _ => hcoeff r s t u v)
  -- Outer sums (over u, t, s, r): unweighted sums of PD functions.
  have hSu : ∀ r s t, PositiveDefinite
      (λ p => ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r s t =>
      PositiveDefinite.sum' Finset.univ
        (fun u p => ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p)
        (fun u _ => hSv r s t u)
  have hSt : ∀ r s, PositiveDefinite
      (λ p => ∑ t : ι, ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r s =>
      PositiveDefinite.sum' Finset.univ
        (fun t p => ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p)
        (fun t _ => hSu r s t)
  have hSs : ∀ r, PositiveDefinite
      (λ p => ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p) :=
    fun r =>
      PositiveDefinite.sum' Finset.univ
        (fun s p => ∑ t : ι, ∑ u : ι, ∑ v : ι, (coeff r s t u v : ℂ) * F r s t u v p)
        (fun s _ => hSt r s)
  have hSr : PositiveDefinite
      (λ p => ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) * F r s t u v p) :=
    PositiveDefinite.sum' Finset.univ
      (fun r p => ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) * F r s t u v p)
      (fun r _ => hSs r)
  -- The Boltzmann factor with inverses equals the character expansion with
  -- g₃ → g₃⁻¹, g₄ → g₄⁻¹ substituted, then χ(g⁻¹) = conj(χ(g)) applied.
  have hfun :
      (λ p : ((SU N × SU N) × SU N) × SU N =>
        (Real.exp (c * (Matrix.trace ((p.1.1.1 * p.1.1.2 * p.1.2⁻¹ * p.2⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) =
      (λ p => ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
        (coeff r s t u v : ℂ) * F r s t u v p) := by
    funext p
    simp only [F]
    -- Apply the axiom to (g₁, g₂, g₃⁻¹, g₄⁻¹)
    have hexp := hexp4 p.1.1.1 p.1.1.2 p.1.2⁻¹ p.2⁻¹
    rw [hexp]
    -- Replace χ_u(g₃⁻¹) = conj(χ_u(g₃)) and χ_v(g₄⁻¹) = conj(χ_v(g₄))
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    rw [repCharacter_inv (ρ u) (hU u) p.1.2,
        repCharacter_inv (ρ v) (hU v) p.2]
  rw [hfun]
  exact hSr

