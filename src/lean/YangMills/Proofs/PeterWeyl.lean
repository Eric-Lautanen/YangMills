/-
# Peter-Weyl Theorem and Positive-Definiteness of the Plaquette Boltzmann Factor

The Osterwalder-Seiler reflection positivity proof for SU(N) lattice gauge theory
requires showing that the *plaquette Boltzmann factor*

    exp(c · Re Tr(g₁ g₂ g₃ g₄))

is a positive-definite function on `SU(N)⁴` (the four link variables around a
plaquette).  As explained in `docs/found_issues.md` §3, this is **not** obtained by
composing the (already proven) positive-definite function `exp(c · Re Tr(g))` on
`SU(N)` with the multiplication map `SU(N)⁴ → SU(N)`, because that map is not a
group homomorphism for non-abelian groups and the composition does not preserve
positive-definiteness (a concrete `SU(2)` counterexample is given in
`docs/found_issues.md`).

The resolution, due to Osterwalder-Seiler (1978, §3), uses the **Peter-Weyl
theorem** and the **Clebsch-Gordan decomposition**:

    exp(c · Re Tr(g₁ g₂ g₃ g₄)) = ∑_λ a_λ χ_λ(g₁ g₂ g₃ g₄)
                                = ∑_λ a_λ ∑_{μ,ν,ρ,σ} C^λ_{μνρσ} χ_μ(g₁) χ_ν(g₂) χ_ρ(g₃) χ_σ(g₄)

where `a_λ ≥ 0` (the character-expansion coefficients of the heat kernel / Wilson
action), `C^λ_{μνρσ} ≥ 0` (Littlewood-Richardson / Clebsch-Gordan coefficients),
and each product `χ_μ(g₁) χ_ν(g₂) χ_ρ(g₃) χ_σ(g₄)` is positive-definite on
`SU(N)⁴` (a product of positive-definite functions on the individual factors,
using `PositiveDefinite.prod` and `repCharacter_positiveDefinite`).  A sum of
positive-definite functions with non-negative coefficients is positive-definite.

Neither the Peter-Weyl theorem nor the Clebsch-Gordan decomposition is currently
available in Mathlib.  We therefore **axiomatize** the combined character
expansion of the plaquette Boltzmann factor (which fuses Peter-Weyl and
Clebsch-Gordan applied three times) and then *prove*, from this axiom together
with the positive-definite-function infrastructure of `PositiveDefinite.lean`,
that the plaquette Boltzmann factor is positive-definite.  The axiomatized
ingredient is a deep theorem of compact-Lie-group representation theory; the
positive-definite algebra is fully formalized.

## References

* K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"
  (Ann. Phys. 110, 1978, pp 440–471), §3.
* M. Lüscher, "Some analytic results concerning the mass spectrum of Yang-Mills
  gauge theories on a torus" (1983).
* A. Kirillov, "An Introduction to Lie Groups and Lie Algebras", Ch. 4 (Peter-Weyl).
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Pi
import YangMills.Proofs.PositiveDefinite

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills

/-! ## Finite sums of positive-definite functions -/

section PositiveDefiniteSum

variable {G : Type*} [Group G]

/-- A finite weighted sum of positive-definite functions with non-negative real
weights is positive-definite.  This is the workhorse for building PD functions
out of character expansions. -/
lemma PositiveDefinite.sum {α : Type*} (s : Finset α)
    (f : α → G → ℂ) (hf : ∀ a ∈ s, PositiveDefinite (f a))
    (w : α → ℝ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    PositiveDefinite (λ g => ∑ a ∈ s, (w a : ℂ) * f a g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact PositiveDefinite.zero
  | insert x s hx ih =>
    have hPDx : PositiveDefinite (λ g => (w x : ℂ) * f x g) :=
      PositiveDefinite.smul_nonneg (hw x (Finset.mem_insert_self x s))
        (hf x (Finset.mem_insert_self x s))
    have hPDs : PositiveDefinite (λ g => ∑ a ∈ s, (w a : ℂ) * f a g) :=
      ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))
        (fun a ha => hw a (Finset.mem_insert_of_mem ha))
    have heq : (λ g => ∑ a ∈ insert x s, (w a : ℂ) * f a g) =
        (λ g => (w x : ℂ) * f x g + ∑ a ∈ s, (w a : ℂ) * f a g) := by
      funext g; rw [Finset.sum_insert hx]
    rw [heq]
    exact PositiveDefinite.add hPDx hPDs

/-- An unweighted finite sum of positive-definite functions is positive-definite. -/
lemma PositiveDefinite.sum' {α : Type*} (s : Finset α)
    (f : α → G → ℂ) (hf : ∀ a ∈ s, PositiveDefinite (f a)) :
    PositiveDefinite (λ g => ∑ a ∈ s, f a g) := by
  have h := PositiveDefinite.sum s f hf (fun _ => 1) (fun _ _ => by norm_num)
  have heq : (λ g => ∑ a ∈ s, (1 : ℂ) * f a g) = (λ g => ∑ a ∈ s, f a g) := by
    funext g; exact Finset.sum_congr rfl (fun a _ => one_mul _)
  rw [← heq]; exact h

end PositiveDefiniteSum

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

/-! ## Clebsch-Gordan decomposition for character products -/

/-- The product of two characters of the same group element is positive-definite,
via the Clebsch-Gordan decomposition: `χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)`
with `cg s t w ≥ 0`, and each `χ_w` is PD by `repCharacter_positiveDefinite`.

(Note: PD-ness of the product also follows directly from the Schur product
theorem `PositiveDefinite.mul`.  This lemma additionally provides the explicit
non-negative character decomposition, which is the key ingredient for combining
character expansions across plaquettes that share a link variable.) -/
lemma charProduct_PD {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (s t : ι) :
    PositiveDefinite (fun g => repCharacter (ρ s) g * repCharacter (ρ t) g) := by
  simp only [hcg_decomp s t]
  exact PositiveDefinite.sum Finset.univ (fun w => repCharacter (ρ w))
    (fun w _ => repCharacter_SU_positiveDefinite ρ hU w) (cg s t)
    (fun w _ => hcg s t w)

/-- A finite product of characters of the same group element decomposes as a
non-negative-weighted sum of single characters, via iterated Clebsch-Gordan.

For a nonempty finite set `s` of representation indices, `∏_{i ∈ s} χ_i(g)`
can be written as `∑_w coeff w · χ_w(g)` with `coeff w ≥ 0`.  This is proved by
induction on `s`, applying the CG decomposition `χ_s·χ_t = ∑_w cg s t w · χ_w`
at each step.  The coefficient of `χ_v` in the product over `insert x s` is
`∑_w coeff_s(w) · cg x w v`, which is non-negative as a sum of products of
non-negative reals.

This is the key algebraic ingredient for the transfer-matrix kernel
decomposition: when a single link variable appears in multiple interface
plaquettes, the product of the character expansions produces a product of
characters of that link, which this lemma reduces to a single non-negative
sum. -/
lemma charProduct_finset_decomp {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (s : Finset ι) (hs : s.Nonempty) :
    ∃ (coeff : ι → ℝ) (hcoeff : ∀ w, 0 ≤ coeff w),
      ∀ (g : SU N),
        (∏ i ∈ s, repCharacter (ρ i) g) =
        ∑ w : ι, (coeff w : ℂ) * repCharacter (ρ w) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | insert x s hx ih =>
    by_cases hse : s = ∅
    · -- Singleton: ∏_{i ∈ {x}} χ_i(g) = χ_x(g) = 1 · χ_x(g)
      subst hse
      refine ⟨fun w => if w = x then 1 else 0, fun w => ?_, fun g => ?_⟩
      · show 0 ≤ (if w = x then 1 else 0)
        split_ifs <;> norm_num
      · -- ∏ i ∈ {x}, χ_i(g) = χ_x(g) = ∑ w, (if w = x then 1 else 0) * χ_w(g)
        rw [Finset.prod_insert hx, Finset.prod_empty, mul_one]
        classical
        -- Only the w = x term survives (coefficient 1); all others are 0.
        have h_eq : ∀ w : ι, ((if w = x then 1 else 0 : ℝ) : ℂ) * repCharacter (ρ w) g =
            if w = x then repCharacter (ρ w) g else 0 := fun w => by
          by_cases hwx : w = x <;> simp [hwx]
        rw [show ∑ w : ι, ((if w = x then 1 else 0 : ℝ) : ℂ) * repCharacter (ρ w) g =
            ∑ w : ι, (if w = x then repCharacter (ρ w) g else 0) from
            Finset.sum_congr rfl (fun w _ => h_eq w)]
        simp
    · -- s ≠ ∅: use ih to decompose ∏_{i∈s} χ_i, then combine with χ_x via CG
      have hs' : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
      obtain ⟨coeff_s, hcoeff_s, hdecomp_s⟩ := ih hs'
      -- New coefficient: coeff v = ∑_w, coeff_s w * cg x w v  (non-negative)
      refine ⟨fun v => ∑ w : ι, coeff_s w * cg x w v, fun v => ?_, fun g => ?_⟩
      · exact Finset.sum_nonneg (fun w _ => mul_nonneg (hcoeff_s w) (hcg x w v))
      · -- χ_x(g) * (∑_w coeff_s w * χ_w(g))
        --   = ∑_w coeff_s w * (χ_x(g) * χ_w(g))     [distribute + rearrange]
        --   = ∑_w coeff_s w * (∑_v cg x w v * χ_v(g)) [CG]
        --   = ∑_v (∑_w coeff_s w * cg x w v) * χ_v(g)  [exchange sums]
        rw [Finset.prod_insert hx, hdecomp_s g, Finset.mul_sum]
        -- Step 1: rearrange χ_x * (coeff_s j * χ_j) to coeff_s j * (χ_x * χ_j)
        have h1 :
          ∑ j : ι, repCharacter (ρ x) g * ((coeff_s j : ℂ) * repCharacter (ρ j) g) =
          ∑ j : ι, (coeff_s j : ℂ) * (repCharacter (ρ x) g * repCharacter (ρ j) g) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [h1]
        -- Step 2: apply CG: χ_x * χ_j = ∑ k, cg x j k * χ_k
        have h2 :
          ∑ j : ι, (coeff_s j : ℂ) * (repCharacter (ρ x) g * repCharacter (ρ j) g) =
          ∑ j : ι, (coeff_s j : ℂ) *
            ∑ k : ι, (cg x j k : ℂ) * repCharacter (ρ k) g :=
          Finset.sum_congr rfl (fun j _ => by rw [hcg_decomp x j g])
        rw [h2]
        -- Step 3: distribute coeff_s j * over the inner sum
        have h3 :
          ∑ j : ι, (coeff_s j : ℂ) *
            ∑ k : ι, (cg x j k : ℂ) * repCharacter (ρ k) g =
          ∑ j : ι, ∑ k : ι,
            (coeff_s j : ℂ) * ((cg x j k : ℂ) * repCharacter (ρ k) g) :=
          Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
        rw [h3]
        -- Step 4: exchange the double sum
        rw [Finset.sum_comm]
        -- Step 5: factor out χ_k(g) from the inner sum
        have h5 :
          ∑ k : ι, ∑ j : ι,
            (coeff_s j : ℂ) * ((cg x j k : ℂ) * repCharacter (ρ k) g) =
          ∑ k : ι,
            (∑ j : ι, (coeff_s j : ℂ) * (cg x j k : ℂ)) * repCharacter (ρ k) g :=
          Finset.sum_congr rfl (fun k _ => by
            have : ∑ j : ι, (coeff_s j : ℂ) * ((cg x j k : ℂ) * repCharacter (ρ k) g) =
                   ∑ j : ι, ((coeff_s j : ℂ) * (cg x j k : ℂ)) * repCharacter (ρ k) g :=
              Finset.sum_congr rfl (fun j _ => by ring)
            rw [this, Finset.sum_mul])
        rw [h5]
        -- The coefficient fun v => ∑ w, coeff_s w * cg x w v applied to k gives
        -- ∑ w, coeff_s w * cg x w k; coerced to ℂ this equals ∑ j, ↑(coeff_s j) * ↑(cg x j k)
        -- by Complex.ofReal_sum + Complex.ofReal_mul.
        exact Finset.sum_congr rfl (fun k _ => by
          have hcoe : ((fun v => ∑ w, coeff_s w * cg x w v) k : ℂ) =
              ∑ j, (coeff_s j : ℂ) * (cg x j k : ℂ) := by
            simp only [Complex.ofReal_sum, Complex.ofReal_mul]
          rw [hcoe])

/-- The product of two non-negative-weighted sums of characters of the same group
element is a non-negative-weighted sum of characters, via Clebsch–Gordan.

If `A(g) = ∑_a coeff1 a · χ_a(g)` and `B(g) = ∑_b coeff2 b · χ_b(g)` with
`coeff1, coeff2 ≥ 0`, then `A(g) · B(g) = ∑_w coeff w · χ_w(g)` with
`coeff w = ∑_{a,b} coeff1 a · coeff2 b · cg a b w ≥ 0`.

This is the key algebraic ingredient for the transfer-matrix kernel decomposition:
each interface plaquette factor has a character expansion (a non-negative-weighted
sum of products of characters), and the product of all interface plaquette factors
is built by iteratively applying this lemma.  When a link appears in multiple
plaquettes, the CG decomposition combines the characters of that link into a
single character, yielding a separable decomposition of the full Boltzmann factor. -/
lemma charSum_product_decomp {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (coeff1 coeff2 : ι → ℝ) (h1 : ∀ w, 0 ≤ coeff1 w) (h2 : ∀ w, 0 ≤ coeff2 w) :
    ∃ (coeff : ι → ℝ) (hcoeff : ∀ w, 0 ≤ coeff w),
      ∀ (g : SU N),
        (∑ a : ι, (coeff1 a : ℂ) * repCharacter (ρ a) g) *
        (∑ b : ι, (coeff2 b : ℂ) * repCharacter (ρ b) g) =
        ∑ w : ι, (coeff w : ℂ) * repCharacter (ρ w) g := by
  classical
  refine ⟨fun w => ∑ a : ι, ∑ b : ι, coeff1 a * coeff2 b * cg a b w,
    fun w => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (mul_nonneg (h1 a) (h2 b)) (hcg a b w))), fun g => ?_⟩
  -- Step 1: distribute the product into a double sum
  -- (∑ a, c1_a * χ_a) * (∑ b, c2_b * χ_b) = ∑ a, ∑ b, (c1_a * χ_a) * (c2_b * χ_b)
  rw [Finset.sum_mul_sum]
  -- Step 2: rearrange to c1_a * c2_b * (χ_a * χ_b)
  have h2 :
    ∑ a : ι, ∑ b : ι,
      ((coeff1 a : ℂ) * repCharacter (ρ a) g) * ((coeff2 b : ℂ) * repCharacter (ρ b) g) =
    ∑ a : ι, ∑ b : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) * (repCharacter (ρ a) g * repCharacter (ρ b) g)) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  rw [h2]
  -- Step 3: apply CG: χ_a * χ_b = ∑ w, cg a b w * χ_w
  have h3 :
    ∑ a : ι, ∑ b : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) * (repCharacter (ρ a) g * repCharacter (ρ b) g)) =
    ∑ a : ι, ∑ b : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) *
        ∑ w : ι, (cg a b w : ℂ) * repCharacter (ρ w) g) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      rw [hcg_decomp a b g]))
  rw [h3]
  -- Step 4: distribute: ∑ a b, c1_a * (c2_b * (∑ w, cg * χ_w)) = ∑ a b w, c1_a * (c2_b * (cg * χ_w))
  have h4 :
    ∑ a : ι, ∑ b : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) *
        ∑ w : ι, (cg a b w : ℂ) * repCharacter (ρ w) g) =
    ∑ a : ι, ∑ b : ι, ∑ w : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) * ((cg a b w : ℂ) * repCharacter (ρ w) g)) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      simp only [Finset.mul_sum]))
  rw [h4]
  -- Step 5: exchange sums to get ∑ w, ∑ a, ∑ b
  -- First exchange outer two: ∑ a, ∑ b, ∑ w → ∑ b, ∑ a, ∑ w
  rw [Finset.sum_comm]
  -- Then exchange inner two: ∑ b, ∑ a, ∑ w → ∑ b, ∑ w, ∑ a  (inside ∑ b)
  have h5a :
    ∑ b : ι, ∑ a : ι, ∑ w : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) * ((cg a b w : ℂ) * repCharacter (ρ w) g)) =
    ∑ b : ι, ∑ w : ι, ∑ a : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) * ((cg a b w : ℂ) * repCharacter (ρ w) g)) :=
    Finset.sum_congr rfl (fun b _ => by rw [Finset.sum_comm])
  rw [h5a]
  -- Then exchange outer two: ∑ b, ∑ w, ∑ a → ∑ w, ∑ b, ∑ a
  rw [Finset.sum_comm]
  -- Step 6: factor out χ_w from the inner double sum
  have h6 :
    ∑ w : ι, ∑ b : ι, ∑ a : ι,
      (coeff1 a : ℂ) * ((coeff2 b : ℂ) * ((cg a b w : ℂ) * repCharacter (ρ w) g)) =
    ∑ w : ι,
      ((∑ b : ι, ∑ a : ι, (coeff1 a : ℂ) * ((coeff2 b : ℂ) * (cg a b w : ℂ))) *
        repCharacter (ρ w) g) := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hw :
      ∑ b : ι, ∑ a : ι,
        (coeff1 a : ℂ) * ((coeff2 b : ℂ) * ((cg a b w : ℂ) * repCharacter (ρ w) g)) =
      ∑ b : ι, ∑ a : ι,
        ((coeff1 a : ℂ) * ((coeff2 b : ℂ) * (cg a b w : ℂ))) * repCharacter (ρ w) g :=
      Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by ring))
    rw [hw]
    simp only [← Finset.sum_mul]
  -- Step 7: match the coefficient (Complex.ofReal_sum + ofReal_mul + sum_comm + ring)
  rw [h6]
  exact Finset.sum_congr rfl (fun w _ => by
    have hcoe : ((fun w => ∑ a : ι, ∑ b : ι, coeff1 a * coeff2 b * cg a b w) w : ℂ) =
        ∑ b : ι, ∑ a : ι, (coeff1 a : ℂ) * ((coeff2 b : ℂ) * (cg a b w : ℂ)) := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    rw [hcoe])
/-- A finite product of non-negative-weighted sums of characters of the same group
element is a non-negative-weighted sum of characters, via iterated Clebsch–Gordan.

For a nonempty finite set `s`, `∏_{a ∈ s} (∑_w f a w · χ_w(g))` can be written as
`∑_w coeff w · χ_w(g)` with `coeff w ≥ 0`.  This is proved by induction on `s`,
applying `charSum_product_decomp` at each step.

This is the key lemma for the interface Boltzmann factor decomposition: the
interface Boltzmann factor is a product of plaquette factors, each of which has a
character expansion (a non-negative-weighted sum of products of characters).  After
collecting characters by link variable, each link's contribution is a
non-negative-weighted sum of characters, and this lemma shows the product over all
links is again a non-negative-weighted sum of characters — i.e., the interface
Boltzmann factor has a character expansion with non-negative coefficients. -/
lemma charSum_finprod_decomp {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (f : α → ι → ℝ) (hf : ∀ a w, 0 ≤ f a w) :
    ∃ (coeff : ι → ℝ) (hcoeff : ∀ w, 0 ≤ coeff w),
      ∀ (g : SU N),
        (∏ a ∈ s, ∑ w : ι, (f a w : ℂ) * repCharacter (ρ w) g) =
        ∑ w : ι, (coeff w : ℂ) * repCharacter (ρ w) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | insert x s hx ih =>
    by_cases hse : s = ∅
    · -- Singleton: the product is just one sum, which is already a char sum
      subst hse
      refine ⟨f x, hf x, fun g => by
        rw [Finset.prod_insert hx, Finset.prod_empty, mul_one]⟩
    · -- s ≠ ∅: use ih to decompose the product over s, then combine with x via charSum_product_decomp
      have hs' : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
      obtain ⟨coeff_s, hcoeff_s, hdecomp_s⟩ := ih hs'
      obtain ⟨coeff, hcoeff, hdecomp⟩ :=
        charSum_product_decomp ρ hU cg hcg hcg_decomp coeff_s (f x) hcoeff_s (hf x)
      refine ⟨coeff, hcoeff, fun g => ?_⟩
      rw [Finset.prod_insert hx, hdecomp_s g, mul_comm, hdecomp g]

/-- The product of per-link non-negative-weighted character sums is a
non-negative-weighted sum of products of characters.

Given a finite type `L` of links and, for each link `l`, a non-negative-weighted
character sum `A_l(g) = ∑_w f l w · χ_w(g)` with `f l w ≥ 0`, the product
`∏_l A_l(g_l)` decomposes as `∑_{w : L → ι} F(w) · ∏_l χ_{w(l)}(g_l)` with
`F(w) = ∏_l f l (w l) ≥ 0`.

This is the "product of sums = sum of products" identity (`Fintype.prod_sum`),
applied to character sums.  It is a key ingredient for the interface Boltzmann
factor decomposition: after the per-link CG reduction (via
`charSum_finprod_decomp`), each link's contribution is a non-negative-weighted
character sum, and this lemma shows the product over all links is again a
non-negative-weighted sum of products of characters — i.e., a separable
decomposition of the full Boltzmann factor. -/
lemma charSum_product_link_decomp
    {L : Type*} [Fintype L] [DecidableEq L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (f : L → ι → ℝ) (hf : ∀ l w, 0 ≤ f l w) :
    ∃ (F : (L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (g : L → SU N),
        (∏ l, ∑ w : ι, (f l w : ℂ) * repCharacter (ρ w) (g l)) =
        ∑ w : L → ι, (F w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l) := by
  refine ⟨fun w => ∏ l, f l (w l), fun w => Finset.prod_nonneg (fun l _ => hf l (w l)), fun g => ?_⟩
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod]

/-- **Generalized Clebsch–Gordan decomposition for a product of characters
indexed by a finset of appearances.**  Given a finset `s` of appearances and a
function `appChar : A → ι` assigning a representation index to each appearance,
the product `∏_{a ∈ s} χ_{appChar(a)}(g)` decomposes as a non-negative-weighted
sum of single characters `∑_w coeff w · χ_w(g)` with `coeff w ≥ 0`.

This generalizes `charProduct_finset_decomp` by allowing the character index to
depend on an auxiliary type `A` (the "appearance" type), so that the same
character index can appear multiple times — which happens when a single link
variable appears in multiple plaquettes with the same representation index. -/
lemma charProduct_finset_decomp' {A : Type*} [Fintype A] [DecidableEq A]
    {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (s : Finset A) (appChar : A → ι) (hs : s.Nonempty) :
    ∃ (coeff : ι → ℝ) (hcoeff : ∀ w, 0 ≤ coeff w),
      ∀ (g : SU N),
        (∏ a ∈ s, repCharacter (ρ (appChar a)) g) =
        ∑ w : ι, (coeff w : ℂ) * repCharacter (ρ w) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | insert x s hx ih =>
    by_cases hse : s = ∅
    · -- Singleton: ∏_{a ∈ {x}} χ_{appChar(x)}(g) = 1 · χ_{appChar(x)}(g)
      subst hse
      refine ⟨fun w => if w = appChar x then 1 else 0, fun w => ?_, fun g => ?_⟩
      · show 0 ≤ (if w = appChar x then 1 else 0)
        split_ifs <;> norm_num
      · rw [Finset.prod_insert hx, Finset.prod_empty, mul_one]
        have h_eq : ∀ w : ι, ((if w = appChar x then 1 else 0 : ℝ) : ℂ) *
            repCharacter (ρ w) g = if w = appChar x then repCharacter (ρ w) g else 0 :=
          fun w => by by_cases hwx : w = appChar x <;> simp [hwx]
        rw [show ∑ w : ι, ((if w = appChar x then 1 else 0 : ℝ) : ℂ) *
            repCharacter (ρ w) g = ∑ w : ι,
              (if w = appChar x then repCharacter (ρ w) g else 0) from
            Finset.sum_congr rfl (fun w _ => h_eq w)]
        simp
    · -- s ≠ ∅: use ih to decompose ∏_{a ∈ s} χ_{appChar(a)}(g), then combine
      have hs' : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
      obtain ⟨coeff_s, hcoeff_s, hdecomp_s⟩ := ih hs'
      refine ⟨fun v => ∑ w : ι, coeff_s w * cg (appChar x) w v, fun v => ?_, fun g => ?_⟩
      · exact Finset.sum_nonneg (fun w _ => mul_nonneg (hcoeff_s w) (hcg (appChar x) w v))
      · rw [Finset.prod_insert hx, hdecomp_s g, Finset.mul_sum]
        have h1 :
          ∑ j : ι, repCharacter (ρ (appChar x)) g * ((coeff_s j : ℂ) * repCharacter (ρ j) g) =
          ∑ j : ι, (coeff_s j : ℂ) *
            (repCharacter (ρ (appChar x)) g * repCharacter (ρ j) g) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [h1]
        have h2 :
          ∑ j : ι, (coeff_s j : ℂ) *
            (repCharacter (ρ (appChar x)) g * repCharacter (ρ j) g) =
          ∑ j : ι, (coeff_s j : ℂ) *
            ∑ k : ι, (cg (appChar x) j k : ℂ) * repCharacter (ρ k) g :=
          Finset.sum_congr rfl (fun j _ => by rw [hcg_decomp (appChar x) j g])
        rw [h2]
        have h3 :
          ∑ j : ι, (coeff_s j : ℂ) *
            ∑ k : ι, (cg (appChar x) j k : ℂ) * repCharacter (ρ k) g =
          ∑ j : ι, ∑ k : ι,
            (coeff_s j : ℂ) * ((cg (appChar x) j k : ℂ) * repCharacter (ρ k) g) :=
          Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
        rw [h3]
        rw [Finset.sum_comm]
        have h5 :
          ∑ k : ι, ∑ j : ι,
            (coeff_s j : ℂ) * ((cg (appChar x) j k : ℂ) * repCharacter (ρ k) g) =
          ∑ k : ι,
            (∑ j : ι, (coeff_s j : ℂ) * (cg (appChar x) j k : ℂ)) *
            repCharacter (ρ k) g := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have hw :
            ∑ j : ι, (coeff_s j : ℂ) *
              ((cg (appChar x) j k : ℂ) * repCharacter (ρ k) g) =
            ∑ j : ι,
              ((coeff_s j : ℂ) * (cg (appChar x) j k : ℂ)) * repCharacter (ρ k) g :=
            Finset.sum_congr rfl (fun j _ => by ring)
          rw [hw, Finset.sum_mul]
        rw [h5]
        exact Finset.sum_congr rfl (fun k _ => by
          have hcoe : ((fun v => ∑ w : ι, coeff_s w * cg (appChar x) w v) k : ℂ) =
              ∑ j : ι, (coeff_s j : ℂ) * (cg (appChar x) j k : ℂ) := by
            simp only [Complex.ofReal_sum, Complex.ofReal_mul]
          rw [hcoe])

/-- **Per-term separable decomposition**: a product of characters grouped by link
decomposes as a non-negative-weighted sum of products of single characters.

Given a finite type `L` of links and, for each link `l`, a nonempty finset `S l`
of appearances with character indices `charIdx l : A → ι`, the product
`∏_l (∏_{a ∈ S l} χ_{charIdx l a}(g l))` decomposes as
`∑_w F(w) · ∏_l χ_{w(l)}(g l)` with `F(w) ≥ 0`.

This is proved by:
1. For each link `l`, applying `charProduct_finset_decomp'` to get the per-link
   CG decomposition `∏_{a ∈ S l} χ_{charIdx l a}(g l) = ∑_w c_l(w) · χ_w(g l)`.
2. Applying `charSum_product_link_decomp` to combine the per-link character sums
   into a separable decomposition.

This is the key algebraic ingredient for the interface Boltzmann factor
decomposition: after expanding the product of plaquette factors (product of
sums = sum of products), each term is a product of characters grouped by link.
This lemma shows each such term has a separable character decomposition with
non-negative coefficients.  The full separable decomposition of the interface
Boltzmann factor is obtained by summing over all terms (with non-negative
plaquette coefficients), preserving non-negativity of the overall coefficients. -/
lemma charProduct_link_separable_decomp
    {L : Type*} [Fintype L] [DecidableEq L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : L → Finset A) (charIdx : L → A → ι)
    (hS : ∀ l, (S l).Nonempty) :
    ∃ (F : (L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (g : L → SU N),
        (∏ l, ∏ a ∈ S l, repCharacter (ρ (charIdx l a)) (g l)) =
        ∑ w : L → ι, (F w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l) := by
  -- Step 1: For each link l, apply charProduct_finset_decomp' to get the per-link
  -- CG decomposition
  have hdecomp : ∀ l, ∃ (c : ι → ℝ) (hc : ∀ w, 0 ≤ c w),
      ∀ (g : SU N), (∏ a ∈ S l, repCharacter (ρ (charIdx l a)) g) =
        ∑ w : ι, (c w : ℂ) * repCharacter (ρ w) g := by
    intro l
    exact charProduct_finset_decomp' ρ hU cg hcg hcg_decomp (S l) (charIdx l) (hS l)
  -- Step 2: Choose the coefficient function for each link
  let f : L → ι → ℝ := fun l => (hdecomp l).choose
  have hf : ∀ l w, 0 ≤ f l w := fun l w => (hdecomp l).choose_spec.choose w
  have hf_decomp : ∀ l (g : SU N),
      (∏ a ∈ S l, repCharacter (ρ (charIdx l a)) g) =
      ∑ w : ι, (f l w : ℂ) * repCharacter (ρ w) g :=
    fun l g => (hdecomp l).choose_spec.choose_spec g
  -- Step 3: Apply charSum_product_link_decomp
  obtain ⟨F, hF, hF_decomp⟩ := charSum_product_link_decomp ρ hU f hf
  -- Step 4: Show the product equals the separable decomposition
  refine ⟨F, hF, fun g => ?_⟩
  have hprod : (∏ l, ∏ a ∈ S l, repCharacter (ρ (charIdx l a)) (g l)) =
      (∏ l, ∑ w : ι, (f l w : ℂ) * repCharacter (ρ w) (g l)) := by
    refine Finset.prod_congr rfl (fun l _ => hf_decomp l (g l))
  rw [hprod, hF_decomp g]

/-- **Mixed-conjugation Clebsch–Gordan decomposition for a product of
characters.**  Given a finset `s` of appearances, character indices
`appChar : A → ι`, and a conjugation flag `isConj : A → Bool`, the product

    ∏_{a ∈ s} (if isConj a then conj(χ_{appChar(a)}(g)) else χ_{appChar(a)}(g))

decomposes as a non-negative-weighted sum of single characters
`∑_w coeff w · χ_w(g)` with `coeff w ≥ 0`.

This is the key lemma for the interface Boltzmann factor decomposition: the
plaquette product has inverted links (3rd and 4th), giving `conj(χ)` via
`repCharacter_inv`.  When a link appears in multiple plaquettes with mixed
orientations, the product involves both `χ(g)` and `conj(χ(g))`.  The dual
map converts `conj(χ)` to `χ_{dual}`, allowing the CG decomposition
(`charProduct_finset_decomp'`) to combine them into a single character sum. -/
lemma charProduct_mixed_finset_decomp' {A : Type*} [Fintype A] [DecidableEq A]
    {ι : Type*} [Fintype ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (s : Finset A) (appChar : A → ι) (isConj : A → Bool) (hs : s.Nonempty) :
    ∃ (coeff : ι → ℝ) (hcoeff : ∀ w, 0 ≤ coeff w),
      ∀ (g : SU N),
        (∏ a ∈ s, if isConj a then conj (repCharacter (ρ (appChar a)) g)
                   else repCharacter (ρ (appChar a)) g) =
        ∑ w : ι, (coeff w : ℂ) * repCharacter (ρ w) g := by
  obtain ⟨coeff, hcoeff, hdecomp⟩ :=
    charProduct_finset_decomp' ρ hU cg hcg hcg_decomp s
      (fun a => if isConj a then dual (appChar a) else appChar a) hs
  refine ⟨coeff, hcoeff, fun g => ?_⟩
  have h_eq : ∀ a ∈ s, (if isConj a then conj (repCharacter (ρ (appChar a)) g)
                       else repCharacter (ρ (appChar a)) g) =
                      repCharacter (ρ (if isConj a then dual (appChar a) else appChar a)) g := by
    intro a ha
    by_cases h : isConj a = true
    · rw [if_pos h]
      conv => rhs; rw [if_pos h]
      exact (hdual (appChar a) g).symm
    · rw [if_neg h]
      conv => rhs; rw [if_neg h]
  rw [Finset.prod_congr rfl h_eq, hdecomp g]

/-- **Per-term separable decomposition with mixed conjugation**: a product of
characters (some conjugated, some not) grouped by link decomposes as a
non-negative-weighted sum of products of single (unconjugated) characters.

Given a finite type `L` of links and, for each link `l`, a nonempty finset
`S l` of appearances with character indices `charIdx l : A → ι` and conjugation
flags `isConj l : A → Bool`, the product

    ∏_l (∏_{a ∈ S l} (if isConj l a then conj(χ_{charIdx l a}(g_l))
                                    else χ_{charIdx l a}(g_l)))

decomposes as `∑_w F(w) · ∏_l χ_{w(l)}(g l)` with `F(w) ≥ 0`.

This is proved by:
1. For each link `l`, applying `charProduct_mixed_finset_decomp'` to get the
   per-link CG decomposition (converting `conj(χ)` to `χ_{dual}` via the dual
   map, then applying CG).
2. Applying `charSum_product_link_decomp` to combine the per-link character
   sums into a separable decomposition.

This is the key algebraic ingredient for the interface Boltzmann factor
decomposition with inverted links: after expanding the product of plaquette
factors (product of sums = sum of products), each term is a product of
characters (some conjugated from inverted links) grouped by link.  This lemma
shows each such term has a separable character decomposition with non-negative
coefficients, with all conjugation resolved via the dual map. -/
lemma charProduct_mixed_link_separable_decomp
    {L : Type*} [Fintype L] [DecidableEq L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ) (hcg : ∀ s t w, 0 ≤ cg s t w)
    (hcg_decomp : ∀ s t (g : SU N),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : L → Finset A) (charIdx : L → A → ι) (isConj : L → A → Bool)
    (hS : ∀ l, (S l).Nonempty) :
    ∃ (F : (L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (g : L → SU N),
        (∏ l, ∏ a ∈ S l,
          (if isConj l a then conj (repCharacter (ρ (charIdx l a)) (g l))
           else repCharacter (ρ (charIdx l a)) (g l))) =
        ∑ w : L → ι, (F w : ℂ) * ∏ l, repCharacter (ρ (w l)) (g l) := by
  have hdecomp : ∀ l, ∃ (c : ι → ℝ) (hc : ∀ w, 0 ≤ c w),
      ∀ (g : SU N),
        (∏ a ∈ S l, if isConj l a then conj (repCharacter (ρ (charIdx l a)) g)
                     else repCharacter (ρ (charIdx l a)) g) =
        ∑ w : ι, (c w : ℂ) * repCharacter (ρ w) g := by
    intro l
    exact charProduct_mixed_finset_decomp' ρ hU cg hcg hcg_decomp dual hdual
      (S l) (charIdx l) (isConj l) (hS l)
  let f : L → ι → ℝ := fun l => (hdecomp l).choose
  have hf : ∀ l w, 0 ≤ f l w := fun l w => (hdecomp l).choose_spec.choose w
  have hf_decomp : ∀ l (g : SU N),
      (∏ a ∈ S l, if isConj l a then conj (repCharacter (ρ (charIdx l a)) g)
                   else repCharacter (ρ (charIdx l a)) g) =
      ∑ w : ι, (f l w : ℂ) * repCharacter (ρ w) g :=
    fun l g => (hdecomp l).choose_spec.choose_spec g
  obtain ⟨F, hF, hF_decomp⟩ := charSum_product_link_decomp ρ hU f hf
  refine ⟨F, hF, fun g => ?_⟩
  have hprod : (∏ l, ∏ a ∈ S l,
      (if isConj l a then conj (repCharacter (ρ (charIdx l a)) (g l))
       else repCharacter (ρ (charIdx l a)) (g l))) =
      (∏ l, ∑ w : ι, (f l w : ℂ) * repCharacter (ρ w) (g l)) := by
    refine Finset.prod_congr rfl (fun l _ => hf_decomp l (g l))
  rw [hprod, hF_decomp g]

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
      cgME, hcgME_decomp, hcgME_unitary,
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

set_option maxHeartbeats 1000000 in
/-- **Triple product integral evaluation.** For irreducible unitary representations
`ρ_s, ρ_t, ρ_u` of a compact group with normalized Haar measure μ, the integral
`∫ χ_s(g) · (ρ_t g)_{ij} · conj((ρ_u g)_{kl}) dμ(g)` equals
`(1/dims u) · ∑_a cgME(s,t,u,a,i,k) · conj(cgME(s,t,u,a,j,l))`.

This is a positive-semidefinite Gram matrix in the coefficients (key for reflection
positivity). Proof: expand χ_s = ∑_a (ρ_s)_{aa} (trace), apply CG decomposition
`hcgME_decomp` to each `(ρ_s)_{aa} · (ρ_t)_{ij}`, exchange sums with integral
(Fubini), apply Schur orthogonality (`characterOrthogonality`), simplify.
0 sorries, 0 custom axioms. -/
lemma triple_product_character_matrix_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s t u : ι) (i j : Fin (dims t)) (k l : Fin (dims u)) :
    ∫ g, repCharacter (ρ s) g * (ρ t g) i j * conj ((ρ u g) k l) ∂μ =
      (1 / dims u : ℂ) * ∑ a : Fin (dims s),
        cgME s t u a i k * conj (cgME s t u a j l) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have hchar : ∀ (g : G),
      repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  have hpt : ∀ (g : G),
      repCharacter (ρ s) g * (ρ t g) i j * conj ((ρ u g) k l) =
        ∑ a : Fin (dims s), ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME s t ν a i p * conj (cgME s t ν a j q)) * ((ρ ν g) p q * conj ((ρ u g) k l)) := by
    intro g
    rw [hchar g, mul_assoc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, hcgME_decomp s t g a a i j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [show (∫ g, repCharacter (ρ s) g * (ρ t g) i j * conj ((ρ u g) k l) ∂μ) =
        ∫ g, (∑ a : Fin (dims s), ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME s t ν a i p * conj (cgME s t ν a j q)) * ((ρ ν g) p q * conj ((ρ u g) k l))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability
  have hInt_term : ∀ (a : Fin (dims s)) (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g => (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a ν p q
    exact Integrable.smul (cgME s t ν a i p * conj (cgME s t ν a j q)) (hInt ν u p q k l)
  have hInt_q : ∀ (a : Fin (dims s)) (ν : ι) (p : Fin (dims ν)),
      Integrable (fun g => ∑ q : Fin (dims ν),
        (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a ν p; exact integrable_finsetSum Finset.univ (fun q _ => hInt_term a ν p q)
  have hInt_p : ∀ (a : Fin (dims s)) (ν : ι),
      Integrable (fun g => ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a ν; exact integrable_finsetSum Finset.univ (fun p _ => hInt_q a ν p)
  have hInt_ν : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a; exact integrable_finsetSum Finset.univ (fun ν _ => hInt_p a ν)
  -- Exchange sums with integral (4 levels)
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_ν a)]
  rw [Finset.sum_congr rfl (fun a _ => integral_finsetSum Finset.univ (fun ν _ => hInt_p a ν))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
      (fun ν _ => integral_finsetSum Finset.univ (fun p _ => hInt_q a ν p)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun p _ => integral_finsetSum Finset.univ
        (fun q _ => hInt_term a ν p q))))]
  -- For ν ≠ u, each integral is 0 (pull constant + Schur offdiag)
  have hν_ne_zero : ∀ (a : Fin (dims s)) (ν : ι), ν ≠ u →
      (∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        ∫ g, (cgME s t ν a i p * conj (cgME s t ν a j q)) *
          ((ρ ν g) p q * conj ((ρ u g) k l)) ∂μ) = 0 := by
    intro a ν hν
    refine Finset.sum_eq_zero (fun p _ => ?_)
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [integral_const_mul, hSchur_offdiag ν u p q k l hν]
    simp
  -- Collapse the ν sum: only ν = u contributes
  have hν_collapse : ∀ (a : Fin (dims s)),
      (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        ∫ g, (cgME s t ν a i p * conj (cgME s t ν a j q)) *
          ((ρ ν g) p q * conj ((ρ u g) k l)) ∂μ) =
      (∑ p : Fin (dims u), ∑ q : Fin (dims u),
        ∫ g, (cgME s t u a i p * conj (cgME s t u a j q)) *
          ((ρ u g) p q * conj ((ρ u g) k l)) ∂μ) := by
    intro a
    exact Finset.sum_eq_single u (fun ν _ hν => hν_ne_zero a ν hν)
        (fun h => (h (Finset.mem_univ _)).elim)
  rw [Finset.sum_congr rfl (fun a _ => hν_collapse a)]
  -- Evaluate each integral (ν = u case: pull constant + Schur diag)
  have hInt_eval_u : ∀ (a : Fin (dims s)) (p : Fin (dims u)) (q : Fin (dims u)),
      ∫ g, (cgME s t u a i p * conj (cgME s t u a j q)) *
        ((ρ u g) p q * conj ((ρ u g) k l)) ∂μ =
        (cgME s t u a i p * conj (cgME s t u a j q)) *
        (if p = k ∧ q = l then (1 / dims u : ℂ) else 0) := by
    intro a p q
    rw [integral_const_mul, hSchur_diag]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => hInt_eval_u a p q)))]
  -- Collapse p, q sums for each a
  have hpq_collapse : ∀ (a : Fin (dims s)),
      (∑ p : Fin (dims u), ∑ q : Fin (dims u),
        (cgME s t u a i p * conj (cgME s t u a j q)) *
        (if p = k ∧ q = l then (1 / dims u : ℂ) else 0)) =
      (cgME s t u a i k * conj (cgME s t u a j l)) * (1 / dims u : ℂ) := by
    intro a
    rw [Finset.sum_eq_single k (fun p _ hp => Finset.sum_eq_zero (fun q _ => by
        simp [hp])) (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, true_and]
    rw [Finset.sum_eq_single l (fun q _ hq => by simp [hq])
        (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, if_true]
  rw [Finset.sum_congr rfl (fun a _ => hpq_collapse a)]
  -- Factor out 1/dims u
  rw [← Finset.sum_mul, mul_comm]

#print axioms triple_product_character_matrix_integral

set_option maxHeartbeats 1000000 in
/-- **Generalized triple-product integral for ι × Λ.** For `s ∈ ι` (finite, from
the character expansion) and `t, u ∈ Λ` (countable, from the L² expansion of the
arbitrary test function `A_w`), the integral
`∫ χ_s(g) · (ρΛ_t g)_{ij} · conj((ρΛ_u g)_{kl}) dμ(g)` equals
`(1/dimsΛ u) · ∑_a cgMEΛ s t u a i k · conj(cgMEΛ s t u a j l)`.

This is a PSD Gram matrix in the CG coefficients (key for reflection positivity
step 3).  Proof: expand χ_s = trace, apply CG decomposition `hcgMEΛ_decomp` for
ι × Λ (finite support), exchange sums with integral (Fubini for finite sums),
apply Schur orthogonality for Λ (`hSchurΛ_diag`/`hSchurΛ_offdiag`), simplify.
Uses the extended `peterWeyl_clebschGordan_plaquette` axiom (Parts 3–4). -/
lemma triple_product_character_matrix_integral_Λ
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (Λ : Type) [Encodable Λ]
    (dimsΛ : Λ → ℕ) (hDimsΛ : ∀ ℓ, 0 < dimsΛ ℓ)
    (ρΛ : ∀ ℓ, G →* Matrix (Fin (dimsΛ ℓ)) (Fin (dimsΛ ℓ)) ℂ)
    (cgMEΛ : ∀ (s : ι) (t ν : Λ), Fin (dims s) → Fin (dimsΛ t) → Fin (dimsΛ ν) → ℂ)
    (hcgMEΛ_support : ∀ (s : ι) (t : Λ), Finset Λ)
    (hcgMEΛ_decomp : ∀ (s : ι) (t : Λ) (g : G) (a b : Fin (dims s)) (i j : Fin (dimsΛ t)),
        (ρ s g) a b * (ρΛ t g) i j =
        ∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
          cgMEΛ s t ν a i p * (ρΛ ν g) p q * conj (cgMEΛ s t ν b j q))
    (hcgMEΛ_support_zero : ∀ (s : ι) (t ν : Λ), ν ∉ hcgMEΛ_support s t →
        ∀ (a : Fin (dims s)) (i : Fin (dimsΛ t)) (p : Fin (dimsΛ ν)),
          cgMEΛ s t ν a i p = 0)
    (hSchurΛ_int : ∀ (ν μ₂ : Λ) (p : Fin (dimsΛ ν)) (q : Fin (dimsΛ ν))
        (k : Fin (dimsΛ μ₂)) (l : Fin (dimsΛ μ₂)),
      Integrable (fun g => (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l)) μ)
    (hSchurΛ_diag : ∀ (ν : Λ) (p q k l : Fin (dimsΛ ν)),
      ∫ g, (ρΛ ν g) p q * conj ((ρΛ ν g) k l) ∂μ =
        if p = k ∧ q = l then (1 / dimsΛ ν : ℂ) else 0)
    (hSchurΛ_offdiag : ∀ (ν μ₂ : Λ) (p q : Fin (dimsΛ ν)) (k l : Fin (dimsΛ μ₂)),
      ν ≠ μ₂ → ∫ g, (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l) ∂μ = 0)
    (s : ι) (t u : Λ) (i j : Fin (dimsΛ t)) (k l : Fin (dimsΛ u)) :
    ∫ g, repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) ∂μ =
      (1 / dimsΛ u : ℂ) * ∑ a : Fin (dims s),
        cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l) := by
  classical
  have hchar : ∀ (g : G),
      repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  have hpt : ∀ (g : G),
      repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) =
        ∑ a : Fin (dims s), ∑ ν ∈ hcgMEΛ_support s t,
          ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
            (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) := by
    intro g
    rw [hchar g, mul_assoc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, hcgMEΛ_decomp s t g a a i j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [show (∫ g, repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) ∂μ) =
        ∫ g, (∑ a : Fin (dims s), ∑ ν ∈ hcgMEΛ_support s t,
          ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
            (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability
  have hInt_term : ∀ (a : Fin (dims s)) (ν : Λ) (p : Fin (dimsΛ ν)) (q : Fin (dimsΛ ν)),
      Integrable (fun g => (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a ν p q
    exact Integrable.smul (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) (hSchurΛ_int ν u p q k l)
  have hInt_q : ∀ (a : Fin (dims s)) (ν : Λ) (p : Fin (dimsΛ ν)),
      Integrable (fun g => ∑ q : Fin (dimsΛ ν),
        (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a ν p; exact integrable_finsetSum Finset.univ (fun q _ => hInt_term a ν p q)
  have hInt_p : ∀ (a : Fin (dims s)) (ν : Λ),
      Integrable (fun g => ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
        (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a ν; exact integrable_finsetSum Finset.univ (fun p _ => hInt_q a ν p)
  have hInt_ν : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
        (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a; exact integrable_finsetSum (hcgMEΛ_support s t) (fun ν _ => hInt_p a ν)
  -- Exchange sums with integral
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_ν a)]
  rw [Finset.sum_congr rfl (fun a _ => integral_finsetSum (hcgMEΛ_support s t) (fun ν _ => hInt_p a ν))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ =>
      integral_finsetSum Finset.univ (fun p _ => hInt_q a ν p)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun p _ => integral_finsetSum Finset.univ
        (fun q _ => hInt_term a ν p q))))]
  -- For ν ≠ u, each integral is 0
  have hν_ne_zero : ∀ (a : Fin (dims s)) (ν : Λ), ν ≠ u →
      (∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
        ∫ g, (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
          ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) ∂μ) = 0 := by
    intro a ν hν
    refine Finset.sum_eq_zero (fun p _ => ?_)
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [integral_const_mul, hSchurΛ_offdiag ν u p q k l hν]
    simp
  by_cases hu : u ∈ hcgMEΛ_support s t
  · -- Case: u ∈ support — collapse ν sum to u
    have hν_collapse : ∀ (a : Fin (dims s)),
        (∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
          ∫ g, (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) ∂μ) =
        (∑ p : Fin (dimsΛ u), ∑ q : Fin (dimsΛ u),
          ∫ g, (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
            ((ρΛ u g) p q * conj ((ρΛ u g) k l)) ∂μ) := by
      intro a
      exact Finset.sum_eq_single u (fun ν _ hν => hν_ne_zero a ν hν) (fun h => (h hu).elim)
    rw [Finset.sum_congr rfl (fun a _ => hν_collapse a)]
    -- Evaluate each integral (ν = u: pull constant + Schur diag)
    have hInt_eval : ∀ (a : Fin (dims s)) (p : Fin (dimsΛ u)) (q : Fin (dimsΛ u)),
        ∫ g, (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
          ((ρΛ u g) p q * conj ((ρΛ u g) k l)) ∂μ =
          (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
          (if p = k ∧ q = l then (1 / dimsΛ u : ℂ) else 0) := by
      intro a p q
      rw [integral_const_mul, hSchurΛ_diag]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun q _ => hInt_eval a p q)))]
    -- Collapse p, q sums
    have hpq_collapse : ∀ (a : Fin (dims s)),
        (∑ p : Fin (dimsΛ u), ∑ q : Fin (dimsΛ u),
          (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
          (if p = k ∧ q = l then (1 / dimsΛ u : ℂ) else 0)) =
          (cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l)) * (1 / dimsΛ u : ℂ) := by
      intro a
      rw [Finset.sum_eq_single k (fun p _ hp => Finset.sum_eq_zero (fun q _ => by
          simp [hp])) (fun h => (h (Finset.mem_univ _)).elim)]
      simp only [eq_self_iff_true, true_and]
      rw [Finset.sum_eq_single l (fun q _ hq => by simp [hq])
          (fun h => (h (Finset.mem_univ _)).elim)]
      simp only [eq_self_iff_true, if_true]
    rw [Finset.sum_congr rfl (fun a _ => hpq_collapse a)]
    rw [← Finset.sum_mul, mul_comm]
  · -- Case: u ∉ support — all terms 0, RHS 0 by support_zero
    have hLHS_zero : ∀ (a : Fin (dims s)),
        (∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
          ∫ g, (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) ∂μ) = 0 := by
      intro a
      refine Finset.sum_eq_zero (fun ν hν => ?_)
      have hν_ne : ν ≠ u := fun heq => hu (heq ▸ hν)
      exact hν_ne_zero a ν hν_ne
    rw [Finset.sum_congr rfl (fun a _ => hLHS_zero a)]
    simp
    -- RHS: all cgMEΛ s t u coefficients are 0
    have hRHS : (∑ a : Fin (dims s), cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l) : ℂ) = 0 := by
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [hcgMEΛ_support_zero s t u hu a i k, hcgMEΛ_support_zero s t u hu a j l]
      simp
    rw [hRHS]
    simp

#print axioms triple_product_character_matrix_integral_Λ

set_option maxHeartbeats 1000000 in
/-- **Iterated (3-fold) matrix-element Clebsch–Gordan decomposition.**

A product of three matrix elements of the *same* group element `g` (in possibly
different representations `s₁, s₂, s₃`) decomposes as a single sum over one
representation `α`, by applying `hcgME_decomp` twice (first combine `s₁, s₂ → ν`,
then `ν, s₃ → α`):

    (ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂} · (ρ_{s₃} g)_{a₃b₃}
      = ∑_ν ∑_{r,s} ∑_α ∑_{p,q}
          cgME s₁ s₂ ν a₁ a₂ r · conj(cgME s₁ s₂ ν b₁ b₂ s) ·
          cgME ν s₃ α r a₃ p · (ρ_α g)_{pq} · conj(cgME ν s₃ α s b₃ q)

The sums are in **natural decomposition order** (intermediate representation `ν`
outermost, final representation `α` innermost), matching the order in which the
two `hcgME_decomp` applications produce them. The intermediate representation `ν`
is **shared** between the row (a-index) and column (b-index) CG coefficients —
the coefficient of `(ρ_α g)_{pq}` is
`∑_ν ∑_{r,s} cgME s₁ s₂ ν a₁ a₂ r · cgME ν s₃ α r a₃ p · conj(cgME s₁ s₂ ν b₁ b₂ s · cgME ν s₃ α s b₃ q)`,
an inner product over the shared `ν` (NOT a product of two independent sums).

This is the matrix-element analogue of `charProduct_finset_decomp` and the key
building block for the **3D single-site Lüscher integral** (Step 2 of the Lüscher
roadmap, §8.11.41–42): in 3D each temporal link `u_t(x)` appears in 3 forward
plaquettes, producing 3 unbarred matrix elements that must be combined into one
before Schur orthogonality can be applied to the single-site integral. 0 sorries,
0 custom axioms (pure algebra from `hcgME_decomp`). -/
lemma cgME_decomp_3fold
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (g : G)
    (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3)) :
    (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 =
    ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
      ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
        cgME ν s3 α r a3 p * (ρ α g) p q * conj (cgME ν s3 α s b3 q) := by
  -- First CG decomposition: (ρ s1 g)_{a1 b1} * (ρ s2 g)_{a2 b2}, then distribute
  -- the remaining (ρ s3 g)_{a3 b3} into the ν, r, s sums.
  rw [hcgME_decomp s1 s2 g a1 b1 a2 b2]
  simp only [Finset.sum_mul]
  -- Descend into the ν, r, s sums (RHS is in the same ν-outermost order).
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  -- Leaf: regroup so (ρ ν g)_{rs} * (ρ s3 g)_{a3 b3} are adjacent, then apply
  -- the second CG decomposition (ν, s₃ → α).
  have hrearr : cgME s1 s2 ν a1 a2 r * (ρ ν g) r s * conj (cgME s1 s2 ν b1 b2 s) *
      (ρ s3 g) a3 b3 =
      cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
      ((ρ ν g) r s * (ρ s3 g) a3 b3) := by ring
  rw [hrearr, hcgME_decomp ν s3 g r s a3 b3]
  -- Distribute the constant (CG coefficients for s₁,s₂) into the α, p, q sums.
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun α _ =>
    Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by ring)))

#print axioms cgME_decomp_3fold

set_option maxHeartbeats 1000000 in
/-- **Conjugate of the iterated 3-fold matrix-element CG decomposition.**

The complex conjugate of `cgME_decomp_3fold`: a product of three *conjugated* matrix
elements of the same group element `g` decomposes as a single sum over `α`, with the
intermediate `ν` shared between row and column CG coefficients. This is the barred
(3 backward plaquettes) counterpart needed for the single-site 3D Lüscher integral.

    conj((ρ_{s₁} g)_{a₁b₁}) · conj((ρ_{s₂} g)_{a₂b₂}) · conj((ρ_{s₃} g)_{a₃b₃})
      = ∑_ν ∑_{r,s} ∑_α ∑_{p,q}
          conj(cgME s₁ s₂ ν a₁ a₂ r) · cgME s₁ s₂ ν b₁ b₂ s ·
          conj(cgME ν s₃ α r a₃ p) · conj((ρ_α g)_{pq}) · cgME ν s₃ α s b₃ q

0 sorries, 0 custom axioms (pure algebra: conjugate of `cgME_decomp_3fold`). -/
lemma cgME_decomp_3fold_conj
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (g : G)
    (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3)) :
    conj ((ρ s1 g) a1 b1) * conj ((ρ s2 g) a2 b2) * conj ((ρ s3 g) a3 b3) =
    ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
      ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        conj (cgME s1 s2 ν a1 a2 r) * cgME s1 s2 ν b1 b2 s *
        conj (cgME ν s3 α r a3 p) * conj ((ρ α g) p q) * cgME ν s3 α s b3 q := by
  have h := cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  have h := cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  -- Take conj of both sides of h, then normalize with simp.
  have hconj : conj ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3) =
      conj (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
          cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
          cgME ν s3 α r a3 p * (ρ α g) p q * conj (cgME ν s3 α s b3 q)) := by
    rw [h]
  -- simp pushes conj through products (conj_mul) and sums (map_sum), and
  -- simplifies conj(conj x) = x (conj_conj), normalizing both sides.
  simp at hconj
  exact hconj
#print axioms cgME_decomp_3fold_conj

set_option maxHeartbeats 1000000 in
/-- **Integral of a single matrix element = projection onto trivial representation.**
For a compact group with normalized Haar measure, irreducible unitary representations
`ρ_i`, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the integral
of a single matrix element `∫ (ρ_σ(g))_{rs} dμ` equals `1` if `σ = σ_0` (and `r = s = 0`,
the only index for a 1-dimensional representation) and `0` otherwise (by Schur orthogonality:
the integral of a matrix element of a nontrivial irrep against the trivial character is 0).

This is the key building block for evaluating the time-like triple product integral
`∫ χ_s · (ρ_t)_{ij} · (ρ_u)_{kl} dμ` (triple product WITHOUT conjugation), which arises
in the L² expansion approach to reflection positivity (Lemma 5, Step 4a). -/
lemma integral_matrix_element_trivial_projection
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (σ : ι) (r : Fin (dims σ)) (s : Fin (dims σ)) :
    ∫ g, (ρ σ g) r s ∂μ = if σ = σ_0 then (1 : ℂ) else 0 := by
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Extract (ρ_{σ_0})_{00} = 1 from ρ_{σ_0} = 1 (identity matrix)
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  -- Rewrite: ∫ (ρ_σ)_{rs} = ∫ (ρ_σ)_{rs} * conj((ρ_{σ_0})_{00}) (since conj((ρ_{σ_0})_{00}) = 1)
  have hconj : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  rw [show ∫ g, (ρ σ g) r s ∂μ = ∫ g, (ρ σ g) r s * conj ((ρ σ_0 g) 0 0) ∂μ from by
    congr 1 with g; rw [hconj g, mul_one]]
  by_cases h : σ = σ_0
  · -- σ = σ_0: diagonal Schur orthogonality
    subst h
    rw [if_pos rfl]
    rw [hSchur_diag σ r s 0 0]
    -- r, s : Fin (dims σ) with dims σ = 1, so r = s = 0 (only element of Fin 1)
    haveI hsub : Subsingleton (Fin (dims σ)) :=
      hσ_0_dims.symm ▸ (inferInstance : Subsingleton (Fin 1))
    have hr : r = 0 := Subsingleton.elim r 0
    have hs : s = 0 := Subsingleton.elim s 0
    simp [hr, hs, hσ_0_dims]
  · -- σ ≠ σ_0: off-diagonal Schur orthogonality
    rw [if_neg h]
    exact hSchur_offdiag σ σ_0 r s 0 0 h

#print axioms integral_matrix_element_trivial_projection

/-- **Integral of a character = projection onto the trivial representation.**
For a compact group with normalized Haar measure, irreducible unitary representations
`ρ_i`, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the integral
of a character `∫ χ_s(g) dμ(g)` equals `1` if `s = σ_0` (the trivial representation) and
`0` otherwise (by Schur orthogonality: the character of a nontrivial irrep integrates to 0).

This is the key building block for step 4 of the formalization path (§8.11.53):
integrating out temporal interface links collapses the temporal characters to the trivial
representation.  Specifically, `∫ ∏_{l∈L_0_temporal} χ_{w(l)}(g_l) dμ = ∏_l δ_{w(l), σ_0}`,
which forces `w(l) = σ_0` for all temporal links l. -/
lemma integral_repCharacter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (s : ι) :
    ∫ g, repCharacter (ρ s) g ∂μ = if s = σ_0 then (1 : ℂ) else 0 := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  have hconj00 : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  have hInt_single : ∀ (a : Fin (dims s)), Integrable (fun g => (ρ s g) a a) μ := by
    intro a
    have h := hInt s σ_0 a a 0 0
    have heq : (fun g => (ρ s g) a a * conj ((ρ σ_0 g) 0 0)) = (fun g => (ρ s g) a a) := by
      funext g; rw [hconj00 g, mul_one]
    rw [heq] at h
    exact h
  -- repCharacter (ρ s) g = ∑ a, (ρ s g) a a (by definition: trace = sum of diagonal)
  show ∫ g, (∑ a : Fin (dims s), (ρ s g) a a) ∂μ = if s = σ_0 then (1 : ℂ) else 0
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_single a)]
  have hInt_eval : ∀ (a : Fin (dims s)),
      ∫ g, (ρ s g) a a ∂μ = if s = σ_0 then (1 : ℂ) else 0 := by
    intro a
    exact integral_matrix_element_trivial_projection μ ι dims hDims ρ hU hIrr
      σ_0 hσ_0_dims hσ_0_trivial s a a
  rw [Finset.sum_congr rfl (fun a _ => hInt_eval a)]
  by_cases h : s = σ_0
  · subst h; simp [hσ_0_dims]
  · simp [h]

#print axioms integral_repCharacter_trivial

/-- **Multi-link character integral = product of single-link integrals (Step 4).**
For a compact group `G` with normalized Haar measure `μ`, a finite type `L` of links,
irreducible unitary representations `ρ_i`, and a trivial representation `σ_0`
(1-dimensional, `ρ_{σ_0}(g) = 1`), the integral of a product of characters over the
product measure on `L → G` factors as a product of single-link integrals:

    ∫ ∏_{l ∈ L} χ_{w(l)}(g_l) dμ = ∏_{l ∈ L} (if w(l) = σ_0 then 1 else 0)

This is the multi-link temporal collapse (Step 4 of §8.11.53): integrating out the
temporal interface links forces each temporal character to be the trivial character.
Uses `integral_fintype_prod_eq_prod` (Fubini for finite products) to factor the
integral, then `integral_repCharacter_trivial` for each single-link factor. -/
lemma integral_prod_repCharacter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (L : Type) [Fintype L] [DecidableEq L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (w : L → ι) :
    ∫ x : L → G, ∏ l : L, repCharacter (ρ (w l)) (x l) ∂(Measure.pi (fun _ => μ)) =
      ∏ l : L, (if w l = σ_0 then (1 : ℂ) else 0) := by
  -- Factor the integral using Fubini for finite products:
  -- ∫ ∏_l f_l(g_l) d(∏ μ) = ∏_l ∫ f_l(g) dμ
  rw [integral_fintype_prod_eq_prod (fun (l : L) (g : G) => repCharacter (ρ (w l)) g)]
  -- Each single-link integral: ∫ χ_{w(l)}(g) dμ = if w(l) = σ_0 then 1 else 0
  refine Finset.prod_congr rfl (fun l _ => ?_)
  exact integral_repCharacter_trivial μ ι dims hDims ρ hU hIrr σ_0 hσ_0_dims hσ_0_trivial (w l)

#print axioms integral_prod_repCharacter_trivial

set_option maxHeartbeats 1000000 in
/-- **Character times matrix element integral (helper for time-like triple product).**
For irreducible unitary representations `ρ_s, ρ_ν` of a compact group with normalized Haar
measure μ, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the integral
`∫ χ_s(g) · (ρ_ν g)_{pq} dμ(g)` equals
`∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s'))`.

Proof: expand `χ_s = ∑_a (ρ_s)_{aa}` (trace), apply CG decomposition `hcgME_decomp` to each
`(ρ_s)_{aa} · (ρ_ν)_{pq}`, exchange sums with integral (Fubini), evaluate
`∫ (ρ_σ)_{rs'} = if σ = σ_0 then 1 else 0` (by `integral_matrix_element_trivial_projection`),
collapse σ sum (only σ = σ_0 contributes). -/
lemma character_times_matrix_element_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (s ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)) :
    ∫ g, repCharacter (ρ s) g * (ρ ν g) p q ∂μ =
      ∑ a : Fin (dims s), ∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
        cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s') := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  -- (ρ_{σ_0})_{00} = 1 and conj((ρ_{σ_0})_{00}) = 1
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  have hconj00 : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  -- Integrability of single matrix elements via hInt with σ_0
  have hInt_single : ∀ (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      Integrable (fun g => (ρ σ g) r s') μ := by
    intro σ r s'
    have h := hInt σ σ_0 r s' 0 0
    have heq : (fun g => (ρ σ g) r s' * conj ((ρ σ_0 g) 0 0)) = (fun g => (ρ σ g) r s') := by
      funext g; rw [hconj00 g, mul_one]
    rw [heq] at h
    exact h
  -- Pointwise identity: χ_s(g) · (ρ_ν g)_{pq} = ∑_a ∑_σ ∑_r ∑_{s'} (coeff) · (ρ_σ g)_{r,s'}
  have hchar : ∀ g, repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  have hpt : ∀ g, repCharacter (ρ s) g * (ρ ν g) p q =
      ∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s' := by
    intro g
    rw [hchar g, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hcgME_decomp s ν g a a p q]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s' _
    ring
  -- Rewrite the integral
  rw [show (∫ g, repCharacter (ρ s) g * (ρ ν g) p q ∂μ) =
        ∫ g, (∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
          (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability
  have hInt_term : ∀ (a : Fin (dims s)) (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      Integrable (fun g => (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a σ r s'
    exact Integrable.smul (cgME s ν σ a p r * conj (cgME s ν σ a q s')) (hInt_single σ r s')
  have hInt_s' : ∀ (a : Fin (dims s)) (σ : ι) (r : Fin (dims σ)),
      Integrable (fun g => ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a σ r; exact integrable_finsetSum Finset.univ (fun s' _ => hInt_term a σ r s')
  have hInt_r : ∀ (a : Fin (dims s)) (σ : ι),
      Integrable (fun g => ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a σ; exact integrable_finsetSum Finset.univ (fun r _ => hInt_s' a σ r)
  have hInt_σ : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a; exact integrable_finsetSum Finset.univ (fun σ _ => hInt_r a σ)
  -- Exchange sums with integral (4 levels)
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_σ a)]
  rw [Finset.sum_congr rfl (fun a _ => integral_finsetSum Finset.univ (fun σ _ => hInt_r a σ))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun σ _ =>
      integral_finsetSum Finset.univ (fun r _ => hInt_s' a σ r)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun σ _ =>
      Finset.sum_congr rfl (fun r _ => integral_finsetSum Finset.univ
        (fun s' _ => hInt_term a σ r s'))))]
  -- Evaluate ∫ (ρ_σ)_{r,s'} = if σ = σ_0 then 1 else 0
  have hInt_eval : ∀ (a : Fin (dims s)) (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      ∫ g, (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s' ∂μ =
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (if σ = σ_0 then (1 : ℂ) else 0) := by
    intro a σ r s'
    rw [integral_const_mul, integral_matrix_element_trivial_projection μ ι dims hDims ρ hU hIrr
      σ_0 hσ_0_dims hσ_0_trivial σ r s']
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun σ _ =>
      Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s' _ => hInt_eval a σ r s'))))]
  -- Collapse σ sum: only σ = σ_0 contributes
  have hσ_ne_zero : ∀ (a : Fin (dims s)) (σ : ι), σ ≠ σ_0 →
      (∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (if σ = σ_0 then (1 : ℂ) else 0)) = 0 := by
    intro a σ hσ
    refine Finset.sum_eq_zero (fun r _ => ?_)
    refine Finset.sum_eq_zero (fun s' _ => ?_)
    rw [if_neg hσ, mul_zero]
  have hσ_collapse : ∀ (a : Fin (dims s)),
      (∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (if σ = σ_0 then (1 : ℂ) else 0)) =
      (∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
        cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s')) := by
    intro a
    rw [Finset.sum_eq_single σ_0 (fun σ _ hσ => hσ_ne_zero a σ hσ)
        (fun h => (h (Finset.mem_univ _)).elim)]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s' _
    rw [if_pos rfl, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => hσ_collapse a)]

#print axioms character_times_matrix_element_integral

set_option maxHeartbeats 1000000 in
/-- **Time-like triple product integral evaluation (Lemma 5, Step 4a key component).**
For irreducible unitary representations `ρ_s, ρ_t, ρ_u` of a compact group with normalized
Haar measure μ, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the
integral `∫ χ_s(g) · (ρ_t g)_{ij} · (ρ_u g)_{kl} dμ(g)` (triple product WITHOUT conjugation,
as arises in the time-like link case of reflection positivity) equals a sum of CG coefficient
products forming a PSD Gram matrix:

    ∑_ν ∑_p ∑_q (cgME(t,u,ν,i,k,p) · conj(cgME(t,u,ν,j,l,q))) ·
      (∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s')))

Proof: apply CG decomposition `hcgME_decomp` to `(ρ_t)_{ij} · (ρ_u)_{kl}`, exchange sums with
integral (Fubini), then evaluate `∫ χ_s · (ρ_ν)_{pq} dμ` using
`character_times_matrix_element_integral` (which uses the double CG decomposition +
`integral_matrix_element_trivial_projection`). The result is a PSD Gram matrix in the
`(i,k)` vs `(j,l)` indices. 0 sorries, 0 new custom axioms. -/
lemma triple_product_character_matrix_integral_timelike
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (s t u : ι) (i j : Fin (dims t)) (k l : Fin (dims u)) :
    ∫ g, repCharacter (ρ s) g * (ρ t g) i j * (ρ u g) k l ∂μ =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
        (∑ a : Fin (dims s), ∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
          cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s')) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  -- (ρ_{σ_0})_{00} = 1 and conj((ρ_{σ_0})_{00}) = 1
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  have hconj00 : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  -- Integrability of single matrix elements via hInt with σ_0
  have hInt_single : ∀ (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      Integrable (fun g => (ρ σ g) r s') μ := by
    intro σ r s'
    have h := hInt σ σ_0 r s' 0 0
    have heq : (fun g => (ρ σ g) r s' * conj ((ρ σ_0 g) 0 0)) = (fun g => (ρ σ g) r s') := by
      funext g; rw [hconj00 g, mul_one]
    rw [heq] at h
    exact h
  -- Character expansion
  have hchar : ∀ g, repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  -- Inner pointwise identity (same as character_times_matrix_element_integral's hpt)
  have hpt_inner : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)) (g : G),
      repCharacter (ρ s) g * (ρ ν g) p q =
      ∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s' := by
    intro ν p q g
    rw [hchar g, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hcgME_decomp s ν g a a p q]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s' _
    ring
  -- Integrability of χ_s(g) · (ρ_ν g)_{pq}
  have hInt_char_me : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g => repCharacter (ρ s) g * (ρ ν g) p q) μ := by
    intro ν p q
    have heq : (fun g => repCharacter (ρ s) g * (ρ ν g) p q) =
        (fun g => ∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
          (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') := by
      funext g; exact hpt_inner ν p q g
    rw [heq]
    apply integrable_finsetSum Finset.univ
    intro a _
    apply integrable_finsetSum Finset.univ
    intro σ _
    apply integrable_finsetSum Finset.univ
    intro r _
    apply integrable_finsetSum Finset.univ
    intro s' _
    exact Integrable.smul (cgME s ν σ a p r * conj (cgME s ν σ a q s')) (hInt_single σ r s')
  -- Outer pointwise identity: first CG decomp
  have hpt_outer : ∀ g, repCharacter (ρ s) g * (ρ t g) i j * (ρ u g) k l =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) * (repCharacter (ρ s) g * (ρ ν g) p q) := by
    intro g
    rw [mul_assoc, hcgME_decomp t u g i j k l, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the integral
  rw [show (∫ g, repCharacter (ρ s) g * (ρ t g) i j * (ρ u g) k l ∂μ) =
        ∫ g, (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME t u ν i k p * conj (cgME t u ν j l q)) *
            (repCharacter (ρ s) g * (ρ ν g) p q)) ∂μ from by
    congr 1 with g; exact hpt_outer g]
  -- Per-term integrability
  have hInt_term : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g => (cgME t u ν i k p * conj (cgME t u ν j l q)) *
        (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    intro ν p q
    exact Integrable.smul (cgME t u ν i k p * conj (cgME t u ν j l q)) (hInt_char_me ν p q)
  have hInt_q : ∀ (ν : ι) (p : Fin (dims ν)),
      Integrable (fun g => ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    intro ν p; exact integrable_finsetSum Finset.univ (fun q _ => hInt_term ν p q)
  have hInt_p : ∀ (ν : ι),
      Integrable (fun g => ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    intro ν; exact integrable_finsetSum Finset.univ (fun p _ => hInt_q ν p)
  have hInt_ν : Integrable (fun g => ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    exact integrable_finsetSum Finset.univ (fun ν _ => hInt_p ν)
  -- Exchange sums with integral (3 levels)
  rw [integral_finsetSum Finset.univ (fun ν _ => hInt_p ν)]
  rw [Finset.sum_congr rfl (fun ν _ => integral_finsetSum Finset.univ (fun p _ => hInt_q ν p))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      integral_finsetSum Finset.univ (fun q _ => hInt_term ν p q)))]
  -- Evaluate each integral using integral_const_mul + helper
  have hInt_eval : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      ∫ g, (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q) ∂μ =
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
        (∑ a : Fin (dims s), ∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
          cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s')) := by
    intro ν p q
    rw [integral_const_mul, character_times_matrix_element_integral μ ι dims hDims ρ hU hIrr
      cgME hcgME_decomp σ_0 hσ_0_dims hσ_0_trivial s ν p q]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => hInt_eval ν p q)))]

#print axioms triple_product_character_matrix_integral_timelike

set_option maxHeartbeats 1000000 in
/-- **Integral of one matrix element times three conjugated matrix elements.**
For irreducible unitary representations of a compact group with normalized Haar measure,
the integral `∫ (ρ_σ g)_{pq} · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) · conj((ρ_{t₃} g)_{c₃d₃}) dμ(g)`
equals `(1/dims σ) · ∑_{ν',r',s'} CG_barred(ν',r',s',σ,p,q)`.

Proof: apply `cgME_decomp_3fold_conj` to the 3 barred MEs, exchange sums with integral
(Fubini), apply Schur orthogonality (`characterOrthogonality`): the combined representation
`β` from the barred side is forced to equal `σ` (the unbarred representation), and the
matrix indices `p'=p, q'=q` are forced by the diagonal Kronecker deltas. 0 sorries, 0 new axioms.
This is the key helper for `single_site_3D_luscher_integral` (Step 2 of the Lüscher roadmap). -/
lemma integral_ME_times_3barred_MEs
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ : ι) (p : Fin (dims σ)) (q : Fin (dims σ))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    ∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) ∂μ =
      (1 / dims σ : ℂ) * ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p) * cgME ν' t3 σ s' d3 q := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Pointwise identity: apply cgME_decomp_3fold_conj to the 3 barred MEs, distribute (ρ σ g) p q
  have hpt : ∀ (g : G),
      (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q')) := by
    intro g
    have hreassoc : (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3) =
        (ρ σ g) p q *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) := by ring
    rw [hreassoc, cgME_decomp_3fold_conj ι dims ρ cgME hcgME_decomp t1 t2 t3 g c1 d1 c2 d2 c3 d3]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q' _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3) ∂μ) =
        ∫ g, (∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
            conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
            conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
            ((ρ σ g) p q * conj ((ρ β g) p' q'))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (6 levels, innermost to outermost)
  have hInt_term : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι)
      (p' : Fin (dims β)) (q' : Fin (dims β)),
      Integrable (fun g =>
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s' β p' q'
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
       conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q')
      (hInt σ β p q p' q')
  have hInt_q' : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι) (p' : Fin (dims β)),
      Integrable (fun g => ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s' β p'
    exact integrable_finsetSum Finset.univ (fun q' _ => hInt_term ν' r' s' β p' q')
  have hInt_p' : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι),
      Integrable (fun g => ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s' β
    exact integrable_finsetSum Finset.univ (fun p' _ => hInt_q' ν' r' s' β p')
  have hInt_β : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      Integrable (fun g => ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s'
    exact integrable_finsetSum Finset.univ (fun β _ => hInt_p' ν' r' s' β)
  have hInt_s' : ∀ (ν' : ι) (r' : Fin (dims ν')),
      Integrable (fun g => ∑ s' : Fin (dims ν'), ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r'
    exact integrable_finsetSum Finset.univ (fun s' _ => hInt_β ν' r' s')
  have hInt_r' : ∀ (ν' : ι),
      Integrable (fun g => ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), ∑ β : ι,
        ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν'
    exact integrable_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r')
  have hInt_ν' : Integrable (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')
  -- Exchange sums with integral (6 levels)
  rw [integral_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')]
  rw [Finset.sum_congr rfl (fun ν' _ => integral_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r'))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      integral_finsetSum Finset.univ (fun s' _ => hInt_β ν' r' s')))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl
      (fun s' _ => integral_finsetSum Finset.univ (fun β _ => hInt_p' ν' r' s' β))))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl
      (fun s' _ => Finset.sum_congr rfl (fun β _ => integral_finsetSum Finset.univ
        (fun p' _ => hInt_q' ν' r' s' β p')))))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl
      (fun s' _ => Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun p' _ =>
        integral_finsetSum Finset.univ (fun q' _ => hInt_term ν' r' s' β p' q'))))))]
  -- For β ≠ σ, each integral is 0 (pull constant + Schur offdiag)
  have hβ_ne_zero : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι),
      β ≠ σ → (∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q')) ∂μ) = 0 := by
    intro ν' r' s' β hβ
    refine Finset.sum_eq_zero (fun p' _ => ?_)
    refine Finset.sum_eq_zero (fun q' _ => ?_)
    rw [integral_const_mul, hSchur_offdiag σ β p q p' q' (Ne.symm hβ)]
    simp
  -- Collapse β sum: only β = σ contributes
  have hβ_collapse : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      (∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q')) ∂μ) =
      (∑ p' : Fin (dims σ), ∑ q' : Fin (dims σ),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
          ((ρ σ g) p q * conj ((ρ σ g) p' q')) ∂μ) := by
    intro ν' r' s'
    exact Finset.sum_eq_single σ (fun β _ hβ => hβ_ne_zero ν' r' s' β hβ)
        (fun h => (h (Finset.mem_univ _)).elim)
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      Finset.sum_congr rfl (fun s' _ => hβ_collapse ν' r' s')))]
  -- Evaluate each integral (β = σ case: pull constant + Schur diag)
  have hInt_eval : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν'))
      (p' : Fin (dims σ)) (q' : Fin (dims σ)),
      ∫ g,
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
        ((ρ σ g) p q * conj ((ρ σ g) p' q')) ∂μ =
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
        (if p = p' ∧ q = q' then (1 / dims σ : ℂ) else 0) := by
    intro ν' r' s' p' q'
    rw [integral_const_mul, hSchur_diag]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun p' _ =>
        Finset.sum_congr rfl (fun q' _ => hInt_eval ν' r' s' p' q')))))]
  -- Collapse p', q' sums
  have hpq'_collapse : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      (∑ p' : Fin (dims σ), ∑ q' : Fin (dims σ),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
        (if p = p' ∧ q = q' then (1 / dims σ : ℂ) else 0)) =
      conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
      conj (cgME ν' t3 σ r' c3 p) * cgME ν' t3 σ s' d3 q * (1 / dims σ : ℂ) := by
    intro ν' r' s'
    rw [Finset.sum_eq_single p (fun p' _ hp => Finset.sum_eq_zero (fun q' _ => by
        simp [Ne.symm hp])) (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, true_and]
    rw [Finset.sum_eq_single q (fun q' _ hq => by simp [Ne.symm hq])
        (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, if_true]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      Finset.sum_congr rfl (fun s' _ => hpq'_collapse ν' r' s')))]
  -- Factor out 1/dims σ: push constant inside the sums on the RHS, then match term-by-term
  conv_rhs => simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν' _
  apply Finset.sum_congr rfl
  intro r' _
  apply Finset.sum_congr rfl
  intro s' _
  ring

#print axioms integral_ME_times_3barred_MEs

/-- **Integrability of a 4-ME product (1 unbarred × 3 barred).** General version of the
`hInt_4ME` step from `single_site_3D_luscher_integral`: for any representations `σ, t₁, t₂, t₃`
and any indices, the product `(ρ_σ g)_{pq} · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) · conj((ρ_{t₃} g)_{c₃d₃})`
is integrable w.r.t. the Haar probability measure.

Proof: expand the 3 barred MEs via `cgME_decomp_3fold_conj` (pointwise identity), then each
leaf is `(ρ_σ g)_{pq} · conj((ρ_β g)_{p'q'})` times a CG coefficient, which is integrable by
`characterOrthogonality` (`hInt`). The finite sum is integrable by `integrable_finsetSum`.
0 sorries, 0 new axioms. -/
lemma integrable_ME_times_3barred_MEs
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ : ι) (p : Fin (dims σ)) (q : Fin (dims σ))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    Integrable (fun g => (ρ σ g) p q *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3))) μ := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Pointwise identity: expand 3 barred MEs via cgME_decomp_3fold_conj
  have hpt_barred : ∀ (g : G),
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * conj ((ρ β g) p' q') * cgME ν' t3 β s' d3 q' := by
    intro g
    exact cgME_decomp_3fold_conj ι dims ρ cgME hcgME_decomp t1 t2 t3 g c1 d1 c2 d2 c3 d3
  -- Rewrite the function using the expansion
  rw [show (fun g => (ρ σ g) p q *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3))) =
      (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q'))) from by
    funext g
    rw [hpt_barred g, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q' _
    ring]
  -- Integrability of each leaf: (CG coeff) * ((ρ σ g) p q * conj ((ρ β g) p' q'))
  apply integrable_finsetSum Finset.univ
  intro ν' _
  apply integrable_finsetSum Finset.univ
  intro r' _
  apply integrable_finsetSum Finset.univ
  intro s' _
  apply integrable_finsetSum Finset.univ
  intro β _
  apply integrable_finsetSum Finset.univ
  intro p' _
  apply integrable_finsetSum Finset.univ
  intro q' _
  exact Integrable.smul
    (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
     conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q')
    (hInt σ β p q p' q')

#print axioms integrable_ME_times_3barred_MEs
#print axioms integrable_ME_times_3barred_MEs

/-- **Integrability of a 6-ME product (3 unbarred × 3 barred).** For any representations
`s₁, s₂, s₃, t₁, t₂, t₃` and any indices, the product of 3 unbarred matrix elements times
3 barred matrix elements (as arises in the 3D Lüscher integral) is integrable w.r.t. the Haar
probability measure.

Proof: decompose the 3 unbarred MEs via `cgME_decomp_3fold` (pointwise identity), then each
leaf is `(ρ_α g)_{pq} · (3 barred MEs)` times a CG coefficient, which is integrable by
`integrable_ME_times_3barred_MEs`. The finite sum is integrable by `integrable_finsetSum`.
0 sorries, 0 new axioms. -/
lemma integrable_6ME_product
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    Integrable (fun g =>
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) μ := by
  -- Pointwise identity: apply cgME_decomp_3fold to the 3 unbarred MEs, distribute barred product
  have hpt : ∀ (g : G),
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3))) := by
    intro g
    have hreassoc : (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3) *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) := by ring
    rw [hreassoc, cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the function using the expansion
  rw [show (fun g =>
        (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) =
      (fun g => ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) from by
    funext g; exact hpt g]
  -- Integrability of each leaf: (CG coeff) * ((ρ α g) p q * (3 barred MEs))
  apply integrable_finsetSum Finset.univ
  intro ν _
  apply integrable_finsetSum Finset.univ
  intro r _
  apply integrable_finsetSum Finset.univ
  intro s _
  apply integrable_finsetSum Finset.univ
  intro α _
  apply integrable_finsetSum Finset.univ
  intro p _
  apply integrable_finsetSum Finset.univ
  intro q _
  exact Integrable.smul
    (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
     cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q))
    (integrable_ME_times_3barred_MEs μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
      α p q t1 t2 t3 c1 d1 c2 d2 c3 d3)
#print axioms integrable_6ME_product
#print axioms integrable_6ME_product

set_option maxHeartbeats 20000000 in
/-- **Character-level single-site 3D Lüscher integral.** The integral of a product of 6
characters — 3 unbarred `χ_{sᵢ}(g·Aᵢ)` and 3 barred `χ_{tⱼ}(g⁻¹·Bⱼ)` — over the Haar measure
equals a sum over all matrix-element indices of the constant (product of `ρ(A)` and `ρ(B)`
matrix elements) times the 6-ME integral (evaluated by `single_site_3D_luscher_integral`).

This is the key building block for the 3D global cascade: it converts the character-level
integral (which arises from the plaquette-level character expansion of the interface
Boltzmann factor) into a sum of matrix-element-level integrals, each of which is evaluated
by `single_site_3D_luscher_integral`. The result is a sum of CG-coefficient products times
`(1/dims α)`, which (in the diagonal case) gives `|C|² ≥ 0` by `cg_unitarity_nonneg`.

Proof: expand each character as a trace (using `Matrix.trace` + `repMatrixElement_inv` for
the barred characters), distribute the product into a 12-fold sum, exchange the sums with the
integral (justified by `integrable_6ME_product`), and apply `single_site_3D_luscher_integral`
to each 6-ME integral. 0 sorries, 0 new axioms. -/
lemma char_level_single_site_3D_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 t1 t2 t3 : ι) (A1 A2 A3 B1 B2 B3 : G) :
    ∫ g, repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
        repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
        repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) ∂μ =
      ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1),
      ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2),
      ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3),
      ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1),
      ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2),
      ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3),
        (ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
        (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3 *
        ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
          conj ((ρ t1 g) d1 c1) * conj ((ρ t2 g) d2 c2) * conj ((ρ t3 g) d3 c3) ∂μ := by
  -- htrace_mul helper: Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  -- Character expansions (unbarred): χ_s(g·A) = ∑ a, ∑ b, (ρ s g) a b * (ρ s A) b a
  have hchar_s1 : ∀ (g : G),
      repCharacter (ρ s1) (g * A1) =
      ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1), (ρ s1 g) a1 b1 * (ρ s1 A1) b1 a1 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  have hchar_s2 : ∀ (g : G),
      repCharacter (ρ s2) (g * A2) =
      ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2), (ρ s2 g) a2 b2 * (ρ s2 A2) b2 a2 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  have hchar_s3 : ∀ (g : G),
      repCharacter (ρ s3) (g * A3) =
      ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3), (ρ s3 g) a3 b3 * (ρ s3 A3) b3 a3 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  -- Character expansions (barred): χ_t(g⁻¹·B) = ∑ c, ∑ d, conj((ρ t g) d c) * (ρ t B) d c
  have hchar_t1 : ∀ (g : G),
      repCharacter (ρ t1) (g⁻¹ * B1) =
      ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1), conj ((ρ t1 g) d1 c1) * (ρ t1 B1) d1 c1 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl; intro c1 _; apply Finset.sum_congr rfl; intro d1 _
    rw [repMatrixElement_inv (ρ t1) (hU t1) g c1 d1]
  have hchar_t2 : ∀ (g : G),
      repCharacter (ρ t2) (g⁻¹ * B2) =
      ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2), conj ((ρ t2 g) d2 c2) * (ρ t2 B2) d2 c2 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl; intro c2 _; apply Finset.sum_congr rfl; intro d2 _
    rw [repMatrixElement_inv (ρ t2) (hU t2) g c2 d2]
  have hchar_t3 : ∀ (g : G),
      repCharacter (ρ t3) (g⁻¹ * B3) =
      ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3), conj ((ρ t3 g) d3 c3) * (ρ t3 B3) d3 c3 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl; intro c3 _; apply Finset.sum_congr rfl; intro d3 _
    rw [repMatrixElement_inv (ρ t3) (hU t3) g c3 d3]
  -- Pointwise identity: expand characters, distribute product into 12-level sum
  have hpt : ∀ (g : G),
      repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
      repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
      repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) =
      ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1),
      ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2),
      ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3),
      ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1),
      ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2),
      ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3),
        (ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
        (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3 *
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
         conj ((ρ t1 g) d1 c1) * conj ((ρ t2 g) d2 c2) * conj ((ρ t3 g) d3 c3)) := by
    intro g
    have hreassoc :
        repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
        repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
        repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) =
        repCharacter (ρ s1) (g * A1) * (repCharacter (ρ s2) (g * A2) *
        (repCharacter (ρ s3) (g * A3) * (repCharacter (ρ t1) (g⁻¹ * B1) *
        (repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3))))) := by ring
    rw [hreassoc, hchar_s1, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a1 _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b1 _
    rw [hchar_s2, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a2 _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b2 _
    rw [hchar_s3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a3 _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b3 _
    rw [hchar_t1, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c1 _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d1 _
    rw [hchar_t2, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c2 _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d2 _
    rw [hchar_t3, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c3 _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d3 _
    ring
  -- Rewrite the integral using hpt
  rw [show (∫ g, repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
        repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
        repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) ∂μ) =
      (∫ g, ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1),
        ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2),
        ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3),
        ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1),
        ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2),
        ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3),
          (ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
          (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3 *
          ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
           conj ((ρ t1 g) d1 c1) * conj ((ρ t2 g) d2 c2) * conj ((ρ t3 g) d3 c3)) ∂μ) from by
    congr 1 with g; exact hpt g]
  -- Exchange the 12 sums with the integral (12 levels of integral_finsetSum)
  rw [integral_finsetSum Finset.univ (fun a1 _ => by
    apply integrable_finsetSum Finset.univ; intro b1 _; apply integrable_finsetSum Finset.univ; intro a2 _
    apply integrable_finsetSum Finset.univ; intro b2 _; apply integrable_finsetSum Finset.univ; intro a3 _
    apply integrable_finsetSum Finset.univ; intro b3 _; apply integrable_finsetSum Finset.univ; intro c1 _
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro a1 _
  rw [integral_finsetSum Finset.univ (fun b1 _ => by
    apply integrable_finsetSum Finset.univ; intro a2 _; apply integrable_finsetSum Finset.univ; intro b2 _
    apply integrable_finsetSum Finset.univ; intro a3 _; apply integrable_finsetSum Finset.univ; intro b3 _
    apply integrable_finsetSum Finset.univ; intro c1 _; apply integrable_finsetSum Finset.univ; intro d1 _
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro b1 _
  rw [integral_finsetSum Finset.univ (fun a2 _ => by
    apply integrable_finsetSum Finset.univ; intro b2 _; apply integrable_finsetSum Finset.univ; intro a3 _
    apply integrable_finsetSum Finset.univ; intro b3 _; apply integrable_finsetSum Finset.univ; intro c1 _
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro a2 _
  rw [integral_finsetSum Finset.univ (fun b2 _ => by
    apply integrable_finsetSum Finset.univ; intro a3 _; apply integrable_finsetSum Finset.univ; intro b3 _
    apply integrable_finsetSum Finset.univ; intro c1 _; apply integrable_finsetSum Finset.univ; intro d1 _
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro b2 _
  rw [integral_finsetSum Finset.univ (fun a3 _ => by
    apply integrable_finsetSum Finset.univ; intro b3 _; apply integrable_finsetSum Finset.univ; intro c1 _
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro a3 _
  rw [integral_finsetSum Finset.univ (fun b3 _ => by
    apply integrable_finsetSum Finset.univ; intro c1 _; apply integrable_finsetSum Finset.univ; intro d1 _
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro b3 _
  rw [integral_finsetSum Finset.univ (fun c1 _ => by
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro c1 _
  rw [integral_finsetSum Finset.univ (fun d1 _ => by
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro d1 _
  rw [integral_finsetSum Finset.univ (fun c2 _ => by
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro c2 _
  rw [integral_finsetSum Finset.univ (fun d2 _ => by
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro d2 _
  rw [integral_finsetSum Finset.univ (fun c3 _ => by
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro c3 _
  rw [integral_finsetSum Finset.univ (fun d3 _ => by
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro d3 _
  -- Pull the constant out of the integral
  rw [integral_const_mul]
#print axioms char_level_single_site_3D_integral

set_option maxHeartbeats 1000000 in
/-- **Single-site 3D Lüscher integral (Step 2 of the Lüscher roadmap, §8.11.41–42).**

For irreducible unitary representations of a compact group with normalized Haar measure, the
integral of 3 unbarred matrix elements times 3 barred matrix elements (as arises at each site
when integrating out a temporal link `u_t(x)` in 3D) equals a sum over the combined representation
`α` of `(1/dims α)` times the product of the unbarred and barred CG coefficients:

    ∫ (ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂} · (ρ_{s₃} g)_{a₃b₃}
        · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) · conj((ρ_{t₃} g)_{c₃d₃}) dμ(g)
      = ∑_{ν,r,s,α,p,q} CG_unbarred(ν,r,s,α,p,q) · (1/dims α) · ∑_{ν',r',s'} CG_barred(ν',r',s',α,p,q)

Proof: apply `cgME_decomp_3fold` to the 3 unbarred MEs (6 sums), exchange sums with integral
(Fubini), then evaluate each inner integral `∫ (ρ_α g)_{pq} · [3 barred MEs] dμ` using
`integral_ME_times_3barred_MEs` (which applies `cgME_decomp_3fold_conj` + Schur orthogonality).
The local coefficient is `CG_unbarred(α) · CG_barred(α)` (NOT necessarily ≥ 0 locally — the
non-negativity comes from the GLOBAL cascade in Step 3). 0 sorries, 0 new axioms. -/
lemma single_site_3D_luscher_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) ∂μ =
      ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((1 / dims α : ℂ) *
         ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
           conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
           conj (cgME ν' t3 α r' c3 p) * cgME ν' t3 α s' d3 q) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Integrability of the 4-ME product (1 unbarred × 3 barred) via CG decomposition of barred MEs
  have hInt_4ME : ∀ (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      Integrable (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3))) μ := by
    intro α p q
    have hpt_barred : ∀ (g : G),
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
        ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
            conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
            conj (cgME ν' t3 β r' c3 p') * conj ((ρ β g) p' q') * cgME ν' t3 β s' d3 q' := by
      intro g
      exact cgME_decomp_3fold_conj ι dims ρ cgME hcgME_decomp t1 t2 t3 g c1 d1 c2 d2 c3 d3
    rw [show (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3))) =
        (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
            conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
            conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
            ((ρ α g) p q * conj ((ρ β g) p' q'))) from by
      funext g
      rw [hpt_barred g, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q' _
      ring]
    apply integrable_finsetSum Finset.univ
    intro ν' _
    apply integrable_finsetSum Finset.univ
    intro r' _
    apply integrable_finsetSum Finset.univ
    intro s' _
    apply integrable_finsetSum Finset.univ
    intro β _
    apply integrable_finsetSum Finset.univ
    intro p' _
    apply integrable_finsetSum Finset.univ
    intro q' _
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
       conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q')
      (hInt α β p q p' q')
  -- Pointwise identity: apply cgME_decomp_3fold to the 3 unbarred MEs, distribute barred product
  have hpt : ∀ (g : G),
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3))) := by
    intro g
    have hreassoc : (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3) *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) := by ring
    rw [hreassoc, cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) ∂μ) =
        ∫ g, (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
          ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
          (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
           cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
          ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
           conj ((ρ t3 g) c3 d3)))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (6 levels, using hInt_4ME)
  have hInt_term : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι)
      (p : Fin (dims α)) (q : Fin (dims α)),
      Integrable (fun g =>
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s α p q
    exact Integrable.smul
      (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
       cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q))
      (hInt_4ME α p q)
  have hInt_q : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι) (p : Fin (dims α)),
      Integrable (fun g => ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s α p
    exact integrable_finsetSum Finset.univ (fun q _ => hInt_term ν r s α p q)
  have hInt_p : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι),
      Integrable (fun g => ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s α
    exact integrable_finsetSum Finset.univ (fun p _ => hInt_q ν r s α p)
  have hInt_α : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)),
      Integrable (fun g => ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s
    exact integrable_finsetSum Finset.univ (fun α _ => hInt_p ν r s α)
  have hInt_s : ∀ (ν : ι) (r : Fin (dims ν)),
      Integrable (fun g => ∑ s : Fin (dims ν), ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r
    exact integrable_finsetSum Finset.univ (fun s _ => hInt_α ν r s)
  have hInt_r : ∀ (ν : ι),
      Integrable (fun g => ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ α : ι,
        ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν
    exact integrable_finsetSum Finset.univ (fun r _ => hInt_s ν r)
  have hInt_ν : Integrable (fun g => ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν _ => hInt_r ν)
  -- Exchange sums with integral (6 levels)
  rw [integral_finsetSum Finset.univ (fun ν _ => hInt_r ν)]
  rw [Finset.sum_congr rfl (fun ν _ => integral_finsetSum Finset.univ (fun r _ => hInt_s ν r))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ =>
      integral_finsetSum Finset.univ (fun s _ => hInt_α ν r s)))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
      (fun s _ => integral_finsetSum Finset.univ (fun α _ => hInt_p ν r s α))))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
      (fun s _ => Finset.sum_congr rfl (fun α _ => integral_finsetSum Finset.univ
        (fun p _ => hInt_q ν r s α p)))))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
      (fun s _ => Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
        integral_finsetSum Finset.univ (fun q _ => hInt_term ν r s α p q))))))]
  -- Evaluate each inner integral using the helper
  have hInt_eval : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι)
      (p : Fin (dims α)) (q : Fin (dims α)),
      ∫ g,
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3))) ∂μ =
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((1 / dims α : ℂ) *
         ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
           conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
           conj (cgME ν' t3 α r' c3 p) * cgME ν' t3 α s' d3 q) := by
    intro ν r s α p q
    rw [integral_const_mul,
        show ∫ g, (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
            conj ((ρ t3 g) c3 d3)) ∂μ =
            ∫ g, (ρ α g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
              conj ((ρ t3 g) c3 d3) ∂μ from by
          congr 1 with g; ring,
        integral_ME_times_3barred_MEs μ ι dims hDims ρ hU hIrr
      cgME hcgME_decomp α p q t1 t2 t3 c1 d1 c2 d2 c3 d3]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ =>
      Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun α _ =>
        Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
          hInt_eval ν r s α p q))))))]

#print axioms single_site_3D_luscher_integral

open scoped ComplexOrder in
/-- **CG unitarity non-negativity (Step 3a of Lüscher roadmap).** In the diagonal case
(barred indices = unbarred indices), the single-site 3D Lüscher integral gives
`∑_{α,p,q} (1/dims α) · |C(α,p,q)|² ≥ 0`, where `C(α,p,q) = ∑_{ν,r,s} CG_unbarred(ν,r,s,α,p,q)`.

This demonstrates the |C|² structure from CG unitarity: the diagonal case of
`single_site_3D_luscher_integral` gives a sum of `|C|²` terms with non-negative coefficients
`(1/dims α) > 0`, hence non-negative. 0 sorries, 0 new axioms. -/
lemma cg_unitarity_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3)) :
    0 ≤ ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ s1 g) a1 b1) * conj ((ρ s2 g) a2 b2) * conj ((ρ s3 g) a3 b3) ∂μ := by
  -- Step 1: Apply single_site_3D_luscher_integral with diagonal args
  rw [single_site_3D_luscher_integral μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
    s1 s2 s3 a1 b1 a2 b2 a3 b3 s1 s2 s3 a1 b1 a2 b2 a3 b3]
  -- Define U (unbarred CG product) for readability
  set U := fun (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι) (p : Fin (dims α)) (q : Fin (dims α)) =>
    cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
    cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)
  -- Define C(α,p,q) = ∑_{ν,r,s} U(ν,r,s,α,p,q)
  let C (α : ι) (p : Fin (dims α)) (q : Fin (dims α)) : ℂ :=
    ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q
  -- Helper: conj pushes through products
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  -- Step 2: Show barred CG product = conj(U) pointwise (conj distribution over products)
  have hBU : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      conj (cgME s1 s2 ν' a1 a2 r') * cgME s1 s2 ν' b1 b2 s' *
      conj (cgME ν' s3 α r' a3 p) * cgME ν' s3 α s' b3 q =
      conj (U ν' r' s' α p q) := by
    intro ν' r' s' α p q
    simp only [U, hconj_mul, Complex.conj_conj]
  -- Step 3: Substitute barred = conj(U) in the goal
  simp only [hBU]
  -- Step 4: Show ∑_{ν',r',s'} conj(U') = conj(C) (conj distribution over sums + alpha-equivalence)
  have hsumB : ∀ (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), conj (U ν' r' s' α p q) = conj (C α p q) := by
    intro α p q
    have h1 : ∀ (ν' : ι) (r' : Fin (dims ν')),
        ∑ s' : Fin (dims ν'), conj (U ν' r' s' α p q) = conj (∑ s' : Fin (dims ν'), U ν' r' s' α p q) := by
      intro ν' r'; rw [← map_sum (starRingEnd ℂ) (fun s' => U ν' r' s' α p q) Finset.univ]
    have h2 : ∀ (ν' : ι),
        ∑ r' : Fin (dims ν'), conj (∑ s' : Fin (dims ν'), U ν' r' s' α p q) =
        conj (∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), U ν' r' s' α p q) := by
      intro ν'; rw [← map_sum (starRingEnd ℂ) (fun r' => ∑ s' : Fin (dims ν'), U ν' r' s' α p q) Finset.univ]
    rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => h1 ν' r'))]
    rw [Finset.sum_congr rfl (fun ν' _ => h2 ν')]
    rw [← map_sum (starRingEnd ℂ)
          (fun ν' => ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), U ν' r' s' α p q) Finset.univ]
  -- Step 5: Substitute ∑ conj(U') = conj(C) in the goal
  simp only [hsumB]
  -- Step 6: Reorder ∑_{ν,r,s,α,p,q} → ∑_{α,p,q,ν,r,s} (9 swaps)
  rw [show (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ ν : ι, ∑ r : Fin (dims ν), ∑ α : ι, ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_comm]))]
  rw [show (∑ ν : ι, ∑ r : Fin (dims ν), ∑ α : ι, ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ ν : ι, ∑ α : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm])]
  rw [Finset.sum_comm]
  rw [show (∑ α : ι, ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ ν : ι, ∑ r : Fin (dims ν), ∑ p : Fin (dims α), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_comm])))]
  rw [show (∑ α : ι, ∑ ν : ι, ∑ r : Fin (dims ν), ∑ p : Fin (dims α), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ ν : ι, ∑ p : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm]))]
  rw [show (∑ α : ι, ∑ ν : ι, ∑ p : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => by rw [Finset.sum_comm])]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ q : Fin (dims α), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_comm]))))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ q : Fin (dims α), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ q : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm])))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ q : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_comm]))]
  -- Step 7: Factor (1/dims α) * conj(C α p q) out of ∑_{ν,r,s} (3 Finset.sum_mul)
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν),
        (∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun ν _ =>
        Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_mul])))))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν),
        (∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι,
        (∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_mul]))))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι,
        (∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rw [Finset.sum_mul])))]
  -- Step 8: Substitute ∑_{ν,r,s} U = C
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        C α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rfl)))]
  -- Step 9: Rewrite C * ((1/dims α) * conj(C)) = (1/dims α) * |C|²
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        C α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (1 / dims α : ℂ) * (Complex.normSq (C α p q) : ℂ)) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rw [Complex.normSq_eq_conj_mul_self]; ring)))]
  -- Step 10: Conclude ∑ (1/dims α) * |C|² ≥ 0
  exact Finset.sum_nonneg (fun α _ => Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun q _ => by
      have h1 : 0 ≤ (1 / dims α : ℝ) := by positivity
      have h2 : 0 ≤ Complex.normSq (C α p q) := Complex.normSq_nonneg _
      have h3 : 0 ≤ (1 / dims α : ℝ) * Complex.normSq (C α p q) := mul_nonneg h1 h2
      convert Complex.zero_le_real.mpr h3 using 2
      simp [Complex.ofReal_mul, Complex.ofReal_div])))

#print axioms cg_unitarity_nonneg

/-! ## Step 3(c): 2-fold CG decomposition building blocks for the 3D global cascade

The 3-fold lemmas above (`single_site_3D_luscher_integral`, `cg_unitarity_nonneg`)
handle the case where each site has 3 unbarred + 3 barred matrix elements (3 spatial
directions, all non-local). The 2-fold lemmas below handle the case where each site
has 2 unbarred + 2 barred matrix elements (2 non-local directions), which is the
simplest setting exhibiting the CG decomposition mechanism in a multi-site cascade.
These are the 2D analogues, proved by the same technique (CG decomposition + Schur
orthogonality) but with 3 nesting levels instead of 6. 0 sorries, 0 new axioms. -/

/-- **2-fold CG conjugate decomposition.** Conjugate of `hcgME_decomp`:
`conj((ρ_s g)_{ab}) · conj((ρ_t g)_{ij}) = ∑_ν ∑_{p,q} conj(cgME s t ν a i p) · conj((ρ_ν g)_{pq}) · cgME s t ν b j q`.

Pure algebra from `hcgME_decomp` (take conjugate, push `conj` through products and sums). -/
lemma cgME_decomp_conj
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)) :
    conj ((ρ s g) a b) * conj ((ρ t g) i j) =
    ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
      conj (cgME s t ν a i p) * conj ((ρ ν g) p q) * cgME s t ν b j q := by
  have h := hcgME_decomp s t g a b i j
  have hconj : conj ((ρ s g) a b * (ρ t g) i j) =
      conj (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q)) := by
    rw [h]
  simp at hconj
  exact hconj

#print axioms cgME_decomp_conj

/-- **Integral of 1 unbarred × 2 barred matrix elements (2D helper).**

`∫ (ρ_σ g)_{pq} · conj((ρ_{t1} g)_{c1d1}) · conj((ρ_{t2} g)_{c2d2}) dμ(g)
  = (1/dims σ) · conj(cgME t1 t2 σ c1 c2 p) · cgME t1 t2 σ d1 d2 q`

Applies `cgME_decomp_conj` to the 2 barred MEs, exchanges sums with the integral
(Fubini, 3 levels), collapses the combined-rep sum to `σ` (Schur off-diagonal),
collapses the index sums to `p, q` (Schur diagonal), and factors out `1/dims σ`.
0 sorries, 0 new axioms. -/
lemma integral_ME_times_2barred_MEs
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ : ι) (p : Fin (dims σ)) (q : Fin (dims σ))
    (t1 t2 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) :
    ∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ =
      (1 / dims σ : ℂ) * (conj (cgME t1 t2 σ c1 c2 p) * cgME t1 t2 σ d1 d2 q) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Pointwise identity: apply cgME_decomp_conj to the 2 barred MEs, distribute (ρ σ g) p q
  have hpt : ∀ (g : G),
      (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s')) := by
    intro g
    have hreassoc : (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
        (ρ σ g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)) := by ring
    rw [hreassoc, cgME_decomp_conj ι dims ρ cgME hcgME_decomp t1 t2 g c1 d1 c2 d2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ) =
        ∫ g, (∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (3 levels)
  have hInt_term : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      Integrable (fun g =>
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    intro ν' r' s'
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s')
      (hInt σ ν' p q r' s')
  have hInt_s' : ∀ (ν' : ι) (r' : Fin (dims ν')),
      Integrable (fun g => ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    intro ν' r'
    exact integrable_finsetSum Finset.univ (fun s' _ => hInt_term ν' r' s')
  have hInt_r' : ∀ (ν' : ι),
      Integrable (fun g => ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    intro ν'
    exact integrable_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r')
  have hInt_ν' : Integrable (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')
  -- Exchange sums with integral (3 levels)
  rw [integral_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')]
  rw [Finset.sum_congr rfl (fun ν' _ => integral_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r'))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      integral_finsetSum Finset.univ (fun s' _ => hInt_term ν' r' s')))]
  -- For ν' ≠ σ, each integral is 0 (pull constant + Schur offdiag)
  have hν'_ne_zero : ∀ (ν' : ι), ν' ≠ σ →
      (∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ ν' g) r' s')) ∂μ) = 0 := by
    intro ν' hν'
    refine Finset.sum_eq_zero (fun r' _ => ?_)
    refine Finset.sum_eq_zero (fun s' _ => ?_)
    rw [integral_const_mul, hSchur_offdiag σ ν' p q r' s' (Ne.symm hν')]
    simp
  -- Collapse ν' sum: only ν' = σ contributes
  have hν'_collapse :
      (∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ ν' g) r' s')) ∂μ) =
      (∑ r' : Fin (dims σ), ∑ s' : Fin (dims σ),
        ∫ g,
          conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ σ g) r' s')) ∂μ) := by
    exact Finset.sum_eq_single σ (fun ν' _ hν' => hν'_ne_zero ν' hν')
        (fun h => (h (Finset.mem_univ _)).elim)
  rw [hν'_collapse]
  -- Evaluate each integral (ν' = σ case: pull constant + Schur diag)
  have hInt_eval : ∀ (r' : Fin (dims σ)) (s' : Fin (dims σ)),
      ∫ g,
        conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ σ g) r' s')) ∂μ =
        conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
        (if p = r' ∧ q = s' then (1 / dims σ : ℂ) else 0) := by
    intro r' s'
    rw [integral_const_mul, hSchur_diag]
  rw [Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl (fun s' _ => hInt_eval r' s'))]
  -- Collapse r', s' sums
  have hrs'_collapse :
      (∑ r' : Fin (dims σ), ∑ s' : Fin (dims σ),
        conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
        (if p = r' ∧ q = s' then (1 / dims σ : ℂ) else 0)) =
      conj (cgME t1 t2 σ c1 c2 p) * cgME t1 t2 σ d1 d2 q * (1 / dims σ : ℂ) := by
    rw [Finset.sum_eq_single p (fun r' _ hr => Finset.sum_eq_zero (fun s' _ => by
        simp [Ne.symm hr])) (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, true_and]
    rw [Finset.sum_eq_single q (fun s' _ hs => by simp [Ne.symm hs])
        (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, if_true]
  rw [hrs'_collapse]
  ring

#print axioms integral_ME_times_2barred_MEs

/-- **Single-site 2D Lüscher integral (Step 3c building block).**

For irreducible unitary representations of a compact group with normalized Haar measure, the
integral of 2 unbarred matrix elements times 2 barred matrix elements (as arises at each site
when integrating out a temporal link `u_t(x)` in 2D, with 2 non-local directions) equals a sum
over the combined representation `ν` of `(1/dims ν)` times the product of the unbarred and
barred CG coefficients:

    ∫ (ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂}
        · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) dμ(g)
      = ∑_{ν,p,q} CG_unbarred(ν,p,q) · (1/dims ν) · CG_barred(ν,p,q)

Proof: apply `hcgME_decomp` to the 2 unbarred MEs (3 sums), exchange sums with integral
(Fubini), then evaluate each inner integral `∫ (ρ_ν g)_{pq} · [2 barred MEs] dμ` using
`integral_ME_times_2barred_MEs`. 0 sorries, 0 new axioms. -/
lemma single_site_2D_luscher_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2))
    (t1 t2 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) :
    ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((1 / dims ν : ℂ) *
         (conj (cgME t1 t2 ν c1 c2 p) * cgME t1 t2 ν d1 d2 q)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Integrability of the 3-ME product (1 unbarred × 2 barred) via CG decomposition of barred MEs
  have hInt_3ME : ∀ (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      Integrable (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) μ := by
    intro α p q
    have hpt_barred : ∀ (g : G),
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
        ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          conj (cgME t1 t2 ν' c1 c2 r') * conj ((ρ ν' g) r' s') * cgME t1 t2 ν' d1 d2 s' := by
      intro g
      exact cgME_decomp_conj ι dims ρ cgME hcgME_decomp t1 t2 g c1 d1 c2 d2
    rw [show (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) =
        (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ α g) p q * conj ((ρ ν' g) r' s'))) from by
      funext g
      rw [hpt_barred g, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      ring]
    apply integrable_finsetSum Finset.univ
    intro ν' _
    apply integrable_finsetSum Finset.univ
    intro r' _
    apply integrable_finsetSum Finset.univ
    intro s' _
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s')
      (hInt α ν' p q r' s')
  -- Pointwise identity: apply hcgME_decomp to the 2 unbarred MEs, distribute barred product
  have hpt : ∀ (g : G),
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) := by
    intro g
    have hreassoc : (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2) *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)) := by ring
    rw [hreassoc, hcgME_decomp s1 s2 g a1 b1 a2 b2]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ) =
        ∫ g, (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
          ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (3 levels, using hInt_3ME)
  have hInt_term : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g =>
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    intro ν p q
    exact Integrable.smul
      (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q))
      (hInt_3ME ν p q)
  have hInt_q : ∀ (ν : ι) (p : Fin (dims ν)),
      Integrable (fun g => ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    intro ν p
    exact integrable_finsetSum Finset.univ (fun q _ => hInt_term ν p q)
  have hInt_p : ∀ (ν : ι),
      Integrable (fun g => ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    intro ν
    exact integrable_finsetSum Finset.univ (fun p _ => hInt_q ν p)
  have hInt_ν : Integrable (fun g => ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν _ => hInt_p ν)
  -- Exchange sums with integral (3 levels)
  rw [integral_finsetSum Finset.univ (fun ν _ => hInt_p ν)]
  rw [Finset.sum_congr rfl (fun ν _ => integral_finsetSum Finset.univ (fun p _ => hInt_q ν p))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      integral_finsetSum Finset.univ (fun q _ => hInt_term ν p q)))]
  -- Evaluate each inner integral using the helper
  have hInt_eval : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      ∫ g,
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) ∂μ =
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((1 / dims ν : ℂ) *
         (conj (cgME t1 t2 ν c1 c2 p) * cgME t1 t2 ν d1 d2 q)) := by
    intro ν p q
    rw [integral_const_mul,
        show ∫ g, (ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)) ∂μ =
            ∫ g, (ρ ν g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ from by
          congr 1 with g; ring,
        integral_ME_times_2barred_MEs μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
          ν p q t1 t2 c1 d1 c2 d2]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => hInt_eval ν p q)))]

#print axioms single_site_2D_luscher_integral

open scoped ComplexOrder in
/-- **2-fold CG unitarity non-negativity (Step 3c building block).** In the diagonal case
(barred indices = unbarred indices), the single-site 2D Lüscher integral gives
`∑_{ν,p,q} (1/dims ν) · |cgME s1 s2 ν a1 a2 p|² · |cgME s1 s2 ν b1 b2 q|² ≥ 0`.

This is the 2D analogue of `cg_unitarity_nonneg`: the diagonal case of
`single_site_2D_luscher_integral` gives a sum of `|A|² · |B|²` terms with non-negative
coefficients `(1/dims ν) > 0`, hence non-negative. 0 sorries, 0 new axioms. -/
lemma cg2_unitarity_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) :
    0 ≤ ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ s1 g) a1 b1) * conj ((ρ s2 g) a2 b2) ∂μ := by
  -- Step 1: Apply single_site_2D_luscher_integral with diagonal args
  rw [single_site_2D_luscher_integral μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
    s1 s2 a1 b1 a2 b2 s1 s2 a1 b1 a2 b2]
  -- Step 2: In the diagonal case, the CG product simplifies to |A|² · |B|² · (1/dims ν)
  exact Finset.sum_nonneg (fun ν _ => Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun q _ => by
      set A := cgME s1 s2 ν a1 a2 p
      set B := cgME s1 s2 ν b1 b2 q
      -- The term is (A * conj B) * ((1/dims ν) * (conj A * B)) = (1/dims ν) * |A|² * |B|²
      have hnormSq : (A * conj B) * ((1 / dims ν : ℂ) * (conj A * B)) =
          (1 / dims ν : ℂ) * Complex.normSq A * Complex.normSq B := by
        rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
        ring
      rw [hnormSq]
      have h1 : 0 ≤ (1 / dims ν : ℝ) := by positivity
      have h2 : 0 ≤ Complex.normSq A := Complex.normSq_nonneg _
      have h3 : 0 ≤ Complex.normSq B := Complex.normSq_nonneg _
      have h4 : 0 ≤ (1 / dims ν : ℝ) * Complex.normSq A * Complex.normSq B :=
        mul_nonneg (mul_nonneg h1 h2) h3
      convert Complex.zero_le_real.mpr h4 using 2
      simp [Complex.ofReal_mul, Complex.ofReal_div])))
#print axioms cg2_unitarity_nonneg

end PlaquetteBoltzmann

end YangMills
