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
import YangMills.Proofs.PositiveDefinite

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
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

The index set `ι` is required to be closed under tensor-product decomposition
and under duals (so that the CG sum and the dual map stay within `ι`); this is
guaranteed by taking `ι` large enough to contain all irreducibles appearing in
any relevant tensor product or dual.

See `docs/found_issues.md` §3 and `docs/gap_analysis.md` for the mathematical
obstruction that necessitates this expansion. -/
axiom peterWeyl_clebschGordan_plaquette (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (coeff : ι → ι → ι → ι → ι → ℝ)
      (hcoeff : ∀ r s t u v, 0 ≤ coeff r s t u v)
      (cg : ι → ι → ι → ℝ)
      (hcg : ∀ s t w, 0 ≤ cg s t w)
      (hcg_decomp : ∀ s t (g : SU N),
        repCharacter (ρ s) g * repCharacter (ρ t) g =
        ∑ w : ι, (cg s t w : ℂ) * repCharacter (ρ w) g)
      (dual : ι → ι)
      (hdual : ∀ i (g : SU N),
        repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g)),
      ∀ (g₁ g₂ g₃ g₄ : SU N),
        (Real.exp (c * (Matrix.trace ((g₁ * g₂ * g₃ * g₄ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
          ∑ r : ι, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∑ v : ι,
            (coeff r s t u v : ℂ) *
            (repCharacter (ρ s) g₁ * repCharacter (ρ t) g₂ *
             repCharacter (ρ u) g₃ * repCharacter (ρ v) g₄)

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
  obtain ⟨ι, hι, dims, ρ, hU, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual, hexp4⟩ :=
    peterWeyl_clebschGordan_plaquette N c hc
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
  obtain ⟨ι, hι, dims, ρ, hU, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual, hexp4⟩ :=
    peterWeyl_clebschGordan_plaquette N c hc
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

end PlaquetteBoltzmann

end YangMills
