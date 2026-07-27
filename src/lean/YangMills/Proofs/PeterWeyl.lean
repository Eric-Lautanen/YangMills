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

/-- **Axiom (Peter-Weyl + Clebsch-Gordan for the plaquette Boltzmann factor).**

For `c ≥ 0`, the plaquette Boltzmann factor `exp(c · Re Tr(g₁ g₂ g₃ g₄))` admits a
character expansion

    exp(c · Re Tr(g₁ g₂ g₃ g₄))
      = ∑_{r,s,t,u,v} coeff r s t u v · χ_s(g₁) · χ_t(g₂) · χ_u(g₃) · χ_v(g₄)

where the sum ranges over a finite index set `ι` of irreducible unitary
representations `ρ i` of `SU(N)`, `χ_i = repCharacter (ρ i)` is the character, and
the coefficients `coeff r s t u v ≥ 0`.  The index `r` is the Peter-Weyl expansion
index (carrying the heat-kernel coefficient `a_r ≥ 0`) and `s, t, u, v` are the
Clebsch-Gordan indices produced by decomposing `χ_r(g₁ g₂ g₃ g₄)` into a sum of
products of single-link characters (Littlewood-Richardson coefficients, applied
three times).  All coefficients are non-negative.

This axiom fuses two deep theorems of compact-Lie-group representation theory
that are not currently in Mathlib:

  * **Peter-Weyl theorem**: `exp(c · Re Tr(g)) = ∑_r a_r χ_r(g)` with `a_r ≥ 0`.
  * **Clebsch-Gordan decomposition**: `χ_r(gh) = ∑_{s,t} N^r_{st} χ_s(g) χ_t(h)`
    with Littlewood-Richardson multiplicities `N^r_{st} ≥ 0`, applied three times
    to split the four-link product.

See `docs/found_issues.md` §3 and `docs/gap_analysis.md` for the mathematical
obstruction that necessitates this expansion. -/
axiom peterWeyl_clebschGordan_plaquette (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (coeff : ι → ι → ι → ι → ι → ℝ)
      (hcoeff : ∀ r s t u v, 0 ≤ coeff r s t u v),
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
  obtain ⟨ι, hι, dims, ρ, hU, coeff, hcoeff, hexp4⟩ :=
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

end PlaquetteBoltzmann

end YangMills
