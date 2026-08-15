/-
# Positive Definite: Character Orthogonality
-/

import YangMills.Proofs.PositiveDefinite.RepCharacter

open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills
variable {G : Type*} [Group G] {n : Nat}

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

