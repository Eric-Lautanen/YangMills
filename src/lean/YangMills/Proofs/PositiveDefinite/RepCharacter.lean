/-
# Positive Definite: Unitary Representations
-/

import YangMills.Proofs.PositiveDefinite.BuildingBlocks

open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills
section UnitaryRepresentation

variable {G : Type*} [Group G] {n : ℕ}

/-- A unitary representation of `G` is a group homomorphism into unitary matrices. -/
def IsUnitaryRepresentation (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ

/-- The character of a representation is the trace of the representation matrix. -/
def repCharacter (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g : G) : ℂ :=
  Matrix.trace (ρ g)

/-- For a unitary matrix `A`, the conjugate transpose equals the inverse. -/
lemma conjTranspose_eq_inv_of_unitary
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Aᴴ = A⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  exact (Matrix.inv_eq_left_inv h).symm

/-- The character of a unitary representation is positive-definite.

This generalizes `fundamentalCharacter_positiveDefinite` from the fundamental
representation of `SU(N)` to arbitrary unitary representations of any group.

The proof: for `B = ∑ conj(c_g) • ρ(g)`, the PD sum equals `Tr(Bᴴ * B) ≥ 0`,
using that `ρ(g)ᴴ = ρ(g⁻¹)` (unitary + homomorphism). -/
lemma repCharacter_positiveDefinite
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) :
    PositiveDefinite (repCharacter ρ) := by
  intro s c
  -- Tr(Mᴴ * M) ≥ 0 for any matrix M
  have h_nonneg_sq : ∀ (M : Matrix (Fin n) (Fin n) ℂ), 0 ≤ Matrix.trace (Mᴴ * M) := by
    intro M
    have htrace : Matrix.trace (Mᴴ * M) = (∑ i : Fin n, (Mᴴ * M) i i : ℂ) := by
      simp [Matrix.trace]
    rw [htrace]
    refine Finset.sum_nonneg (λ i _ => ?_)
    have hdiag : (Mᴴ * M) i i = ∑ k : Fin n, conj (M k i) * M k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hdiag]
    refine Finset.sum_nonneg (λ k _ => ?_)
    have hnn : 0 ≤ conj (M k i) * M k i := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have hval : 0 ≤ Complex.normSq (M k i) := Complex.normSq_nonneg _
      rw [Complex.nonneg_iff]
      exact ⟨by simpa using hval, by simp⟩
    exact hnn
  -- Key: ρ(g)ᴴ = ρ(g⁻¹) for unitary representations
  have h_star_eq (g : G) : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  -- B = ∑ conj(c_g) • ρ(g)
  set B : Matrix (Fin n) (Fin n) ℂ := ∑ g ∈ s, (conj (c g) : ℂ) • (ρ g)
  -- Bᴴ = ∑ c_g • ρ(g⁻¹)
  have hB_star : Bᴴ = ∑ g ∈ s, (c g : ℂ) • (ρ g⁻¹) := by
    show (∑ g ∈ s, (conj (c g) : ℂ) • (ρ g))ᴴ = _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Matrix.conjTranspose_smul, h_star_eq g]
    simp [Complex.conj_conj]
  -- Key identity: Tr(Bᴴ * B) = ∑ c_i conj(c_j) * χ(i⁻¹ * j)
  have hBstarB : Bᴴ * B = ∑ i ∈ s, ∑ j ∈ s,
      ((c i : ℂ) * (conj (c j) : ℂ)) • (ρ (i⁻¹ * j)) := by
    rw [hB_star]
    show (∑ g ∈ s, (c g : ℂ) • (ρ g⁻¹)) * (∑ g ∈ s, (conj (c g) : ℂ) • (ρ g)) = _
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← ρ.map_mul]
  have h_tr_eq : Matrix.trace (Bᴴ * B) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * repCharacter ρ (i⁻¹ * j)) := by
    rw [hBstarB]
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [repCharacter]
  have h_trace_nonneg : 0 ≤ Matrix.trace (Bᴴ * B) := h_nonneg_sq B
  rw [← h_tr_eq]
  exact h_trace_nonneg

/-- For a unitary representation, the character satisfies `χ(g⁻¹) = conj(χ(g))`.
This follows from `ρ(g⁻¹) = ρ(g)⁻¹ = ρ(g)ᴴ` (unitary) and
`Tr(Mᴴ) = conj(Tr(M))`. -/
lemma repCharacter_inv (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G) :
    repCharacter ρ g⁻¹ = conj (repCharacter ρ g) := by
  have h_star_eq : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  rw [repCharacter, repCharacter, ← h_star_eq]
  simp [Matrix.trace, Matrix.conjTranspose_apply, Complex.star_def]

/-- The character is invariant under cyclic permutations of its argument:
`χ(g * h * k) = χ(h * k * g)`.

This is the *class-function* (conjugation-invariance) property of characters,
expressed via the cyclic invariance of the trace: `Tr(ABC) = Tr(BCA)`.
It follows from `Matrix.trace_mul_comm` applied twice.  No unitary hypothesis
is needed — this is pure trace algebra. -/
lemma repCharacter_cyclic (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g h k : G) :
    repCharacter ρ (g * h * k) = repCharacter ρ (h * k * g) := by
  simp only [repCharacter, MonoidHom.map_mul]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc]

/-- **Characters are invariant under 2-factor cyclic permutation**: `χ(g · h) = χ(h · g)`.

This follows from `Tr(A · B) = Tr(B · A)` (cyclicity of the trace). No unitary
hypothesis is needed — this is pure trace algebra. This is the key lemma for
rearranging character arguments in the bipartite Lüscher cascade. -/
lemma repCharacter_cyclic2 (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g h : G) :
    repCharacter ρ (g * h) = repCharacter ρ (h * g) := by
  simp only [repCharacter, MonoidHom.map_mul]
  rw [Matrix.trace_mul_comm]

/-- **Characters are class functions** (conjugation-invariant): `χ(g · h · g⁻¹) = χ(h)`.

This follows from `repCharacter_cyclic` (cyclic invariance of the trace) plus the
group inverse property `g⁻¹ · g = 1`. No unitary hypothesis is needed — this is
pure trace algebra.

This is the key property for the 3D Lüscher cascade (Step 3c of the roadmap):
a "local" plaquette at site `x` in direction `ν` has plaquette variable
`u_t(x) · W_ν(x) · u_t(x)⁻¹`, and since `B_p` is a sum of characters (each a
class function), `B_p(u · W · u⁻¹) = B_p(W)` — the local plaquette contributes a
CONSTANT (independent of `u_t(x)`), which factors out of the temporal-link
integral. Only NON-LOCAL plaquettes (connecting different sites) contribute to
the cascade. 0 sorries, 0 new axioms. -/
lemma repCharacter_isClassFunction (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g h : G) :
    repCharacter ρ (g * h * g⁻¹) = repCharacter ρ h := by
  rw [repCharacter_cyclic, mul_assoc, inv_mul_cancel, mul_one]

/-- For a unitary representation, the character is bounded by the dimension:
`‖χ(g)‖ ≤ n` where `n = dim(ρ)`.

This follows from `|Tr(A)| ≤ ∑ |A_jj| ≤ ∑ 1 = n` for a unitary `n×n` matrix `A`,
using `entry_norm_bound_of_unitary` (each entry of a unitary matrix has norm ≤ 1).
This bound is a key ingredient for proving integrability of the character-expansion
terms w.r.t. the finite Haar measure (needed for the Fubini exchange in step 4c). -/
lemma repCharacter_norm_le_dim (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G) :
    ‖repCharacter ρ g‖ ≤ n := by
  have hU : ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ := h_unitary g
  have h_entry : ∀ j : Fin n, ‖(ρ g) j j‖ ≤ 1 := fun j =>
    entry_norm_bound_of_unitary hU j j
  rw [repCharacter]
  simp only [Matrix.trace]
  calc ‖∑ j : Fin n, (ρ g) j j‖
      ≤ ∑ j : Fin n, ‖(ρ g) j j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => h_entry j
    _ = n := by simp

#print axioms repCharacter_norm_le_dim

/-- For a unitary representation, the matrix element at `g⁻¹` equals the
conjugate of the transposed matrix element at `g`:

    (ρ g⁻¹)_{ij} = conj((ρ g)_{ji})

This follows from `ρ(g⁻¹) = ρ(g)ᴴ` (unitary + homomorphism) and the definition
of conjugate transpose `(Mᴴ)_{ij} = conj(M_{ji})`.

This is the key relation connecting the σ reflection (inversion of time-like
interface links) to the matrix-element basis. In the L² expansion approach to
closing `transferMatrixPositivity_axiom`, the σ reflection on a time-like
interface link `g ↦ g⁻¹` transforms matrix elements as
`(ρ(σ(g)))_{ij} = conj((ρ g)_{ji})`, which is essential for evaluating the
reflection-positivity integral using Schur orthogonality. -/
lemma repMatrixElement_inv (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G)
    (i j : Fin n) :
    (ρ g⁻¹) i j = conj ((ρ g) j i) := by
  have h_star_eq : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  rw [← h_star_eq]
  simp [Matrix.conjTranspose_apply]

#print axioms repMatrixElement_inv

