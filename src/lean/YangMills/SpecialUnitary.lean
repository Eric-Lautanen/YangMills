/-
# SU(N) Compact Lie Group

Formalization of SU(N), the special unitary group, and its Lie algebra su(N)
as the foundation for Yang-Mills gauge theory.

We use Mathlib's existing matrix group implementations:
- `Matrix.specialUnitaryGroup n ℂ` for SU(N)
- `Matrix.unitaryGroup n ℂ` for U(N)
- The Lie algebra su(N) is modelled as skew-Hermitian traceless matrices

Reference: Mathlib/LinearAlgebra/UnitaryGroup.lean
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic

open Matrix
open scoped Matrix
open Set
open Metric
open Finset
open MeasureTheory

namespace YangMills

/--
The special unitary group SU(N) as unitary `N×N` complex matrices with determinant 1.
Implemented as `Matrix.specialUnitaryGroup (Fin N) ℂ`.
-/
abbrev SU (N : ℕ) : Type :=
  Matrix.specialUnitaryGroup (Fin N) ℂ

-- ---------------------------------------------------------------
-- Topological group structure
-- ---------------------------------------------------------------

lemma star_mem_specialUnitaryGroup (N : ℕ) : ∀ {x : Matrix (Fin N) (Fin N) ℂ},
    x ∈ Matrix.specialUnitaryGroup (Fin N) ℂ → star x ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  intro x hx
  let x' : Matrix.specialUnitaryGroup (Fin N) ℂ := ⟨x, hx⟩
  have hstar_prop : (star x').1 ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := (star x').property
  simpa [Matrix.specialUnitaryGroup.coe_star] using hstar_prop

instance (N : ℕ) : ContinuousMul (SU N) :=
  inferInstance

instance (N : ℕ) : ContinuousStar (SU N) := by
  have hstar_cont : Continuous (star : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
    ContinuousStar.continuous_star
  have hstar_preserves : ∀ (x : Matrix (Fin N) (Fin N) ℂ),
      x ∈ Matrix.specialUnitaryGroup (Fin N) ℂ → star x ∈ Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun x hx => star_mem_specialUnitaryGroup N hx
  have h_cont_map : Continuous (Subtype.map (star : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ)
      hstar_preserves) :=
    hstar_cont.subtype_map hstar_preserves
  have h_eq : (star : SU N → SU N) = 
      (Subtype.map (star : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) hstar_preserves) := by
    ext x : 1
    apply Subtype.ext
    rfl
  have h_cont_star : Continuous (star : SU N → SU N) := by
    rw [h_eq]
    exact h_cont_map
  exact ⟨h_cont_star⟩

instance (N : ℕ) : ContinuousInv (SU N) := by
  have h_cont_star : Continuous (star : SU N → SU N) :=
    ContinuousStar.continuous_star
  have h_inv_eq_star : (fun (x : SU N) => x⁻¹) = (star : SU N → SU N) := by
    ext x : 1
    apply Subtype.ext
    exact congrArg Subtype.val (Matrix.star_eq_inv x).symm
  refine ⟨?continuous_inv⟩
  rw [h_inv_eq_star]
  exact h_cont_star

instance (N : ℕ) : IsTopologicalGroup (SU N) where

-- ---------------------------------------------------------------
-- Borel structure (needed for Haar measure)
-- ---------------------------------------------------------------

noncomputable instance (N : ℕ) : MeasurableSpace (SU N) :=
  borel _

instance (N : ℕ) : BorelSpace (SU N) where
  measurable_eq := rfl

-- ---------------------------------------------------------------
-- Compactness of SU(N)
-- ---------------------------------------------------------------

lemma entry_norm_le_one (N : ℕ) (A : SU N) (i j : Fin N) : ‖A.1 i j‖ ≤ 1 := by
  rcases A.property with ⟨⟨huni1, huni2⟩, hdet⟩
  have h_diag : (star A.1 * A.1) j j = 1 := by
    rw [huni1]
    simp
  have h_sum_complex : (∑ k : Fin N, Complex.normSq (A.1 k j) : ℂ) = 1 := by
    calc
      (∑ k : Fin N, Complex.normSq (A.1 k j) : ℂ) = ∑ k : Fin N, ((starRingEnd ℂ) (A.1 k j) * A.1 k j) := by
        simp [Complex.normSq_eq_conj_mul_self]
      _ = (star A.1 * A.1) j j := by
        simp [Matrix.mul_apply, Matrix.star_apply]
      _ = 1 := h_diag
  have h_sum_real : ∑ k : Fin N, Complex.normSq (A.1 k j) = 1 := by
    exact_mod_cast h_sum_complex
  have h_nonneg : ∀ k : Fin N, 0 ≤ Complex.normSq (A.1 k j) :=
    λ k => Complex.normSq_nonneg _
  have h_bound_sq : Complex.normSq (A.1 i j) ≤ 1 := by
    have : Complex.normSq (A.1 i j) ≤ ∑ k : Fin N, Complex.normSq (A.1 k j) :=
      Finset.single_le_sum (λ k hk => h_nonneg k) (Finset.mem_univ i)
    linarith
  calc
    ‖A.1 i j‖ = Real.sqrt (Complex.normSq (A.1 i j)) := by rw [Complex.norm_def]
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h_bound_sq
    _ = 1 := by norm_num
lemma trace_re_bound (N : ℕ) (A : SU N) : |(trace ((A : Matrix (Fin N) (Fin N) ℂ))).re| ≤ N := by
  have h_entry : ∀ i : Fin N, |(A.1 i i).re| ≤ 1 := by
    intro i
    have h_norm : ‖A.1 i i‖ ≤ 1 := entry_norm_le_one N A i i
    have h_re_norm : |(A.1 i i).re| ≤ ‖A.1 i i‖ := Complex.abs_re_le_norm _
    linarith
  have h_trace_re : (trace ((A : Matrix (Fin N) (Fin N) ℂ))).re = ∑ i : Fin N, (A.1 i i).re := by
    simp [Matrix.trace, map_sum]
  rw [h_trace_re]
  calc
    |∑ i : Fin N, (A.1 i i).re| ≤ ∑ i : Fin N, |(A.1 i i).re| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (1 : ℝ) := Finset.sum_le_sum (λ i hi => h_entry i)
    _ = (N : ℝ) := by simp

-- ---------------------------------------------------------------
-- Compactness of SU(N)
-- ---------------------------------------------------------------

lemma continuous_det (N : ℕ) : Continuous (Matrix.det : Matrix (Fin N) (Fin N) ℂ → ℂ) := by
  have h_eq : (Matrix.det : Matrix (Fin N) (Fin N) ℂ → ℂ) = 
    λ A => ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • ∏ i : Fin N, A (σ i) i := by
    ext A; exact Matrix.det_apply A
  rw [h_eq]
  refine continuous_finsetSum _ (λ σ hσ => ?_)
  have h_prod : Continuous (λ (A : Matrix (Fin N) (Fin N) ℂ) => ∏ i : Fin N, A (σ i) i) := by
    refine continuous_finsetProd _ (λ i hi => ?_)
    have h1 : Continuous (λ (A : Matrix (Fin N) (Fin N) ℂ) => A (σ i)) :=
      continuous_apply (σ i)
    have h2 : Continuous (λ (f : (Fin N) → ℂ) => f i) :=
      continuous_apply i
    exact h2.comp h1
  exact (continuous_const.smul h_prod)

lemma isClosed_SU_range (N : ℕ) : IsClosed (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) := by
  let f1 : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ := λ A => A * star A
  let f2 : Matrix (Fin N) (Fin N) ℂ → ℂ := Matrix.det
  have h_cont_f1 : Continuous f1 :=
    Continuous.mul continuous_id ContinuousStar.continuous_star
  have h_cont_f2 : Continuous f2 := continuous_det N
  have h_closed_1 : IsClosed ({1} : Set (Matrix (Fin N) (Fin N) ℂ)) := isClosed_singleton
  have h_closed_2 : IsClosed ({1} : Set ℂ) := isClosed_singleton
  have h_closed_inter : IsClosed (f1⁻¹' ({1} : Set (Matrix (Fin N) (Fin N) ℂ)) ∩ f2⁻¹' ({1} : Set ℂ)) :=
    IsClosed.inter (IsClosed.preimage h_cont_f1 h_closed_1) (IsClosed.preimage h_cont_f2 h_closed_2)
  have h_eq : Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ) = 
    f1⁻¹' ({1} : Set (Matrix (Fin N) (Fin N) ℂ)) ∩ f2⁻¹' ({1} : Set ℂ) := by
    ext A
    constructor
    · rintro ⟨A', rfl⟩
      rcases A'.property with ⟨hA'_unitary, hA'_det⟩
      have hA' : (A' : Matrix (Fin N) (Fin N) ℂ) * star (A' : Matrix (Fin N) (Fin N) ℂ) = 1 := by
        simpa using Matrix.mem_unitaryGroup_iff.mp hA'_unitary
      have hdet : Matrix.det (A' : Matrix (Fin N) (Fin N) ℂ) = 1 := by
        simpa [MonoidHom.mem_mker] using hA'_det
      simp [f1, f2, hA', hdet]
    · rintro ⟨hA_star, hA_det⟩
      have hA_unitary : A ∈ Matrix.unitaryGroup (Fin N) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff]
        exact hA_star
      have hA_su : A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
        rw [Matrix.mem_specialUnitaryGroup_iff]
        exact ⟨hA_unitary, hA_det⟩
      exact ⟨⟨A, hA_su⟩, rfl⟩
  rw [h_eq]
  exact h_closed_inter

lemma norm_pi_le_of_forall (N : ℕ) (f : (Fin N) → (Fin N) → ℂ) (hf : ∀ i j, ‖f i j‖ ≤ 1) : ‖f‖ ≤ 1 := by
  rw [Pi.norm_def]
  have h_row : ∀ (i : Fin N), ‖f i‖ ≤ 1 := by
    intro i
    rw [Pi.norm_def]
    have h_sup_row : Finset.univ.sup (fun (j : Fin N) => ‖f i j‖₊) ≤ (1 : NNReal) := by
      apply Finset.sup_le
      intro j hj
      have h_entry : ‖f i j‖ ≤ 1 := hf i j
      exact_mod_cast h_entry
    exact_mod_cast h_sup_row
  have h_sup : Finset.univ.sup (fun (i : Fin N) => ‖f i‖₊) ≤ (1 : NNReal) := by
    apply Finset.sup_le
    intro i hi
    have h_row' : ‖f i‖ ≤ 1 := h_row i
    exact_mod_cast h_row'
  exact_mod_cast h_sup

/-- The homeomorphism between matrices and Pi types. -/
def matrixPiHomeomorph (N : ℕ) : Homeomorph (Matrix (Fin N) (Fin N) ℂ) ((Fin N) → (Fin N) → ℂ) := by
  refine {
    toFun := λ A i j => A i j
    invFun := λ f => λ i j => f i j
    left_inv := λ A => rfl
    right_inv := λ f => rfl
    continuous_toFun := by continuity
    continuous_invFun := by continuity
  }

/-- Homeomorphism between SU N and its image in matrices. -/
noncomputable def SUHomeomorphRange (N : ℕ) : Homeomorph (SU N) (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) := by
  have h_iff : ∀ (A : Matrix (Fin N) (Fin N) ℂ), 
      A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ ↔ A ∈ Set.range ((fun (A' : SU N) => (A' : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ) := by
    intro A
    constructor
    · intro hA
      exact ⟨⟨A, hA⟩, rfl⟩
    · rintro ⟨A', rfl⟩
      exact A'.property
  apply Homeomorph.subtype (Homeomorph.refl (Matrix (Fin N) (Fin N) ℂ)) h_iff

noncomputable instance (N : ℕ) : CompactSpace (SU N) := by
  -- Strategy: SU(N) is homeomorphic to its image in matrices, which is compact

  -- Step 1: The closed unit ball in the Pi type is compact
  have h_ball_compact : IsCompact (closedBall (0 : (Fin N) → (Fin N) → ℂ) 1) :=
    isCompact_closedBall (0 : (Fin N) → (Fin N) → ℂ) 1

  -- Step 2: Its image under the homeomorphism inverse is compact in matrices
  have h_compact_mat : IsCompact ((matrixPiHomeomorph N).symm '' closedBall (0 : (Fin N) → (Fin N) → ℂ) 1) :=
    (matrixPiHomeomorph N).symm.isCompact_image.mpr h_ball_compact

  -- Step 3: The range of SU N in matrices is a subset of this compact set
  have h_range_subset : Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ) ⊆
      (matrixPiHomeomorph N).symm '' closedBall (0 : (Fin N) → (Fin N) → ℂ) 1 := by
    intro A hA
    rcases hA with ⟨A', rfl⟩
    have h_entry : ∀ i j, ‖(A' : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 :=
      entry_norm_le_one N A'
    have h_norm : ‖(λ i j => (A' : Matrix (Fin N) (Fin N) ℂ) i j)‖ ≤ 1 :=
      norm_pi_le_of_forall N (λ i j => (A' : Matrix (Fin N) (Fin N) ℂ) i j) h_entry
    have h_mem : (λ i j => (A' : Matrix (Fin N) (Fin N) ℂ) i j) ∈ closedBall (0 : (Fin N) → (Fin N) → ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact h_norm
    refine ⟨(λ i j => (A' : Matrix (Fin N) (Fin N) ℂ) i j), h_mem, ?_⟩
    rfl

  -- Step 4: The range is closed
  have h_range_closed : IsClosed (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) :=
    isClosed_SU_range N

  -- Step 5: The range is compact (closed subset of a compact set)
  have h_range_compact : IsCompact (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) := by
    have h_inter_eq : ((matrixPiHomeomorph N).symm '' closedBall (0 : (Fin N) → (Fin N) → ℂ) 1) ∩
      Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ) =
      Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ) :=
      Set.inter_eq_right.mpr h_range_subset
    rw [← h_inter_eq]
    exact IsCompact.inter_right h_compact_mat h_range_closed

  -- Step 6: Use isCompact_iff_compactSpace and the homeomorphism
  have h_compact_range_type : CompactSpace (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) :=
    (isCompact_iff_compactSpace.mp h_range_compact)

  -- SU N is homeomorphic to this range, so CompactSpace transfers
  exact Homeomorph.compactSpace (SUHomeomorphRange N).symm

/-- SU(N) is second-countable because it embeds into the Euclidean space of matrices. -/
instance (N : ℕ) : SecondCountableTopology (SU N) := by
  -- The image of SU(N) under the embedding into matrices is compact, hence second-countable.
  -- Since `SU N` is homeomorphic to its image, it is also second-countable.
  haveI h_image : SecondCountableTopology (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) := by
    -- The range is a subset of `Matrix (Fin N) (Fin N) ℂ` which is second-countable
    -- because it is homeomorphic to `(Fin N) → (Fin N) → ℂ` (finite product of ℂ).
    haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
      (matrixPiHomeomorph N).secondCountableTopology
    -- The image is a subspace, hence second-countable (via `Subtype.secondCountableTopology` instance)
    infer_instance
  -- SU(N) is homeomorphic to its image, hence second-countable
  have h_homeo : Homeomorph (SU N) (Set.range ((fun (A : SU N) => (A : Matrix (Fin N) (Fin N) ℂ)) : SU N → Matrix (Fin N) (Fin N) ℂ)) :=
    SUHomeomorphRange N
  exact h_homeo.secondCountableTopology
/--
The dimension of SU(N) as a real Lie group is N² - 1.
-/
def dimensionSU (N : ℕ) : ℕ :=
  N*N - 1

/--
The Lie algebra su(N): skew-Hermitian traceless complex matrices.
As a real vector space, these are `X ∈ M_N(ℂ)` such that `X† = -X` and `Tr(X) = 0`.
-/
structure LieAlgebraSU (N : ℕ) : Type where
  /-- The underlying matrix. -/
  matrix : Matrix (Fin N) (Fin N) ℂ
  /-- Skew-Hermitian condition: X† = -X. -/
  skewHermitian : matrixᴴ = -matrix
  /-- Traceless condition: Tr(X) = 0. -/
  traceless : trace matrix = 0

/--
The structure constants of su(N) in a basis {T^a}: [T^a, T^b] = i f^{abc} T^c
Here `f : Fin dim → Fin dim → Fin dim → ℝ` are the totally antisymmetric structure constants.
-/
structure StructureConstants (N : ℕ) : Type 1 where
  /-- The dimension of the Lie algebra. -/
  dim : ℕ
  /-- The totally antisymmetric structure constants f^{abc} -/
  f : (Fin dim) → (Fin dim) → (Fin dim) → ℝ
  /-- Antisymmetry in first two indices -/
  antisymm : ∀ a b c, f a b c = - f b a c
  /-- Jacobi identity -/
  jacobi : ∀ a b c d e : Fin dim,
    f a b c * f c d e + f a d c * f c b e + f a e c * f c d b = 0

/--
The matrix exponential map exp : su(N) → SU(N).
In a full formalization this would use a matrix exponential function.
Mathlib does not currently have a general matrix exponential, so this is a placeholder.
-/
noncomputable def exponentialMap (N : ℕ) (_X : LieAlgebraSU N) : SU N :=
  1

end YangMills
