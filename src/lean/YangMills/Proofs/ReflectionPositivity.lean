/-
# Reflection Positivity on the Lattice

Reflection positivity (Osterwalder-Schrader positivity) is the key axiom
connecting Euclidean quantum field theory to Minkowski quantum field theory
via the OS reconstruction theorem.

For SU(N) lattice gauge theory, reflection positivity states:

    ⟨f θ(f)⟩ ≥ 0

for any observable f depending only on link variables in the positive-time
half-lattice (t > 0). Here θ is the time-reflection map:

    (θ U)(n, μ) = U(θ n, μ)⁻¹   if μ = 0 (time direction)
    (θ U)(n, μ) = U(θ n, μ)     if μ ≠ 0 (spatial direction)
-/

import YangMills.Lattice
import YangMills.SpecialUnitary
import YangMills.Proofs.LatticeMeasure
import YangMills.Proofs.BasicLemmas
import YangMills.Proofs.PeterWeyl
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
namespace YangMills
namespace Lattice

/--
The reflection of an observable on any lattice type with `ReflectSite`:
    (θ f)(U) = f(θ U)
where θ acts on link variables via `reflectLinkVariable`.
-/
def reflectObservable (N : ℕ) {Λ : Type} [ReflectSite Λ] (f : LinkVariable (SU N) Λ → ℝ) :
    LinkVariable (SU N) Λ → ℝ :=
  λ U => f (reflectLinkVariable N U)

lemma reflectObservable_involution (N : ℕ) {Λ : Type} [ReflectSite Λ] (f : LinkVariable (SU N) Λ → ℝ)
    (U : LinkVariable (SU N) Λ) : reflectObservable N (reflectObservable N f) U = f U := by
  dsimp [reflectObservable]
  rw [reflection_involution N U]
/--
The reflection of an observable on ℤ⁴ under the full geometric reflection:
    (θ f)(U) = f(θ U)
where θ acts on link variables via `reflectLinkVariableZ4`.
-/
def reflectObservableZ4 (N : ℕ) (f : LinkVariable (SU N) Z4Site → ℝ) : LinkVariable (SU N) Z4Site → ℝ :=
  λ U => f (reflectLinkVariableZ4 N U)

/--
The expectation-like pairing for reflection positivity on ℤ⁴.

Given a Wilson action S_W and a reference measure dU (product Haar measure),
the expectation of an observable F is:

    ⟨F⟩ = (1/Z) ∫ F(U) exp(-S_W[U]) dU

For the factorization lemma, we only need the formal algebraic structure
of this expression. The actual integration theory (Haar measure, product
measure, partition function) is available in Mathlib but requires heavy
infrastructure. Here we give the symbolic manipulation that underlies
the reflection positivity proof.

⚠️ **Known limitation**: The `linearity` field requires integrability hypotheses
on `F(extend...)*exp(-β*S)` and `G(extend...)*exp(-β*S)`. This is mathematically
correct (linearity of expectation requires integrability). The `reflectionPositive`
field relies on `gibbsExpectationZ4_reflection_positive` which has the `hadd` issue
documented in `docs/hadd_issue.md`.
-/
structure Z4Expectation (N : ℕ) (β : ℝ) (sites : Finset Z4Site) : Type 1 where
  /-- The partition function Z = ∫ exp(-S_W) dU. -/
  partitionFunction : ℝ
  /-- Positivity of the partition function: Z > 0 for β > 0. -/
  partitionFunctionPos : partitionFunction > 0
  /--
  The expectation of an observable F, symbolically:
      ⟨F⟩ = (1/Z) ∫ F(U) exp(-S_W[U]) dU
  -/
  evaluate : (LinkVariable (SU N) Z4Site → ℝ) → ℝ
  /--
  The expectation is linear: ⟨aF + bG⟩ = a⟨F⟩ + b⟨G⟩,
  provided the integrands F(U) exp(-β S_W[U]) and G(U) exp(-β S_W[U]) are integrable
  with respect to the product Haar measure.
  -/
  linearity : ∀ (a b : ℝ) (F G : LinkVariable (SU N) Z4Site → ℝ),
    (MeasureTheory.Integrable (λ (cfg : FiniteLinkConfigZ4 N sites) => F (extendLinkVariableZ4 N sites cfg) *
      Real.exp (-β * wilsonActionFiniteConfigZ4 N β sites cfg)) (productHaarMeasureZ4 N sites)) →
    (MeasureTheory.Integrable (λ (cfg : FiniteLinkConfigZ4 N sites) => G (extendLinkVariableZ4 N sites cfg) *
      Real.exp (-β * wilsonActionFiniteConfigZ4 N β sites cfg)) (productHaarMeasureZ4 N sites)) →
    evaluate (λ U => a * F U + b * G U) = a * evaluate F + b * evaluate G
  /--
  The expectation is normalized: ⟨1⟩ = 1.
  -/
  normalization : evaluate (λ _ => 1) = 1
  /--
  The expectation is positive: if F ≥ 0 pointwise, then ⟨F⟩ ≥ 0.
  -/
  positivity : ∀ (F : LinkVariable (SU N) Z4Site → ℝ),
    (∀ U, F U ≥ 0) → evaluate F ≥ 0
  /--
  Reflection positivity: for any observable f, we have ⟨f θ(f)⟩ ≥ 0.
  
  This is the conclusion of the Osterwalder-Seiler factorization lemma:
  the expectation of f θ(f) is an L² norm squared, hence non-negative.
  -/
  reflectionPositive : ∀ (f : LinkVariable (SU N) Z4Site → ℝ),
    evaluate (λ U => f U * reflectObservableZ4 N f U) ≥ 0

/--
Construct a `Z4Expectation` for the Wilson action on a finite ℤ⁴ lattice.
This provides the reflection positivity certificate for the Wilson action.
-/
noncomputable def wilsonZ4Expectation (N : ℕ) (β : ℝ) (sites : Finset Z4Site)
    (hadd : ∀ n, n ∈ sites → addVector n 0 ∈ sites)
    (hsites : ∀ n, n ∈ sites → reflectSite n ∈ sites) : Z4Expectation N β sites :=
  {
    partitionFunction := partitionFunctionFiniteZ4 N β sites
    partitionFunctionPos := partitionFunctionFiniteZ4_pos N β sites
    evaluate := gibbsExpectationZ4 N β sites
    linearity := λ a b F G hF hG => gibbsExpectationZ4_linear N β sites a b F G hF hG
    normalization := gibbsExpectationZ4_normalization N β sites
    positivity := λ F hF => gibbsExpectationZ4_pos N β sites F hF
    reflectionPositive := λ f => 
      gibbsExpectationZ4_reflection_positive N β sites hadd hsites f
  }

/--
The SU(N) lattice Yang-Mills measure with the Wilson action on any finite ℤ⁴ lattice
satisfying the closure conditions `hadd` and `hsites` is reflection positive.

⚠️ **Status**: Validated by the Lean kernel. The proof of `gibbsExpectationZ4_reflection_positive`
is mathematically vacuous for nonempty finite lattices due to the `hadd` issue (see
`docs/hadd_issue.md`). A complete proof requires implementing periodic boundary conditions
and the Osterwalder-Seiler factorization.
-/
theorem lattice_ym_reflection_positive (N : ℕ) (β : ℝ) (hβ : β > 0)
    (sites : Finset Z4Site) (hadd : ∀ n, n ∈ sites → addVector n 0 ∈ sites)
    (hsites : ∀ n, n ∈ sites → reflectSite n ∈ sites) :
    ∀ (f : LinkVariable (SU N) Z4Site → ℝ),
      (wilsonZ4Expectation N β sites hadd hsites).evaluate (λ U => f U * reflectObservableZ4 N f U) ≥ 0 := by
  intro f
  exact (wilsonZ4Expectation N β sites hadd hsites).reflectionPositive f

/-! ### Periodic Lattice (PeriodicSite) -/

section PeriodicSite

open scoped BigOperators

/--
Signed lift of `ZMod T` to `ℤ`. For an odd T, this gives a symmetric representation
where `t` and `-t` map to opposite integers. The element `0` maps to `0`.
-/
noncomputable def signedTime (T : ℕ) (t : ZMod T) : ℤ :=
  if h : (t.val : ℕ) ≤ (T-1)/2 then (t.val : ℤ) else (t.val : ℤ) - (T : ℤ)

lemma signedTime_neg (T : ℕ) [NeZero T] (t : ZMod T) (hT : Odd T) : signedTime T (-t) = -signedTime T t := by
  unfold signedTime
  have h_val_lt : t.val < T := ZMod.val_lt t
  rcases hT with ⟨k, hT⟩
  have hTodd : (T : ℤ) = 2*(k : ℤ) + 1 := by exact_mod_cast hT
  by_cases hzero : t = 0
  · subst hzero; simp
  · have hzero_val : t.val ≠ 0 := by rwa [ZMod.val_ne_zero]
    haveI : NeZero t := ⟨hzero⟩
    have h_neg_val_nat : (-t).val = T - t.val := ZMod.val_neg_of_ne_zero (a := t)
    have h_neg_val : ((-t).val : ℤ) = (T : ℤ) - (t.val : ℤ) := by
      have h_le : t.val ≤ T := Nat.le_of_lt h_val_lt
      simp [h_neg_val_nat, Nat.cast_sub h_le, Nat.cast_ofNat]
    split_ifs with h1 h2
    · -- Both h1 and h2 hold: ((-t).val : ℕ) ≤ (T-1)/2 and (t.val : ℕ) ≤ (T-1)/2
      -- Then (-t).val = T - t.val, and we have T - t.val ≤ (T-1)/2
      -- But if t.val ≤ (T-1)/2 then T - t.val > (T-1)/2, contradiction
      have : T - t.val > (T-1)/2 := by omega
      rw [h_neg_val_nat] at h1
      omega
    · -- h1 true, h2 false: ((-t).val : ℕ) ≤ (T-1)/2, (t.val : ℕ) > (T-1)/2
      rw [h_neg_val_nat] at h1
      omega
    · -- h1 false, h2 true: ((-t).val : ℕ) > (T-1)/2, (t.val : ℕ) ≤ (T-1)/2
      omega
    · -- Both false
      omega

/--
The set of lattice sites with positive signed time (strictly positive).
-/
noncomputable def positiveSites (T L : ℕ) [NeZero T] [NeZero L] : Finset (PeriodicSite T L) :=
  Finset.filter (λ n => signedTime T n.time > 0) Finset.univ

/--
The set of lattice sites with negative signed time.
-/
noncomputable def negativeSites (T L : ℕ) [NeZero T] [NeZero L] : Finset (PeriodicSite T L) :=
  Finset.filter (λ n => signedTime T n.time < 0) Finset.univ

/--
The set of lattice sites at the time interface (signed time = 0).
-/
noncomputable def interfaceSites (T L : ℕ) [NeZero T] [NeZero L] : Finset (PeriodicSite T L) :=
  Finset.filter (λ n => signedTime T n.time = 0) Finset.univ

/--
The positive-time part of the Wilson action.
-/
noncomputable def wilsonActionPeriodicPositive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  wilsonActionFinite N β (positiveSites T L) U

/--
The negative-time part of the Wilson action.
-/
noncomputable def wilsonActionPeriodicNegative (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  wilsonActionFinite N β (negativeSites T L) U

/--
The interface part of the Wilson action.
-/
noncomputable def wilsonActionPeriodicInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  wilsonActionFinite N β (interfaceSites T L) U

/--
The total action decomposes into positive, negative, and interface parts:
    S_W = S⁺ + S⁻ + S_int
-/
lemma total_decomposition_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U =
    wilsonActionPeriodicPositive N T L β U +
    wilsonActionPeriodicNegative N T L β U +
    wilsonActionPeriodicInterface N T L β U := by
  unfold wilsonActionFinite
  have h_cover : (Finset.univ : Finset (PeriodicSite T L)) =
      positiveSites T L ∪ negativeSites T L ∪ interfaceSites T L := by
    ext n; simp [positiveSites, negativeSites, interfaceSites]
    by_cases hpos : signedTime T n.time > 0
    · simp [hpos]
    · by_cases hneg : signedTime T n.time < 0
      · simp [hpos, hneg]
      · have hzero : signedTime T n.time = 0 := by
          have hle : signedTime T n.time ≤ 0 := by linarith
          have hge : signedTime T n.time ≥ 0 := by linarith
          linarith
        simp [hpos, hneg, hzero]
  rw [h_cover]
  have h_disjoint_pos_neg : Disjoint (positiveSites T L) (negativeSites T L) := by
    unfold positiveSites negativeSites
    rw [Finset.disjoint_filter]
    intro n hn hpos
    intro hneg
    linarith
  have h_disjoint_neg_int : Disjoint (negativeSites T L) (interfaceSites T L) := by
    unfold negativeSites interfaceSites
    rw [Finset.disjoint_filter]
    intro n hn hneg
    intro hzero
    linarith
  have h_disjoint_pos_int : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]
    intro n hn hpos
    intro hzero
    linarith
  have h_disjoint_union_int : Disjoint (positiveSites T L ∪ negativeSites T L) (interfaceSites T L) := by
    rw [Finset.disjoint_union_left]
    exact ⟨h_disjoint_pos_int, h_disjoint_neg_int⟩
  calc
    ∑ n ∈ (positiveSites T L ∪ negativeSites T L) ∪ interfaceSites T L,
        ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν
        = (∑ n ∈ positiveSites T L ∪ negativeSites T L,
            ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν) +
          (∑ n ∈ interfaceSites T L,
            ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν) := by
      rw [Finset.sum_union h_disjoint_union_int]
    _ = (∑ n ∈ positiveSites T L,
            ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν) +
        (∑ n ∈ negativeSites T L,
            ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν) +
        (∑ n ∈ interfaceSites T L,
            ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν) := by
      rw [Finset.sum_union h_disjoint_pos_neg, add_assoc]
    _ = wilsonActionPeriodicPositive N T L β U + wilsonActionPeriodicNegative N T L β U +
        wilsonActionPeriodicInterface N T L β U := by
      rfl

/--
A function `f : LinkVariable (SU N) (PeriodicSite T L) → ℝ` depends only on
positive-time and interface (time-0) links iff its value is determined by
the values of the link variable on `positiveSites T L ∪ interfaceSites T L`.
This is the correct hypothesis for the Osterwalder-Seiler reflection positivity
theorem: only observables localized in the positive-time region (including the
interface at time 0) are required to satisfy ⟨θf, f⟩ ≥ 0.

⚠️ **Mathematical note**: The lemma `gibbsExpectationPeriodic_reflection_positive`
as originally stated (without this hypothesis) is **false** in general.  A
counterexample exists even for β=0 (free theory): take
`f(U) = a(U(ℓ))·b(U(θℓ)) - a(U(θℓ))·b(U(ℓ))` for a positive-site link ℓ
and its reflection θℓ.  Then `f·θf = -(f)²` and its integral is strictly negative.
The hypothesis that `f` depends only on positive+interface links excludes such
counterexamples.
-/
def dependsOnlyOnPosInterface (N T L : ℕ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) : Prop :=
  ∀ (U V : LinkVariable (SU N) (PeriodicSite T L)),
    (∀ (n : PeriodicSite T L) (μ : Fin 4),
      n ∈ (positiveSites T L ∪ interfaceSites T L) → U.value n μ = V.value n μ) → f U = f V

/-! ### Osterwalder-Seiler decomposition (plaquette-based) -/
open scoped BigOperators

/-- Index type for oriented plaquettes on a periodic lattice: (base site, μ, ν). -/
abbrev PlaquetteIndex (T L : ℕ) : Type := PeriodicSite T L × Fin 4 × Fin 4

instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (PlaquetteIndex T L) :=
  inferInstanceAs (Fintype (PeriodicSite T L × Fin 4 × Fin 4))

/-- Cyclic permutation of trace for 4 matrices: Tr(ABCD) = Tr(BCDA). -/
lemma trace_cyclic_four (N : ℕ) (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  calc
    Matrix.trace (A * B * C * D) = Matrix.trace (D * (A * B * C)) := by
      rw [Matrix.trace_mul_comm (A * B * C) D]
    _ = Matrix.trace (D * A * B * C) := by noncomm_ring
    _ = Matrix.trace ((D * A) * (B * C)) := by noncomm_ring
    _ = Matrix.trace ((B * C) * (D * A)) := Matrix.trace_mul_comm (D * A) (B * C)
    _ = Matrix.trace (B * C * D * A) := by noncomm_ring
/-- For A ∈ SU(N), Re Tr(A) = Re Tr(A⁻¹). -/
lemma trace_re_inv (N : ℕ) (A : SU N) :
    ((Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace (((A⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  have hstar : (A⁻¹ : SU N) = (star A : SU N) := by
    simpa using (Matrix.star_eq_inv (A : SU N)).symm
  have h_trace_star : Matrix.trace (star ((A : Matrix (Fin N) (Fin N) ℂ))) =
      star (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))) := by
    simp [Matrix.trace, map_sum]
  calc
    ((Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
        ((star (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ)))).re : ℝ) := by simp
    _ = ((Matrix.trace (star ((A : Matrix (Fin N) (Fin N) ℂ)))).re : ℝ) := by
      simp [h_trace_star]
    _ = ((Matrix.trace (((A⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by simp [hstar]

/-- The sum over all oriented plaquettes (n; μ, ν) where all four corners have
positive signed time. This is the correct positive-time part of the
Osterwalder-Seiler decomposition. -/
noncomputable def wilsonActionOSPositive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time > 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The sum over all oriented plaquettes (n; μ, ν) where all four corners have
negative signed time. This is the correct negative-time part of the
Osterwalder-Seiler decomposition. -/
noncomputable def wilsonActionOSNegative (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time < 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The sum over the remaining oriented plaquettes (those with corners on both sides
of the time interface). This is the interface part of the
Osterwalder-Seiler decomposition. -/
noncomputable def wilsonActionOSInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
       ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) then
      plaquetteContribution N β U n μ ν
    else 0

/--
For each oriented plaquette (n; μ, ν), exactly one of the three conditions holds:
positive (all corners > 0), negative (all corners < 0), or interface (the rest).
-/
lemma plaquette_classification (T L : ℕ) [NeZero T] [NeZero L] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time > 0) ∨
    (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time < 0) ∨
    (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
        signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
        signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
     ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
        signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
        signedTime T (addVectorPeriodic T L n ν).time < 0)) := by
  by_cases hpos : signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0
  · exact Or.inl hpos
  · by_cases hneg : signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                   signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                   signedTime T (addVectorPeriodic T L n ν).time < 0
    · exact Or.inr (Or.inl hneg)
    · exact Or.inr (Or.inr ⟨hpos, hneg⟩)

/--
The total Wilson action decomposes into positive, negative, and interface parts
(plaquette-based OS decomposition):
    S_W = S_OS⁺ + S_OS⁻ + S_OS_int
-/
lemma total_decomposition_os_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U =
    wilsonActionOSPositive N T L β U +
    wilsonActionOSNegative N T L β U +
    wilsonActionOSInterface N T L β U := by
  unfold wilsonActionOSPositive wilsonActionOSNegative wilsonActionOSInterface wilsonActionFinite
  have h_split (n : PeriodicSite T L) (μ ν : Fin 4) : plaquetteContribution N β U n μ ν =
    (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
         signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
         signedTime T (addVectorPeriodic T L n ν).time > 0 then
      plaquetteContribution N β U n μ ν else 0) +
    (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
         signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
         signedTime T (addVectorPeriodic T L n ν).time < 0 then
      plaquetteContribution N β U n μ ν else 0) +
    (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
       ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) then
      plaquetteContribution N β U n μ ν else 0) := by
    rcases plaquette_classification T L n μ ν with (⟨h1, h2, h3, h4⟩|⟨h1, h2, h3, h4⟩|⟨hnpos, hnneg⟩)
    · -- All signed times > 0
      have h_neg : ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) := by
        intro h; rcases h with ⟨hn1, hn2, hn3, hn4⟩; have := h1; linarith
      have h_int : ¬ (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0)) := by
        intro h; rcases h with ⟨hnpos', hnneg'⟩; apply hnpos'; exact ⟨h1, h2, h3, h4⟩
      calc
        plaquetteContribution N β U n μ ν
            = (plaquetteContribution N β U n μ ν) + 0 + 0 := by ring
        _ = (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
               ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0) then
              plaquetteContribution N β U n μ ν else 0) := by
          rw [if_pos ⟨h1, h2, h3, h4⟩, if_neg h_neg, if_neg h_int]
    · -- All signed times < 0
      have h_pos : ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) := by
        intro h; rcases h with ⟨hp1, hp2, hp3, hp4⟩; have := h1; linarith
      have h_int : ¬ (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0)) := by
        intro h; rcases h with ⟨hnpos', hnneg'⟩; apply hnneg'; exact ⟨h1, h2, h3, h4⟩
      calc
        plaquetteContribution N β U n μ ν
            = 0 + (plaquetteContribution N β U n μ ν) + 0 := by ring
        _ = (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
               ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0) then
              plaquetteContribution N β U n μ ν else 0) := by
          rw [if_neg h_pos, if_pos ⟨h1, h2, h3, h4⟩, if_neg h_int]
    · -- Interface case: neither all positive nor all negative
      have h_int_cond : (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0)) := ⟨hnpos, hnneg⟩
      calc
        plaquetteContribution N β U n μ ν
            = 0 + 0 + (plaquetteContribution N β U n μ ν) := by ring
        _ = (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
               ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0) then
              plaquetteContribution N β U n μ ν else 0) := by
          rw [if_neg hnpos, if_neg hnneg, if_pos h_int_cond]
  have h_sum : ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ((if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 then
          plaquetteContribution N β U n μ ν else 0) +
        (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 then
          plaquetteContribution N β U n μ ν else 0) +
        (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
           ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0) then
          plaquetteContribution N β U n μ ν else 0)) := by
    refine Finset.sum_congr rfl (λ n hn => ?_)
    refine Finset.sum_congr rfl (λ μ hμ => ?_)
    refine Finset.sum_congr rfl (λ ν hν => ?_)
    exact h_split n μ ν
  rw [h_sum]
  simp [Finset.sum_add_distrib]

lemma reflectSite_addVector_comm (T L : ℕ) (n : PeriodicSite T L) (μ : Fin 4) (hμ0 : μ ≠ 0) :
    ReflectSite.reflectSite (AddVector.addVector n μ) =
    AddVector.addVector (ReflectSite.reflectSite n) μ := by
  -- For spatial directions (μ ≠ 0), reflection commutes with adding a basis vector
  fin_cases μ
  · -- μ = 0 is excluded by hμ0
    exfalso; exact hμ0 rfl
  · -- μ = 1 (x direction): adding e_x doesn't change time, so reflection commutes
    ext <;> simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic]
  · -- μ = 2 (y direction)
    ext <;> simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic]
  · -- μ = 3 (z direction)
    ext <;> simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic]

/-- For spatial directions (μ ≠ 0), addition and reflection commute at the level of
    the reflected site applied twice. -/
lemma reflectSite_addVector_comm_two (T L : ℕ) (n : PeriodicSite T L) (μ ν : Fin 4) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n μ) ν) =
    AddVector.addVector (AddVector.addVector (ReflectSite.reflectSite n) μ) ν := by
  calc
    ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n μ) ν)
        = AddVector.addVector (ReflectSite.reflectSite (AddVector.addVector n μ)) ν :=
      reflectSite_addVector_comm T L (AddVector.addVector n μ) ν hν0
    _ = AddVector.addVector (AddVector.addVector (ReflectSite.reflectSite n) μ) ν := by
      rw [reflectSite_addVector_comm T L n μ hμ0]

lemma trace_plaquetteProduct_reflect_ss (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U) (ReflectSite.reflectSite n) μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  have h_eq : plaquetteProduct N (reflectLinkVariable N U) (ReflectSite.reflectSite n) μ ν =
      plaquetteProduct N U n μ ν := by
    dsimp [plaquetteProduct, reflectLinkVariable]
    simp [hμ0, hν0]
    rw [ReflectSite.involution n]
    rw [reflectSite_addVector_comm T L (ReflectSite.reflectSite n) μ hμ0, ReflectSite.involution n]
    rw [reflectSite_addVector_comm_two T L (ReflectSite.reflectSite n) μ ν hμ0 hν0, ReflectSite.involution n]
    rw [reflectSite_addVector_comm T L (ReflectSite.reflectSite n) ν hν0, ReflectSite.involution n]
  simpa [h_eq]

lemma trace_plaquetteProduct_reflect_ts (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (ν : Fin 4)
    (hν0 : ν ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N U n 0 ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  set a := U.value n 0
  set b := U.value (addVectorPeriodic T L n 0) ν
  set c := (U.value (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν) 0)⁻¹
  set d := (U.value (addVectorPeriodic T L n ν) ν)⁻¹
  have h_original : ((plaquetteProduct N U n 0 ν : Matrix (Fin N) (Fin N) ℂ)) = a * b * c * d := by
    dsimp [plaquetteProduct, a, b, c, d]; rfl
  set m := ReflectSite.reflectSite (addVectorPeriodic T L n 0)
  have h_reflected : ((plaquetteProduct N (reflectLinkVariable N U) m ν 0 : Matrix (Fin N) (Fin N) ℂ)) = b * c * d * a := by
    dsimp only [plaquetteProduct]
    -- Factor 1: (θU)(m, ν) = U(θm, ν) = U(n+e₀, ν) = b
    have h_f1 : (reflectLinkVariable N U).value m ν = b := by
      dsimp [reflectLinkVariable, m, b]
      simp [hν0, ReflectSite.involution]
    -- Factor 2: (θU)(m+e_ν, 0) = (U(θ(m+e_ν), 0))⁻¹ = (U(n+e₀+e_ν, 0))⁻¹ = c
    have h_f2 : (reflectLinkVariable N U).value (AddVector.addVector m ν) 0 = c := by
      dsimp [reflectLinkVariable, c]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m ν) = addVectorPeriodic T L (addVectorPeriodic T L n 0) ν := by
        calc
          ReflectSite.reflectSite (AddVector.addVector m ν)
              = AddVector.addVector (ReflectSite.reflectSite m) ν :=
            reflectSite_addVector_comm T L m ν hν0
          _ = AddVector.addVector (addVectorPeriodic T L n 0) ν := by simp [m, ReflectSite.involution]
      simp [hν0, h_θ]
    have h_f3 : ((reflectLinkVariable N U).value (AddVector.addVector (AddVector.addVector m ν) 0) ν)⁻¹ = d := by
      dsimp [reflectLinkVariable, d]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector m ν) 0) = addVectorPeriodic T L n ν := by
        fin_cases ν
        · exfalso; exact hν0 rfl
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [hν0, h_θ]
    -- Factor 4: ((θU)(m+e_0, 0))⁻¹ = ((U(θ(m+e_0), 0))⁻¹)⁻¹ = U(n, 0) = a
    have h_f4 : ((reflectLinkVariable N U).value (AddVector.addVector m 0) 0)⁻¹ = a := by
      dsimp [reflectLinkVariable, a]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = n := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [h_θ]
    rw [h_f1, h_f2, h_f3, h_f4]
    simp [map_mul]
  rw [h_original, h_reflected]
  exact congrArg (fun x => x.re) (trace_cyclic_four N (a : Matrix (Fin N) (Fin N) ℂ) b c d)

lemma trace_plaquetteProduct_reflect_st (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ : Fin 4)
    (hμ0 : μ ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N U n μ 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0 μ : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  set a := U.value n μ
  set b := U.value (addVectorPeriodic T L n μ) 0
  set c := (U.value (addVectorPeriodic T L (addVectorPeriodic T L n μ) 0) μ)⁻¹
  set d := (U.value (addVectorPeriodic T L n 0) 0)⁻¹
  have h_original : ((plaquetteProduct N U n μ 0 : Matrix (Fin N) (Fin N) ℂ)) = a * b * c * d := by
    dsimp [plaquetteProduct, a, b, c, d]; rfl
  set m := ReflectSite.reflectSite (addVectorPeriodic T L n 0)
  have h_reflected : ((plaquetteProduct N (reflectLinkVariable N U) m 0 μ : Matrix (Fin N) (Fin N) ℂ)) = d * a * b * c := by
    dsimp only [plaquetteProduct]
    -- Factor 1: (θU)(m, 0) = (U(θm, 0))⁻¹ = (U(n+e₀, 0))⁻¹ = d
    have h_f1 : (reflectLinkVariable N U).value m 0 = d := by
      have h_θm : ReflectSite.reflectSite m = addVectorPeriodic T L n 0 := by
        simp [m, ReflectSite.involution]
      simp [reflectLinkVariable, h_θm, d]
    -- Factor 2: (θU)(m+e_0, μ) = U(θ(m+e_0), μ) = U(n, μ) = a
    have h_f2 : (reflectLinkVariable N U).value (AddVector.addVector m 0) μ = a := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = n := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, hμ0, h_θ, a]
    -- Factor 3: ((θU)(m+e_0+e_μ, 0))⁻¹ = ((U(θ(m+e_0+e_μ), 0))⁻¹)⁻¹ = U(θ(m+e_0+e_μ), 0) = U(n+e_μ, 0) = b
    have h_f3 : ((reflectLinkVariable N U).value (AddVector.addVector (AddVector.addVector m 0) μ) 0)⁻¹ = b := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector m 0) μ) = addVectorPeriodic T L n μ := by
        fin_cases μ
        · exfalso; exact hμ0 rfl
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, b]
    -- Factor 4: ((θU)(m+e_μ, μ))⁻¹ = (U(θ(m+e_μ), μ))⁻¹ = (U(n+e₀+e_μ, μ))⁻¹ = c
    have h_f4 : ((reflectLinkVariable N U).value (AddVector.addVector m μ) μ)⁻¹ = c := by
      dsimp [reflectLinkVariable, c]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m μ) = addVectorPeriodic T L (addVectorPeriodic T L n 0) μ := by
        calc
          ReflectSite.reflectSite (AddVector.addVector m μ)
              = AddVector.addVector (ReflectSite.reflectSite m) μ :=
            reflectSite_addVector_comm T L m μ hμ0
          _ = AddVector.addVector (addVectorPeriodic T L n 0) μ := by simp [m, ReflectSite.involution]
      have h_comm : addVectorPeriodic T L (addVectorPeriodic T L n 0) μ = addVectorPeriodic T L (addVectorPeriodic T L n μ) 0 := by
        fin_cases μ
        · exfalso; exact hμ0 rfl
        · ext <;> simp [addVectorPeriodic]
        · ext <;> simp [addVectorPeriodic]
        · ext <;> simp [addVectorPeriodic]
      simp [hμ0, h_θ, h_comm]
    rw [h_f1, h_f2, h_f3, h_f4]
    rfl
  rw [h_original, h_reflected]
  exact congrArg (fun x => x.re) (trace_cyclic_four N (d : Matrix (Fin N) (Fin N) ℂ) a b c).symm

lemma trace_plaquetteProduct_reflect_tt (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) :
    ((Matrix.trace ((plaquetteProduct N U n 0 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  set a := U.value n 0
  set b := U.value (addVectorPeriodic T L n 0) 0
  set c := (U.value (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0) 0)⁻¹
  set d := (U.value (addVectorPeriodic T L n 0) 0)⁻¹
  have h_original : ((plaquetteProduct N U n 0 0 : Matrix (Fin N) (Fin N) ℂ)) = a * b * c * d := by
    dsimp [plaquetteProduct, a, b, c, d]; rfl
  set m := ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)
  have h_reflected : ((plaquetteProduct N (reflectLinkVariable N U) m 0 0 : Matrix (Fin N) (Fin N) ℂ)) = c * d * a * b := by
    dsimp only [plaquetteProduct]
    -- Factor 1: (θU)(m, 0) = (U(θm, 0))⁻¹ = (U(n+2e₀, 0))⁻¹ = c
    have h_f1 : (reflectLinkVariable N U).value m 0 = c := by
      have h_θm : ReflectSite.reflectSite m = addVectorPeriodic T L (addVectorPeriodic T L n 0) 0 := by
        simp [m, ReflectSite.involution]
      simp [reflectLinkVariable, h_θm, c]
    -- Factor 2: (θU)(m+e_0, 0) = (U(θ(m+e_0), 0))⁻¹ = (U(n+e₀, 0))⁻¹ = d
    have h_f2 : (reflectLinkVariable N U).value (AddVector.addVector m 0) 0 = d := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = addVectorPeriodic T L n 0 := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, d]
    -- Factor 3: ((θU)(m+2e_0, 0))⁻¹ = ((U(θ(m+2e_0), 0))⁻¹)⁻¹ = U(θ(m+2e_0), 0) = U(n, 0) = a
    have h_f3 : ((reflectLinkVariable N U).value (AddVector.addVector (AddVector.addVector m 0) 0) 0)⁻¹ = a := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector m 0) 0) = n := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, a]
    -- Factor 4: ((θU)(m+e_0, 0))⁻¹ = ((U(θ(m+e_0), 0))⁻¹)⁻¹ = U(θ(m+e_0), 0) = U(n+e₀, 0) = b
    have h_f4 : ((reflectLinkVariable N U).value (AddVector.addVector m 0) 0)⁻¹ = b := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = addVectorPeriodic T L n 0 := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, b]
    rw [h_f1, h_f4, h_f2, h_f3]
    rfl
  rw [h_original, h_reflected]
  exact congrArg (fun x => x.re)
    (Eq.trans (trace_cyclic_four N (a : Matrix (Fin N) (Fin N) ℂ) b c d)
      (trace_cyclic_four N (b : Matrix (Fin N) (Fin N) ℂ) c d a))
section ConditionEquivalence

open scoped BigOperators

/-- For spatial-spatial plaquettes (μ≠0, ν≠0), the signed times at reflected corners
are the negations of the signed times at the original corners. -/
lemma signedTime_ss_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) (μ ν : Fin 4) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) μ).time = -signedTime T (addVectorPeriodic T L n μ).time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite n) μ) ν).time = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) ν).time = -signedTime T (addVectorPeriodic T L n ν).time := by
  have h1 : signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T n.time hT]
  have h2 : signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) μ).time = -signedTime T (addVectorPeriodic T L n μ).time := by
    calc
      signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) μ).time
          = signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n μ)).time := by
        show signedTime T (AddVector.addVector (ReflectSite.reflectSite n) μ).time =
             signedTime T (ReflectSite.reflectSite (AddVector.addVector n μ)).time
        rw [reflectSite_addVector_comm T L n μ hμ0]
      _ = -signedTime T (addVectorPeriodic T L n μ).time := by
        simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T (addVectorPeriodic T L n μ).time hT]
  have h3 : signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite n) μ) ν).time =
      -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time := by
    calc
      signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite n) μ) ν).time
          = signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n μ)) ν).time := by
        show signedTime T (AddVector.addVector (AddVector.addVector (ReflectSite.reflectSite n) μ) ν).time =
             signedTime T (AddVector.addVector (ReflectSite.reflectSite (AddVector.addVector n μ)) ν).time
        rw [reflectSite_addVector_comm T L n μ hμ0]
      _ = signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν)).time := by
        show signedTime T (AddVector.addVector (ReflectSite.reflectSite (AddVector.addVector n μ)) ν).time =
             signedTime T (ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n μ) ν)).time
        rw [reflectSite_addVector_comm T L (AddVector.addVector n μ) ν hν0]
      _ = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time := by
        simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time hT]
  have h4 : signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) ν).time = -signedTime T (addVectorPeriodic T L n ν).time := by
    calc
      signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) ν).time
          = signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n ν)).time := by
        show signedTime T (AddVector.addVector (ReflectSite.reflectSite n) ν).time =
             signedTime T (ReflectSite.reflectSite (AddVector.addVector n ν)).time
        rw [reflectSite_addVector_comm T L n ν hν0]
      _ = -signedTime T (addVectorPeriodic T L n ν).time := by
        simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T (addVectorPeriodic T L n ν).time hT]
  exact ⟨h1, h2, h3, h4⟩

/-- Adding a spatial direction (μ ≠ 0) does not change the time coordinate of a
`PeriodicSite`; only the time direction `μ = 0` increments `time`. -/
lemma addVectorPeriodic_time_of_ne_zero (T L : ℕ) (n : PeriodicSite T L) (μ : Fin 4)
    (hμ0 : μ ≠ 0) : (addVectorPeriodic T L n μ).time = n.time := by
  fin_cases μ
  · exfalso; exact hμ0 rfl
  · simp [addVectorPeriodic]
  · simp [addVectorPeriodic]
  · simp [addVectorPeriodic]

/-- For time-spatial plaquettes (μ=0, ν≠0), the signed times at reflected corners
are the negations of the signed times at the original corners (with time shifts). -/
lemma signedTime_ts_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) (ν : Fin 4) (hν0 : ν ≠ 0) :
    signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -signedTime T (addVectorPeriodic T L n 0).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν).time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν) 0).time = -signedTime T (addVectorPeriodic T L n ν).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -signedTime T n.time := by
  -- Time of n + e_0
  have h_n0_time : (addVectorPeriodic T L n 0).time = n.time + 1 := by simp [addVectorPeriodic]
  -- Time of θ(n + e_0) = -(n.time + 1)
  have h_refl_time : (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -(n.time + 1 : ZMod T) := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, h_n0_time]
  -- Time of θ(n + e_0) + e_ν = -(n.time + 1) (spatial doesn't change time)
  have h_refl_ν_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time = -(n.time + 1 : ZMod T) := by
    have h_spatial : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time =
        (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time :=
      addVectorPeriodic_time_of_ne_zero T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν hν0
    rw [h_spatial, h_refl_time]
  -- Time of θ(n + e_0) + e_ν + e_0 = -(n.time + 1) + 1 = -n.time
  have h_refl_ν_0_time : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν) 0).time = (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_ν_time]
    ring
  -- Time of θ(n + e_0) + e_0 = -(n.time + 1) + 1 = -n.time
  have h_refl_0_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_time]
    ring
  -- Time of n + e_ν = n.time (spatial)
  have h_nν_time : (addVectorPeriodic T L n ν).time = n.time :=
    addVectorPeriodic_time_of_ne_zero T L n ν hν0
  -- Time of n + e_0 + e_ν = n.time + 1 (spatial doesn't change time)
  have h_n0ν_time : (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν).time = n.time + 1 := by
    have h_spatial : (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν).time =
        (addVectorPeriodic T L n 0).time :=
      addVectorPeriodic_time_of_ne_zero T L (addVectorPeriodic T L n 0) ν hν0
    rw [h_spatial, h_n0_time]
  -- Assemble the four conjuncts using signedTime_neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_refl_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_ν_time, h_n0ν_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_ν_0_time, h_nν_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_0_time]; exact signedTime_neg T n.time hT

-- Additional signed-time reflection lemmas for (μ≠0, ν=0) and (μ=0, ν=0) cases.

/-- For spatial-time plaquettes (μ≠0, ν=0), the signed times at reflected corners
are the negations of the signed times at the original corners. -/
lemma signedTime_st_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) (μ : Fin 4) (hμ0 : μ ≠ 0) :
    signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -signedTime T (addVectorPeriodic T L n 0).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -signedTime T n.time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ).time = -signedTime T (addVectorPeriodic T L n μ).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ).time = -signedTime T (addVectorPeriodic T L n 0).time := by
  -- Time of n + e_0
  have h_n0_time : (addVectorPeriodic T L n 0).time = n.time + 1 := by simp [addVectorPeriodic]
  -- Time of θ(n + e_0) = -(n.time + 1)
  have h_refl_time : (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -(n.time + 1 : ZMod T) := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, h_n0_time]
  -- Time of θ(n + e_0) + e_0 = -n.time
  have h_refl_0_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_time]
    ring
  -- Time of θ(n + e_0) + e_0 + e_μ = -n.time (spatial doesn't change time)
  have h_refl_0_μ_time : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ).time = -n.time := by
    have h_spatial : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ).time =
        (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time :=
      addVectorPeriodic_time_of_ne_zero T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ hμ0
    rw [h_spatial, h_refl_0_time]
  -- Time of θ(n + e_0) + e_μ = -(n.time + 1) (spatial doesn't change time)
  have h_refl_μ_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ).time = -(n.time + 1 : ZMod T) := by
    have h_spatial : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ).time =
        (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time :=
      addVectorPeriodic_time_of_ne_zero T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ hμ0
    rw [h_spatial, h_refl_time]
  -- Time of n + e_μ = n.time (spatial)
  have h_nμ_time : (addVectorPeriodic T L n μ).time = n.time :=
    addVectorPeriodic_time_of_ne_zero T L n μ hμ0
  -- Assemble
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_refl_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_0_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_0_μ_time, h_nμ_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_μ_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT

/-- For time-time plaquettes (μ=0, ν=0), the signed times at reflected corners
are the negations of the signed times at the original corners. -/
lemma signedTime_tt_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) :
    signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)).time = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = -signedTime T (addVectorPeriodic T L n 0).time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0).time = -signedTime T n.time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = -signedTime T (addVectorPeriodic T L n 0).time := by
  -- Time of n + e_0
  have h_n0_time : (addVectorPeriodic T L n 0).time = n.time + 1 := by simp [addVectorPeriodic]
  -- Time of n + 2e_0
  have h_n00_time : (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0).time = n.time + 2 := by
    have h_add0 : (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0).time = (addVectorPeriodic T L n 0).time + 1 := by simp [addVectorPeriodic]
    rw [h_add0, h_n0_time]
    ring
  -- Time of θ(n + 2e_0) = -(n.time + 2)
  have h_refl_time : (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)).time = -(n.time + 2 : ZMod T) := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, h_n00_time]
  -- Time of θ(n + 2e_0) + e_0 = -(n.time + 2) + 1 = -(n.time + 1)
  have h_refl_0_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = -(n.time + 1 : ZMod T) := by
    have h_add0 : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_time]
    ring
  -- Time of θ(n + 2e_0) + 2e_0 = -(n.time + 2) + 2 = -n.time
  have h_refl_00_time : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0).time = (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_0_time]
    ring
  -- Assemble
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_refl_time, h_n00_time]; exact signedTime_neg T (n.time + 2) hT
  · rw [h_refl_0_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_00_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_0_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT

end ConditionEquivalence

/-- Symmetric form of `trace_plaquetteProduct_reflect_ss`: the trace of the original
spatial plaquette equals the trace of the reflected plaquette (μ ≠ 0, ν ≠ 0). -/
lemma trace_plaquetteProduct_reflect_ss' (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite n) μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) :=
  (trace_plaquetteProduct_reflect_ss N T L U n μ ν hμ0 hν0).symm

set_option maxHeartbeats 1000000 in
/--
When all four corners of a plaquette have negative signed time, the trace of the
reflected plaquette (under the Osterwalder-Seiler bijection) equals the trace of
the original plaquette. This dispatches to the appropriate
`trace_plaquetteProduct_reflect_*` lemma based on the directions μ, ν.
-/
lemma trace_plaquetteProduct_neg_to_pos (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (h_neg : signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
             signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
             signedTime T (addVectorPeriodic T L n ν).time < 0) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (match μ, ν with
      | 0, 0 => ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)
      | 0, _ => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
      | _, 0 => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
      | _, _ => ReflectSite.reflectSite n)
      (match μ, ν with
      | 0, 0 => 0
      | 0, ν => ν
      | μ, 0 => 0
      | μ, ν => μ)
      (match μ, ν with
      | 0, 0 => 0
      | 0, ν => 0
      | μ, 0 => μ
      | μ, ν => ν)
    : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  -- The trace identity holds for every direction pair (μ, ν); the sign hypothesis
  -- `h_neg` only selects which plaquettes land in the negative-time sum, so it is
  -- irrelevant to the pointwise trace equality. We dispatch to the four already-proven
  -- `trace_plaquetteProduct_reflect_*` lemmas by case analysis on (μ, ν).  Explicit
  -- bullets (rather than `first`) keep each case to a single `defEq` check.
  obtain ⟨h1, h2, h3, h4⟩ := h_neg
  fin_cases μ <;> fin_cases ν
  · exact trace_plaquetteProduct_reflect_tt N T L U n
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide

set_option maxHeartbeats 1000000 in
/-- Reflection cancels a single forward time step: θ(θ(n+e₀)+e₀) = n. -/
lemma reflectSite_addVector0_inv (T L : ℕ) [NeZero T] (n : PeriodicSite T L) :
    ReflectSite.reflectSite (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) = n := by
  ext <;> simp [ReflectSite.reflectSite, reflectSitePeriodic, addVectorPeriodic]

set_option maxHeartbeats 1000000 in
/-- Reflection cancels two forward time steps: θ(θ(n+2e₀)+2e₀) = n. -/
lemma reflectSite_addVector00_inv (T L : ℕ) [NeZero T] (n : PeriodicSite T L) :
    ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L
      (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0) = n := by
  ext <;> simp [ReflectSite.reflectSite, reflectSitePeriodic, addVectorPeriodic]

/-- The Osterwalder-Seiler reflection of a plaquette index (n, μ, ν) maps it to the
reflected plaquette (n', μ', ν') whose trace equals the original (by
`trace_plaquetteProduct_neg_to_pos`). -/
def reflectPlaquetteIndex (T L : ℕ) [NeZero T] : PlaquetteIndex T L → PlaquetteIndex T L
  | (n, 0, 0) => (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0), 0, 0)
  | (n, 0, ν) => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), ν, 0)
  | (n, μ, 0) => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), 0, μ)
  | (n, μ, ν) => (ReflectSite.reflectSite n, μ, ν)

/-- `reflectPlaquetteIndex` is involutive, hence a bijection on plaquette indices. -/
lemma reflectPlaquetteIndex_involution (T L : ℕ) [NeZero T] (p : PlaquetteIndex T L) :
    reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p := by
  rcases p with ⟨n, μ, ν⟩
  fin_cases μ <;> fin_cases ν <;>
    simp [reflectPlaquetteIndex, reflectSite_addVector0_inv, reflectSite_addVector00_inv,
      ReflectSite.involution]

/-- The Osterwalder-Seiler plaquette reflection as an equivalence (involution → bijection). -/
def reflectPlaquetteIndexEquiv (T L : ℕ) [NeZero T] : PlaquetteIndex T L ≃ PlaquetteIndex T L where
  toFun := reflectPlaquetteIndex T L
  invFun := reflectPlaquetteIndex T L
  left_inv := reflectPlaquetteIndex_involution T L
  right_inv := reflectPlaquetteIndex_involution T L

/-- A plaquette index is "negative" if all four corners have strictly negative signed time. -/
abbrev plaquetteNegative (T L : ℕ) (p : PlaquetteIndex T L) : Prop :=
  signedTime T p.1.time < 0 ∧ signedTime T (addVectorPeriodic T L p.1 p.2.1).time < 0 ∧
  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L p.1 p.2.1) p.2.2).time < 0 ∧
  signedTime T (addVectorPeriodic T L p.1 p.2.2).time < 0

/-- A plaquette index is "positive" if all four corners have strictly positive signed time. -/
abbrev plaquettePositive (T L : ℕ) (p : PlaquetteIndex T L) : Prop :=
  signedTime T p.1.time > 0 ∧ signedTime T (addVectorPeriodic T L p.1 p.2.1).time > 0 ∧
  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L p.1 p.2.1) p.2.2).time > 0 ∧
  signedTime T (addVectorPeriodic T L p.1 p.2.2).time > 0

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (0,0) case. -/
lemma signedTime_tt_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L) :
    plaquettePositive T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0), 0, 0) ↔
    plaquetteNegative T L (n, 0, 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_tt_reflect T L hT n
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (0,ν) case. -/
lemma signedTime_ts_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L)
    (ν : Fin 4) (hν0 : ν ≠ 0) :
    plaquettePositive T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0), ν, 0) ↔
    plaquetteNegative T L (n, 0, ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_ts_reflect T L hT n ν hν0
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (μ,0) case. -/
lemma signedTime_st_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L)
    (μ : Fin 4) (hμ0 : μ ≠ 0) :
    plaquettePositive T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0), 0, μ) ↔
    plaquetteNegative T L (n, μ, 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_st_reflect T L hT n μ hμ0
  -- n+e_μ+e₀ and n+e₀ have the same time coordinate (e_μ is spatial), so their
  -- signed times are equal.  Omega needs this to close the iff.
  have h_same : signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) 0).time =
      signedTime T (addVectorPeriodic T L n 0).time := by
    have h1 : (addVectorPeriodic T L (addVectorPeriodic T L n μ) 0).time =
        (addVectorPeriodic T L n μ).time + 1 := rfl
    have h2 : (addVectorPeriodic T L n 0).time = n.time + 1 := rfl
    rw [h1, addVectorPeriodic_time_of_ne_zero T L n μ hμ0, h2]
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (μ,ν) case. -/
lemma signedTime_ss_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L)
    (μ ν : Fin 4) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    plaquettePositive T L (ReflectSite.reflectSite n, μ, ν) ↔
    plaquetteNegative T L (n, μ, ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_ss_reflect T L hT n μ ν hμ0 hν0
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa. -/
lemma reflectPlaquetteIndex_sign (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (p : PlaquetteIndex T L) :
    plaquettePositive T L (reflectPlaquetteIndex T L p) ↔ plaquetteNegative T L p := by
  rcases p with ⟨n, μ, ν⟩
  fin_cases μ <;> fin_cases ν <;> simp only [reflectPlaquetteIndex] <;> first
    | exact signedTime_tt_sign_iff T L hT n
    | (apply signedTime_ts_sign_iff T L hT n _; decide)
    | (apply signedTime_st_sign_iff T L hT n _; decide)
    | (apply signedTime_ss_sign_iff T L hT n _ _; all_goals decide)

/-- `reflectPlaquetteIndex` first component expanded as a match expression. -/
lemma reflectPlaquetteIndex_fst (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (reflectPlaquetteIndex T L (n, μ, ν)).1 =
    (match μ, ν with
    | 0, 0 => ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)
    | 0, _ => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
    | _, 0 => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
    | _, _ => ReflectSite.reflectSite n) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- `reflectPlaquetteIndex` second component (μ') expanded as a match expression. -/
lemma reflectPlaquetteIndex_snd_fst (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (reflectPlaquetteIndex T L (n, μ, ν)).2.1 =
    (match μ, ν with
    | 0, 0 => 0
    | 0, ν => ν
    | μ, 0 => 0
    | μ, ν => μ) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- `reflectPlaquetteIndex` third component (ν') expanded as a match expression. -/
lemma reflectPlaquetteIndex_snd_snd (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (reflectPlaquetteIndex T L (n, μ, ν)).2.2 =
    (match μ, ν with
    | 0, 0 => 0
    | 0, ν => 0
    | μ, 0 => μ
    | μ, ν => ν) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- `reflectPlaquetteIndex` expanded as a match expression (for rewriting). -/
lemma reflectPlaquetteIndex_eq (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    reflectPlaquetteIndex T L (n, μ, ν) =
    (match μ, ν with
    | 0, 0 => (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0), 0, 0)
    | 0, ν => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), ν, 0)
    | μ, 0 => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), 0, μ)
    | μ, ν => (ReflectSite.reflectSite n, μ, ν)) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- Congruence: equal traces give equal plaquette contributions. -/
lemma plaquetteContribution_congr (N : ℕ) (β : ℝ) (A B : ℝ) (h : A = B) :
    β * ((1 : ℝ) - (1 / (N : ℝ)) * A) = β * ((1 : ℝ) - (1 / (N : ℝ)) * B) := by rw [h]

set_option maxHeartbeats 1000000 in
/-- Variant of `trace_plaquetteProduct_neg_to_pos` whose RHS is expressed via
`reflectPlaquetteIndex` (rather than an explicit `match`), so it composes cleanly with
`plaquetteContribution`. -/
lemma trace_plaquetteProduct_neg_to_pos' (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (h_neg : plaquetteNegative T L (n, μ, ν)) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L (n, μ, ν)).1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.2
    : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h_neg
  fin_cases μ <;> fin_cases ν
  · exact trace_plaquetteProduct_reflect_tt N T L U n
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide

set_option maxHeartbeats 4000000 in
/-- Under the negative-time hypothesis, the plaquette contribution is preserved by the
Osterwalder-Seiler reflection (the reflected trace equals the original trace). -/
lemma plaquetteContribution_reflect_eq (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : PlaquetteIndex T L)
    (h : plaquetteNegative T L p) :
    plaquetteContribution N β U p.1 p.2.1 p.2.2 =
    plaquetteContribution N β (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
      (reflectPlaquetteIndex T L p).2.2 := by
  rcases p with ⟨n, μ, ν⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  -- Reduce the tuple projections on the LHS to `n μ ν` (definitional).
  show plaquetteContribution N β U n μ ν =
    plaquetteContribution N β (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L (n, μ, ν)).1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.2
  unfold plaquetteContribution
  rw [trace_plaquetteProduct_neg_to_pos' N T L U n μ ν ⟨h1, h2, h3, h4⟩]

set_option maxHeartbeats 8000000 in
lemma trace_plaquetteProduct_reflect_all (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L (n, μ, ν)).1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.2 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  -- The equality holds for every direction pair (μ, ν) by the specific trace lemmas.
  -- We dispatch by cases on μ and ν.
  fin_cases μ <;> fin_cases ν
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_tt N T L U n
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ts N T L U n 1 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ts N T L U n 2 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ts N T L U n 3 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_st N T L U n 1 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 1 1 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 1 2 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 1 3 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_st N T L U n 2 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 2 1 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 2 2 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 2 3 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_st N T L U n 3 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 3 1 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 3 2 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 3 3 (by decide) (by decide)
set_option maxHeartbeats 4000000 in
/-- Unconditional version: `plaquetteContribution_reflect_eq` without the `plaquetteNegative`
hypothesis.  The trace equality holds for any plaquette index `p`. -/
lemma plaquetteContribution_reflect_eq_all (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : PlaquetteIndex T L) :
    plaquetteContribution N β U p.1 p.2.1 p.2.2 =
    plaquetteContribution N β (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
      (reflectPlaquetteIndex T L p).2.2 := by
  rcases p with ⟨n, μ, ν⟩
  unfold plaquetteContribution
  rw [trace_plaquetteProduct_reflect_all N T L U n μ ν]

set_option maxHeartbeats 1000000 in
lemma neg_action_reflection_os_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSNegative N T L β U =
    wilsonActionOSPositive N T L β (reflectLinkVariable N U) := by
  have h_neg_sum : wilsonActionOSNegative N T L β U = ∑ p : PlaquetteIndex T L,
      (if plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSNegative
    simp [PlaquetteIndex, plaquetteNegative, Fintype.sum_prod_type]
  have h_pos_sum : wilsonActionOSPositive N T L β (reflectLinkVariable N U) = ∑ p : PlaquetteIndex T L,
      (if plaquettePositive T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSPositive
    simp [PlaquetteIndex, plaquettePositive, Fintype.sum_prod_type]
  rw [h_neg_sum, h_pos_sum]
  let f : PlaquetteIndex T L → ℝ := λ p =>
    (if plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0)
  let g : PlaquetteIndex T L → ℝ := λ p =>
    (if plaquettePositive T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0)
  let e : PlaquetteIndex T L ≃ PlaquetteIndex T L := reflectPlaquetteIndexEquiv T L
  have h_eq (p : PlaquetteIndex T L) : f (e p) = g p := by
    have h_e_val : e p = reflectPlaquetteIndex T L p := rfl
    rw [h_e_val]
    have h_neg_iff_pos : plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔ plaquettePositive T L p := by
      have h := reflectPlaquetteIndex_sign T L hT (reflectPlaquetteIndex T L p)
      have h_inv : reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p :=
        reflectPlaquetteIndex_involution T L p
      simpa [h_inv] using h.symm
    by_cases h : plaquettePositive T L p
    · have h_neg : plaquetteNegative T L (reflectPlaquetteIndex T L p) := (h_neg_iff_pos.mpr h)
      have h_contrib : plaquetteContribution N β U (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
          (reflectPlaquetteIndex T L p).2.2 = plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 := by
        simpa [reflectPlaquetteIndex_involution T L p] using
          plaquetteContribution_reflect_eq_all N T L β U (reflectPlaquetteIndex T L p)
      dsimp [f, g]
      rw [if_pos h_neg, if_pos h, h_contrib]
    · have h_not_neg : ¬ plaquetteNegative T L (reflectPlaquetteIndex T L p) := mt h_neg_iff_pos.mp h
      dsimp [f, g]
      rw [if_neg h_not_neg, if_neg h]
  calc
    ∑ p : PlaquetteIndex T L, f p = ∑ p : PlaquetteIndex T L, f (e p) := by
      symm
      exact Fintype.sum_equiv e (λ p => f (e p)) f (λ p => rfl)
    _ = ∑ p : PlaquetteIndex T L, g p := by
      refine Finset.sum_congr rfl (λ p hp => ?_)
      rw [h_eq p]

set_option maxHeartbeats 1000000 in
lemma interface_action_reflection_symmetric_os_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSInterface N T L β (reflectLinkVariable N U) =
    wilsonActionOSInterface N T L β U := by
  have h_sum_eq : wilsonActionOSInterface N T L β U = ∑ p : PlaquetteIndex T L,
      (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSInterface
    simp [PlaquetteIndex, plaquettePositive, plaquetteNegative, Fintype.sum_prod_type]
  have h_sum_eq_reflect : wilsonActionOSInterface N T L β (reflectLinkVariable N U) = ∑ p : PlaquetteIndex T L,
      (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSInterface
    simp [PlaquetteIndex, plaquettePositive, plaquetteNegative, Fintype.sum_prod_type]
  rw [h_sum_eq_reflect, h_sum_eq]
  let f : PlaquetteIndex T L → ℝ := λ p =>
    (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0)
  let g : PlaquetteIndex T L → ℝ := λ p =>
    (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0)
  let e : PlaquetteIndex T L ≃ PlaquetteIndex T L := reflectPlaquetteIndexEquiv T L
  have h_interface_inv (p : PlaquetteIndex T L) : 
      (¬ plaquettePositive T L (reflectPlaquetteIndex T L p) ∧ ¬ plaquetteNegative T L (reflectPlaquetteIndex T L p)) ↔
      (¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p) := by
    have h1 := reflectPlaquetteIndex_sign T L hT p
    have h2 : plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔ plaquettePositive T L p := by
      have h_inv : reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p :=
        reflectPlaquetteIndex_involution T L p
      have h' := reflectPlaquetteIndex_sign T L hT (reflectPlaquetteIndex T L p)
      simpa [h_inv] using h'.symm
    constructor
    · rintro ⟨hnpos, hnneg⟩
      constructor
      · exact mt h2.symm.mp hnneg
      · exact mt h1.symm.mp hnpos
    · rintro ⟨hnpos, hnneg⟩
      constructor
      · exact mt h1.mp hnneg
      · exact mt h2.mp hnpos
  have h_eq (p : PlaquetteIndex T L) : f (e p) = g p := by
    have h_e_val : e p = reflectPlaquetteIndex T L p := rfl
    rw [h_e_val]
    have h_cond : ¬ plaquettePositive T L (reflectPlaquetteIndex T L p) ∧ ¬ plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔
      ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p := h_interface_inv p
    dsimp [f, g]
    by_cases hi : (¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p)
    · rw [if_pos hi, if_pos ((h_interface_inv p).mpr hi)]
      rw [← plaquetteContribution_reflect_eq_all N T L β U p]
    · rw [if_neg hi, if_neg (mt (h_interface_inv p).mp hi)]
  calc
    ∑ p : PlaquetteIndex T L, f p = ∑ p : PlaquetteIndex T L, f (e p) := by
      symm
      exact Fintype.sum_equiv e (λ p => f (e p)) f (λ p => rfl)
    _ = ∑ p : PlaquetteIndex T L, g p := by
      refine Finset.sum_congr rfl (λ p hp => ?_)
      rw [h_eq p]
/-- The Osterwalder-Seiler "G" function: the Boltzmann factor for the positive
half-lattice, including the interface action at half weight.  This is the
function whose integral `∫ G(U)·G(θU) dμ₀` must be shown non-negative. -/
noncomputable def osG (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  f U * Real.exp (-β * wilsonActionOSPositive N T L β U) *
  Real.exp (-β * wilsonActionOSInterface N T L β U / 2)

/-- **Axiom (Transfer-matrix positivity).**

For `f` depending only on positive-time and interface links, the integral
`∫ G(U)·G(θU) dμ₀ ≥ 0`, where `G = osG` is the Osterwalder-Seiler Boltzmann
factor and `θ` is the time-reflection.

This is the positivity of the transfer matrix `T` constructed from the
plaquette Boltzmann factor.  The mathematical justification is:

1. The plaquette Boltzmann factor `exp(c·Re Tr(g₁g₂g₃g₄))` is a
   positive-definite function on `SU(N)⁴` — this is proved (from the
   Peter-Weyl / Clebsch-Gordan axiom) in `PeterWeyl.lean` as
   `plaquetteBoltzmannPD`.
2. Positive-definiteness of the plaquette factor implies that the transfer
   matrix `T` (which integrates out the negative-time links with the
   reflection kernel) is a positive operator on `L²(SU(N)^{interface})`.
3. The identity `∫ G(U)·G(θU) dμ₀ = ∫ g(u)·(Tg)(u) dμ⁺⁰` (proved in
   `TransferMatrix.lean` as `integral_G_thetaG_eq_inner_g_Tg`) then gives
   `∫ G·G(θU) ≥ 0` from the positivity of `T`.

Steps 2–3 require the full transfer-matrix construction (measure-theoretic
factorization of the product Haar measure, Fubini, and the character-expansion
argument).  The positive-definiteness of the plaquette factor (step 1) is the
key input and is proved in `PeterWeyl.lean`; the remaining measure theory is
axiomatized here.  See `docs/found_issues.md` §3 and `docs/gap_analysis.md`. -/
axiom transferMatrixPositivity_axiom (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf_supported : dependsOnlyOnPosInterface N T L f) :
    0 ≤ ∫ (cfg : FiniteLinkConfig N (PeriodicSite T L)
        (Finset.univ : Finset (PeriodicSite T L))),
      osG N T L β f
        (extendLinkVariable N (PeriodicSite T L)
          (Finset.univ : Finset (PeriodicSite T L)) cfg) *
      osG N T L β f
        (reflectLinkVariable N
          (extendLinkVariable N (PeriodicSite T L)
            (Finset.univ : Finset (PeriodicSite T L)) cfg))
      ∂ productHaarMeasure N (PeriodicSite T L)
        (Finset.univ : Finset (PeriodicSite T L))

lemma gibbsExpectationPeriodic_reflection_positive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf_supported : dependsOnlyOnPosInterface N T L f) :
    0 ≤ gibbsExpectation N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
      (λ U => f U * reflectObservable N f U) := by
  dsimp [gibbsExpectation]
  have hZ_pos : partitionFunctionFinite N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) > 0 :=
    partitionFunctionFinite_pos N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
  refine div_nonneg ?_ (le_of_lt hZ_pos)
  set μ₀ := productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) with hμ₀
  set S_total := wilsonActionFiniteConfig N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) with hS
  set U_ext := extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) with hU
  have h_total_decomp : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      S_total cfg = wilsonActionOSPositive N T L β (U_ext cfg) +
        wilsonActionOSNegative N T L β (U_ext cfg) +
        wilsonActionOSInterface N T L β (U_ext cfg) := by
    intro cfg
    calc
      S_total cfg = wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) (U_ext cfg) := rfl
      _ = wilsonActionOSPositive N T L β (U_ext cfg) +
          wilsonActionOSNegative N T L β (U_ext cfg) +
          wilsonActionOSInterface N T L β (U_ext cfg) :=
        total_decomposition_os_periodic N T L β (U_ext cfg)
  have h_neg_reflect : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      wilsonActionOSNegative N T L β (U_ext cfg) =
      wilsonActionOSPositive N T L β (reflectLinkVariable N (U_ext cfg)) := by
    intro cfg
    exact neg_action_reflection_os_periodic N T L β hT (U_ext cfg)
  have h_int_reflect : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      wilsonActionOSInterface N T L β (reflectLinkVariable N (U_ext cfg)) =
      wilsonActionOSInterface N T L β (U_ext cfg) := by
    intro cfg
    exact interface_action_reflection_symmetric_os_periodic N T L β hT (U_ext cfg)
  have h_factorization : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      Real.exp (-β * S_total cfg) = 
      (Real.exp (-β * wilsonActionOSPositive N T L β (U_ext cfg)) *
        Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2)) *
      (Real.exp (-β * wilsonActionOSPositive N T L β (reflectLinkVariable N (U_ext cfg))) *
        Real.exp (-β * wilsonActionOSInterface N T L β (reflectLinkVariable N (U_ext cfg)) / 2)) := by
    intro cfg
    rw [h_total_decomp cfg]
    have h_mul : -β * (wilsonActionOSPositive N T L β (U_ext cfg) + wilsonActionOSNegative N T L β (U_ext cfg) +
      wilsonActionOSInterface N T L β (U_ext cfg)) = 
      (-β * wilsonActionOSPositive N T L β (U_ext cfg)) + 
      (-β * wilsonActionOSNegative N T L β (U_ext cfg)) + 
      (-β * wilsonActionOSInterface N T L β (U_ext cfg)) := by ring
    rw [h_mul]
    rw [Real.exp_add, Real.exp_add]
    rw [h_neg_reflect cfg, h_int_reflect cfg]
    have h_exp_split : Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg)) =
      Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) *
      Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) := by
      calc
        Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg)) =
          Real.exp ((-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) +
                   (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2)) := by ring
        _ = Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) *
            Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) := by rw [Real.exp_add]
    rw [h_exp_split]
    ring
  set G := osG N T L β f with hG
  have h_integrand_eq : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      f (U_ext cfg) * f (reflectLinkVariable N (U_ext cfg)) *
      Real.exp (-β * S_total cfg) =
      G (U_ext cfg) * G (reflectLinkVariable N (U_ext cfg)) := by
    intro cfg
    dsimp [G, osG]
    rw [h_factorization cfg]
    ring
  have h_fun_eq : (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
      f (U_ext cfg) * f (reflectLinkVariable N (U_ext cfg)) * Real.exp (-β * S_total cfg)) =
    (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
      G (U_ext cfg) * G (reflectLinkVariable N (U_ext cfg))) := by
    ext cfg; exact h_integrand_eq cfg
  calc
    (∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      f (U_ext cfg) * f (reflectLinkVariable N (U_ext cfg)) * Real.exp (-β * S_total cfg) ∂ μ₀)
        = (∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      G (U_ext cfg) * G (reflectLinkVariable N (U_ext cfg)) ∂ μ₀) := by
      rw [h_fun_eq]
    _ ≥ 0 := by
      -- GOAL: Prove that ∫ G(U)·G(θU) dμ₀(U) ≥ 0.
      -- The positivity follows from `transferMatrixPositivity_axiom`, which is
      -- justified by `plaquetteBoltzmannPD` (Peter-Weyl / Clebsch-Gordan) ⟹
      -- transfer matrix T positive ⟹ ∫ G·G(θU) ≥ 0.  See the axiom's docstring.
      exact transferMatrixPositivity_axiom N T L β hT f hf_supported
structure PeriodicExpectation (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T) : Type 1 where
  /-- The partition function Z = ∫ exp(-S_W) dU. -/
  partitionFunction : ℝ
  /-- Positivity of the partition function: Z > 0 for β > 0. -/
  partitionFunctionPos : partitionFunction > 0
  /-- The expectation of an observable F. -/
  evaluate : (LinkVariable (SU N) (PeriodicSite T L) → ℝ) → ℝ
  /-- Linearity of expectation. -/
  linearity : ∀ (a b : ℝ) (F G : LinkVariable (SU N) (PeriodicSite T L) → ℝ),
    (MeasureTheory.Integrable (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
      F (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg) *
      Real.exp (-β * wilsonActionFiniteConfig N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg))
      (productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)))) →
    (MeasureTheory.Integrable (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
      G (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg) *
      Real.exp (-β * wilsonActionFiniteConfig N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg))
      (productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)))) →
    evaluate (λ U => a * F U + b * G U) = a * evaluate F + b * evaluate G
  /-- Normalization: ⟨1⟩ = 1. -/
  normalization : evaluate (λ _ => 1) = 1
  /-- Positivity: if F ≥ 0 pointwise, then evaluate F ≥ 0. -/
  positivity : ∀ (F : LinkVariable (SU N) (PeriodicSite T L) → ℝ),
    (∀ U, F U ≥ 0) → evaluate F ≥ 0
  /-- Reflection positivity: if f depends only on positive+interface links, then ⟨f · θ(f)⟩ ≥ 0. -/
  reflectionPositive : ∀ (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ),
    dependsOnlyOnPosInterface N T L f →
    evaluate (λ U => f U * reflectObservable N f U) ≥ 0
/--
Construct a `PeriodicExpectation` for the Wilson action on a finite periodic lattice.
This uses the Osterwalder-Seiler factorization to prove reflection positivity without
the `hadd` limitation of the Z4Site version.
-/
noncomputable def wilsonPeriodicExpectation (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T) :
    PeriodicExpectation N T L β hT :=
  {
    partitionFunction := partitionFunctionFinite N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
    partitionFunctionPos := partitionFunctionFinite_pos N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
    evaluate := gibbsExpectation N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
    linearity := λ a b F G hF hG =>
      gibbsExpectation_linear N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) a b F G hF hG
    normalization := gibbsExpectation_normalization N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
    positivity := λ F hF => gibbsExpectation_pos N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) F hF
    reflectionPositive := λ f hf_supported =>
      gibbsExpectationPeriodic_reflection_positive N T L β hT f hf_supported
  }
/--
The SU(N) lattice Yang-Mills measure with the Wilson action on a finite periodic lattice
is reflection positive for observables that depend only on links in the positive-time
and interface (time-0) regions.  This is the content of the Osterwalder-Seiler theorem.
-/
theorem lattice_ym_reflection_positive_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hβ : β > 0) (hT : Odd T) :
    ∀ (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ),
      dependsOnlyOnPosInterface N T L f →
      (wilsonPeriodicExpectation N T L β hT).evaluate (λ U => f U * reflectObservable N f U) ≥ 0 := by
  intro f hf_supported
  exact (wilsonPeriodicExpectation N T L β hT).reflectionPositive f hf_supported

end PeriodicSite
