/-
# Reflection Positivity: Periodic Lattice
-/

import YangMills.Lattice
import YangMills.SpecialUnitary
import YangMills.Proofs.LatticeMeasure
import YangMills.Proofs.BasicLemmas
import YangMills.Proofs.PeterWeyl
import YangMills.Proofs.BoltzmannFactor
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

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

/-- The signed time of a reflected site is the negation of the original. -/
lemma signedTime_reflectSite {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    (n : PeriodicSite T L) :
    signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time := by
  simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T n.time hT]

/-- Reflection maps positive-time sites to negative-time sites. -/
lemma reflectSite_mem_negative_of_positive {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ positiveSites T L) :
    ReflectSite.reflectSite n ∈ negativeSites T L := by
  have h_signed : signedTime T n.time > 0 := by
    simpa [positiveSites, Finset.mem_filter] using hn
  have h_neg_signed : signedTime T (ReflectSite.reflectSite n).time < 0 := by
    rw [signedTime_reflectSite hT n]; linarith
  simpa [negativeSites, Finset.mem_filter] using h_neg_signed

/-- Reflection maps interface sites to interface sites. -/
lemma reflectSite_mem_interface_of_interface {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ interfaceSites T L) :
    ReflectSite.reflectSite n ∈ interfaceSites T L := by
  have h_signed : signedTime T n.time = 0 := by
    simpa [interfaceSites, Finset.mem_filter] using hn
  have h_int_signed : signedTime T (ReflectSite.reflectSite n).time = 0 := by
    rw [signedTime_reflectSite hT n, h_signed]; simp
  simpa [interfaceSites, Finset.mem_filter] using h_int_signed

/-- For an interface site (signedTime = 0), the reflection FIXES the site: θ n = n.
This is because `signedTime T t = 0` implies `t = 0` in `ZMod T` (for odd T), and
`reflectSitePeriodic n = { n with time := -n.time }` fixes `n` when `n.time = 0`.
This is the key fact underlying the σ-disappears-from-g lemma (§8.11.37): σ only
inverts temporal interface links and keeps spatial interface links fixed because
`reflectSite n = n` for interface sites. -/
lemma reflectSite_interface_self {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ interfaceSites T L) :
    ReflectSite.reflectSite n = n := by
  have h_signed : signedTime T n.time = 0 := by
    simpa [interfaceSites, Finset.mem_filter] using hn
  -- signedTime T t = 0 implies t = 0 in ZMod T
  have h_time_zero : n.time = 0 := by
    unfold signedTime at h_signed
    split_ifs at h_signed with h
    · -- t.val ≤ (T-1)/2, signedTime = (t.val : ℤ) = 0, so t.val = 0, so t = 0
      have hval : (n.time.val : ℤ) = 0 := by exact_mod_cast h_signed
      have hval_nat : n.time.val = 0 := by exact_mod_cast hval
      exact (ZMod.val_eq_zero n.time).mp hval_nat
    · -- t.val > (T-1)/2, signedTime = (t.val : ℤ) - (T : ℤ) = 0, so t.val = T
      -- but t.val < T, contradiction
      have hval : (n.time.val : ℤ) = (T : ℤ) := by linarith
      have hval_lt : n.time.val < T := ZMod.val_lt n.time
      have : (n.time.val : ℤ) < (T : ℤ) := by exact_mod_cast hval_lt
      linarith
  -- reflectSitePeriodic n = { n with time := -n.time } = { n with time := 0 } = n
  simp only [ReflectSite.reflectSite, reflectSitePeriodic]
  ext <;> simp [h_time_zero]

/-- Reflection does not map interface sites to positive sites. -/
lemma reflectSite_not_mem_positive_of_interface {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ interfaceSites T L) :
    ReflectSite.reflectSite n ∉ positiveSites T L := by
  have h_reflect_int := reflectSite_mem_interface_of_interface hT hn
  have h_disjoint : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]
    intro m hm hpos hint; linarith
  exact Finset.disjoint_right.mp h_disjoint h_reflect_int

/-- Reflection does not map interface sites to negative sites. -/
lemma reflectSite_not_mem_negative_of_interface {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ interfaceSites T L) :
    ReflectSite.reflectSite n ∉ negativeSites T L := by
  have h_reflect_int := reflectSite_mem_interface_of_interface hT hn
  have h_disjoint : Disjoint (negativeSites T L) (interfaceSites T L) := by
    unfold negativeSites interfaceSites
    rw [Finset.disjoint_filter]
    intro m hm hneg hint; linarith
  exact Finset.disjoint_right.mp h_disjoint h_reflect_int

/-- Reflection does not map positive sites to positive sites. -/
lemma reflectSite_not_mem_positive_of_positive {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ positiveSites T L) :
    ReflectSite.reflectSite n ∉ positiveSites T L := by
  have h_reflect_neg := reflectSite_mem_negative_of_positive hT hn
  have h_disjoint : Disjoint (positiveSites T L) (negativeSites T L) := by
    unfold positiveSites negativeSites
    rw [Finset.disjoint_filter]
    intro m hm hpos hneg; linarith
  exact Finset.disjoint_right.mp h_disjoint h_reflect_neg

/-- Reflection maps negative-time sites to positive-time sites. -/
lemma reflectSite_mem_positive_of_negative {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ negativeSites T L) :
    ReflectSite.reflectSite n ∈ positiveSites T L := by
  have h_signed : signedTime T n.time < 0 := by
    simpa [negativeSites, Finset.mem_filter] using hn
  have h_pos_signed : signedTime T (ReflectSite.reflectSite n).time > 0 := by
    rw [signedTime_reflectSite hT n]; linarith
  simpa [positiveSites, Finset.mem_filter] using h_pos_signed

/-- Reflection does not map negative sites to negative sites. -/
lemma reflectSite_not_mem_negative_of_negative {T L : ℕ} [NeZero T] [NeZero L] (hT : Odd T)
    {n : PeriodicSite T L} (hn : n ∈ negativeSites T L) :
    ReflectSite.reflectSite n ∉ negativeSites T L := by
  have h_reflect_pos := reflectSite_mem_positive_of_negative hT hn
  have h_disjoint : Disjoint (positiveSites T L) (negativeSites T L) := by
    unfold positiveSites negativeSites
    rw [Finset.disjoint_filter]
    intro m hm hpos hneg; linarith
  exact Finset.disjoint_left.mp h_disjoint h_reflect_pos

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

/-- Stronger version of `dependsOnlyOnPosInterface` that also excludes temporal
interface links (direction `μ = 0` at interface sites).

This is the correct hypothesis for the Osterwalder-Seiler reflection positivity
theorem.  The weaker `dependsOnlyOnPosInterface` (which allows `f` to depend on
temporal interface links) is **insufficient**: for `β = 0` (free theory), taking
`f(g) = Im Tr(g)` for a single temporal interface link `g` gives
`∫ f(g)·f(g⁻¹) dg = -∫ (Im Tr(g))² dg < 0`, a strictly negative integral.
The temporal-link inversion `σ` (which inverts `μ = 0` links at the interface)
is the sole obstacle; restricting `f` to spatial interface links removes it.

See `docs/transfer_matrix_positivity_design.md` §8.11.36 for the full analysis. -/
def dependsOnlyOnPosSpatialInterface (N T L : ℕ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) : Prop :=
  ∀ (U V : LinkVariable (SU N) (PeriodicSite T L)),
    (∀ (n : PeriodicSite T L) (μ : Fin 4),
      n ∈ positiveSites T L ∨ (n ∈ interfaceSites T L ∧ μ ≠ (0 : Fin 4)) →
      U.value n μ = V.value n μ) → f U = f V

/-- `dependsOnlyOnPosSpatialInterface` is stronger than `dependsOnlyOnPosInterface`:
if `f` ignores temporal interface links, it certainly ignores all links outside
the positive+interface region. -/
lemma dependsOnlyOnPosSpatialInterface.dependsOnlyOnPosInterface
    (N T L : ℕ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f) :
    dependsOnlyOnPosInterface N T L f := by
  intro U V hUV
  apply hf
  intro n μ hn
  rcases hn with hpos | ⟨hint, hμ⟩
  · exact hUV n μ (Finset.mem_union_left _ hpos)
  · exact hUV n μ (Finset.mem_union_right _ hint)

/-- **Strongest support condition**: `f` depends only on strictly positive-time links
(sites with `signedTime > 0`), NOT on any interface links (sites with `signedTime = 0`).

This is the standard Osterwalder-Schrader OS3 hypothesis: test functions `f` are
supported in positive time `t > 0`.  It is stronger than `dependsOnlyOnPosSpatialInterface`
(which allows `f` to depend on spatial interface links at `t = 0`).

The §8.11.60 analysis showed that the §8.11.58 obstruction (the interface kernel
`K_{u⁰}` is NOT PD for each `u⁰` because character expansion coefficients `Ψ_w(u⁰)`
are complex) SURVIVES the change of variables for `dependsOnlyOnPosSpatialInterface`.
The §8.11.61 analysis identified that the correct proof mechanism requires:

1. **`dependsOnlyOnPositive`** (not the weaker `dependsOnlyOnPosSpatialInterface`):
   so that the interface-link integral gives `δ_{w, trivial}` (unweighted character
   orthogonality) rather than a weighted integral `∫ f(u⁰_s)²·Ψ_w(u⁰_s) dμ⁰_s` that
   can be negative.

2. **The FULL character expansion** (all plaquettes, not just interface ones):
   the interface-only expansion gives a "twisted" quadratic form `Σ F(w)·A_w²` that
   is NOT obviously non-negative (since `A_w` is complex and `Re(A_w²)` can be
   negative).  The full expansion (bulk + interface) gives `Σ F_full(w)·|Â_w|² ≥ 0`,
   a standard sum of squared Fourier coefficients with non-negative weights.

See `docs/transfer_matrix_positivity_design.md` §8.11.61 for the full analysis. -/
def dependsOnlyOnPositive (N T L : ℕ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) : Prop :=
  ∀ (U V : LinkVariable (SU N) (PeriodicSite T L)),
    (∀ (n : PeriodicSite T L) (μ : Fin 4),
      n ∈ positiveSites T L → U.value n μ = V.value n μ) → f U = f V

/-- `dependsOnlyOnPositive` is stronger than `dependsOnlyOnPosSpatialInterface`:
if `f` depends only on positive-time links (ignoring ALL interface links), then
in particular it ignores temporal interface links. -/
lemma dependsOnlyOnPositive.dependsOnlyOnPosSpatialInterface
    (N T L : ℕ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPositive N T L f) :
    dependsOnlyOnPosSpatialInterface N T L f := by
  intro U V hUV
  apply hf
  intro n μ hn
  exact hUV n μ (Or.inl hn)

