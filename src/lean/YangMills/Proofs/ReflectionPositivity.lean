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
import YangMills.Proofs.BoltzmannFactor
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

/-! ### Concrete-to-abstract plaquette-product bridge

These lemmas connect the *concrete* Wilson action (with its specific sign
convention `S_p = β(1 - (1/N) Re Tr(U_∂p))`) to the *abstract* plaquette-product
form `∏_p exp(c · Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` with `c ≥ 0` that the
`interface_kernel_character_expansion` lemma (in `PeterWeyl.lean`) operates on.

This is the "exp-of-sum = product-of-exps" step of the KEY GAP identified in
`docs/transfer_matrix_positivity_design.md` §8.8 (task #46): the concrete
transfer-matrix kernel `exp(-β·S_OS)` must be rewritten as a product of
plaquette Boltzmann factors before the abstract character-expansion lemma can
be applied.  These lemmas are pure algebra (0 axioms, 0 sorries). -/

/-- The single-plaquette Boltzmann factor `exp(-S_p)` factors as a positive
constant `exp(-β)` times `exp(c·Re Tr(U_∂p))` with `c = β/N ≥ 0` (for `β ≥ 0`,
`1 ≤ N`).

This is the atomic building block of the concrete↔abstract bridge: it shows
that each plaquette's contribution to the Boltzmann factor matches the abstract
form `exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` (with `c ≥ 0`) up to a positive constant
that can be absorbed into the overall normalization.  The plaquette product
`plaquetteProduct = U(n,μ)·U(n+e_μ,ν)·U(n+e_μ+e_ν,μ)⁻¹·U(n+e_ν,ν)⁻¹` already has
the 3rd/4th links inverted, matching the abstract form.

This is the same decomposition used internally by `plaquetteContributionPD`
(in `BoltzmannFactor.lean`); it is extracted here as a standalone equality lemma
so it can be composed with `exp_neg_wilsonActionFinite_eq_prod` to bridge the
concrete kernel `exp(-S_W)` to the abstract plaquette-product form. -/
lemma plaquetteContribution_exp_decomp (N : ℕ) (β : ℝ)
    {Λ : Type} [AddVector Λ] (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) :
    Real.exp (-plaquetteContribution N β U n μ ν) =
    Real.exp (-β) *
    Real.exp ((β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ)))) := by
  unfold plaquetteContribution
  have h : -(β * (1 - (1 / (N : ℝ)) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))))) =
      (-β) + (β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))) := by
    rw [div_eq_inv_mul]; ring
  rw [h, Real.exp_add]

/-- The coupling constant `c = β/N` for the abstract plaquette-product form is
non-negative when `β ≥ 0` and `1 ≤ N`.  This is the hypothesis `0 ≤ c` required
by `peterWeyl_clebschGordan_plaquette` and `interface_kernel_character_expansion`. -/
lemma plaquetteBoltzmann_coupling_nonneg (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    0 ≤ β / N := by
  exact div_nonneg hβ (Nat.cast_nonneg N)

/-- The per-plaquette constant `exp(-β)` is positive. -/
lemma plaquetteBoltzmann_const_pos (β : ℝ) : 0 < Real.exp (-β) :=
  Real.exp_pos _

/-- **Transfer-matrix kernel per-plaquette factorization.** The factor
`exp(-β·S_p)` (which appears in the transfer-matrix kernel `exp(-β·S_W) =
∏ exp(-β·S_p)`, since `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_W)`) decomposes as
`exp(-β²)·exp((β²/N)·Re Tr(U_∂p))` with coupling `c = β²/N ≥ 0`.

This is the version needed for the concrete transfer-matrix kernel: the `G`
function uses `exp(-β·S⁺)` (with the extra β), so the per-plaquette factor is
`exp(-β·S_p) = exp(-β²)·exp((β²/N)·Re Tr)`, NOT `exp(-S_p)`.  The coupling
`c = β²/N` is non-negative for all `β` (since `β² ≥ 0`) and `1 ≤ N`. -/
lemma plaquetteContribution_exp_decomp_tm (N : ℕ) (β : ℝ)
    {Λ : Type} [AddVector Λ] (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) :
    Real.exp (-β * plaquetteContribution N β U n μ ν) =
    Real.exp (-(β * β)) *
    Real.exp ((β * β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ)))) := by
  unfold plaquetteContribution
  have h : -β * (β * (1 - (1 / (N : ℝ)) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))))) =
      -(β * β) + (β * β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))) := by
    field_simp; ring
  rw [h, Real.exp_add]

/-- The transfer-matrix coupling `c = β²/N` is non-negative for all `β` and `1 ≤ N`.
Unlike `plaquetteBoltzmann_coupling_nonneg`, this does NOT require `β ≥ 0` (since
`β² ≥ 0` always). -/
lemma plaquetteBoltzmann_tm_coupling_nonneg (N : ℕ) (β : ℝ) (hN : 1 ≤ N) :
    0 ≤ β * β / N := by
  have hβ : 0 ≤ β * β := by nlinarith [sq_nonneg β, pow_two β]
  exact div_nonneg hβ (Nat.cast_nonneg N)

/-- The transfer-matrix per-plaquette constant `exp(-β²)` is positive. -/
lemma plaquetteBoltzmann_tm_const_pos (β : ℝ) : 0 < Real.exp (-(β * β)) :=
  Real.exp_pos _

/-- **exp-of-sum = product-of-exps for the transfer-matrix kernel.** The
transfer-matrix Boltzmann factor `exp(-β·S_W)` factorises as a product of
per-plaquette factors `exp(-β·S_p)`:

    exp(-β·S_W[U]) = ∏_{n ∈ sites} ∏_{μ : Fin 4} ∏_{ν : Fin 4} exp(-β·S_p(n,μ,ν))

This is the transfer-matrix analogue of `exp_neg_wilsonActionFinite_eq_prod`
(in `BoltzmannFactor.lean`), with the extra factor of `β` that the `G`/`osG`
functions introduce.  Pure algebra — no representation theory, no axioms beyond
the standard three. -/
lemma exp_neg_beta_wilsonActionFinite_eq_prod (N : ℕ) (β : ℝ)
    {Λ : Type} [AddVector Λ]
    (sites : Finset Λ) (U : Lattice.LinkVariable (SU N) Λ) :
    Real.exp (-β * Lattice.wilsonActionFinite N β sites U) =
    ∏ n ∈ sites, ∏ μ : Fin 4, ∏ ν : Fin 4,
      Real.exp (-β * Lattice.plaquetteContribution N β U n μ ν) := by
  simp only [Lattice.wilsonActionFinite, ← Finset.sum_neg_distrib, Real.exp_sum,
    Finset.mul_sum]

#print axioms plaquetteContribution_exp_decomp
#print axioms plaquetteBoltzmann_coupling_nonneg
#print axioms plaquetteBoltzmann_const_pos
#print axioms plaquetteContribution_exp_decomp_tm
#print axioms plaquetteBoltzmann_tm_coupling_nonneg
#print axioms plaquetteBoltzmann_tm_const_pos
#print axioms exp_neg_beta_wilsonActionFinite_eq_prod

/-! ### G3: Interface plaquette enumeration

The third piece of the concrete↔abstract bridge (§8.11 of
`docs/transfer_matrix_positivity_design.md`): restrict the product to
*interface* plaquettes only.  The interface action `S_OS_int` is defined as
`∑ (if isInterface then S_p else 0)`, so `exp(-β·S_int) = ∏ (if isInterface
then exp(-β·S_p) else 1)` by exp-of-sum + if-splitting.  Non-interface
plaquettes contribute a factor of 1, so the product is effectively over
interface plaquettes only.  Pure algebra — 0 sorries, 0 custom axioms. -/

/-- The interface plaquette predicate: a plaquette `(n, μ, ν)` is an "interface
plaquette" iff its four corners do NOT all have positive signed time AND do NOT
all have negative signed time (i.e., the corners straddle the time interface).
This matches the condition in `wilsonActionOSInterface`.  Defined as an
abbreviation so it unfolds to the inline condition (matching the `Decidable`
instance used by `wilsonActionOSInterface`). -/
abbrev isInterfacePlaquette (T L : ℕ) [NeZero T] [NeZero L]
    (n : PeriodicSite T L) (μ ν : Fin 4) : Prop :=
  ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
  ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time < 0)

/-- `wilsonActionOSInterface` equals the sum over all plaquettes with the
interface predicate as the if-condition.  This is by definition (the condition
in `wilsonActionOSInterface` is exactly `isInterfacePlaquette`). -/
lemma wilsonActionOSInterface_eq (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSInterface N T L β U =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0) := by
  unfold wilsonActionOSInterface isInterfacePlaquette
  rfl

/-- The interface action is uniformly bounded: `|S_int| ≤ #(PeriodicSite T L)·32·|β|`.

Each plaquette contribution satisfies `|plaquetteContribution| ≤ 2|β|`
(`plaquetteContribution_bounded`), and the interface action is a sum of at most
`#(PeriodicSite T L)·16` such terms (the `if isInterfacePlaquette` selects a subset).
This gives `|S_int| ≤ #(PeriodicSite T L)·16·2|β| = #(PeriodicSite T L)·32·|β|`.

This is ingredient 2 of the integrability discharge (design doc §8.11.10): it
provides a uniform upper bound on `|S_int|`, hence a positive lower bound
`exp(-β·S_int) ≥ exp(-|β|·#(PeriodicSite T L)·32·|β|) > 0`. 0 sorries, 0 custom axioms. -/
lemma wilsonActionOSInterface_bounded (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    |wilsonActionOSInterface N T L β U| ≤ (Fintype.card (PeriodicSite T L) * 32) * |β| := by
  rw [wilsonActionOSInterface_eq]
  -- Each term is bounded: |if c then pc else 0| ≤ 2|β|
  have h_bound : ∀ n μ ν,
      |(if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0)| ≤
        2 * |β| := by
    intro n μ ν
    by_cases h : isInterfacePlaquette T L n μ ν
    · rw [if_pos h]; exact plaquetteContribution_bounded N β U n μ ν
    · rw [if_neg h]; simp
  -- Upper bound: each term ≤ 2|β|
  have h_upper : ∀ n μ ν,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0) ≤
        2 * |β| := fun n μ ν => (abs_le.mp (h_bound n μ ν)).2
  -- Lower bound: each term ≥ -(2|β|)
  have h_lower : ∀ n μ ν,
      -(2 * |β|) ≤
        (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0) :=
    fun n μ ν => (abs_le.mp (h_bound n μ ν)).1
  -- S ≤ ∑ n μ ν 2|β|
  have h_S_upper : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0)) ≤
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, 2 * |β| := by
    apply Finset.sum_le_sum; intro n _
    apply Finset.sum_le_sum; intro μ _
    apply Finset.sum_le_sum; intro ν _
    exact h_upper n μ ν
  -- -(∑ n μ ν 2|β|) ≤ S
  have h_S_lower : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, -(2 * |β|)) ≤
    (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0)) := by
    apply Finset.sum_le_sum; intro n _
    apply Finset.sum_le_sum; intro μ _
    apply Finset.sum_le_sum; intro ν _
    exact h_lower n μ ν
  -- Constant sums
  have h_const : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, 2 * |β|) =
      (Fintype.card (PeriodicSite T L) * 32) * |β| := by
    have h_ν : ∑ ν : Fin 4, (2 * |β| : ℝ) = 8 * |β| := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_μ : ∑ μ : Fin 4, (8 * |β| : ℝ) = 32 * |β| := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_n : ∑ n : PeriodicSite T L, (32 * |β| : ℝ) =
        Fintype.card (PeriodicSite T L) * (32 * |β|) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h_ν, h_μ, h_n]; ring
  have h_const_neg : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, -(2 * |β|)) =
      -((Fintype.card (PeriodicSite T L) * 32) * |β|) := by
    have h_ν : ∑ ν : Fin 4, (-(2 * |β|) : ℝ) = -(8 * |β|) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_μ : ∑ μ : Fin 4, (-(8 * |β|) : ℝ) = -(32 * |β|) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_n : ∑ n : PeriodicSite T L, (-(32 * |β|) : ℝ) =
        -(Fintype.card (PeriodicSite T L) * (32 * |β|)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    rw [h_ν, h_μ, h_n]; ring
  -- |S| ≤ C
  rw [h_const] at h_S_upper
  rw [h_const_neg] at h_S_lower
  exact abs_le.mpr ⟨h_S_lower, h_S_upper⟩

#print axioms wilsonActionOSInterface_bounded

/-- The interface Boltzmann factor `exp(-β·S_int)` is bounded below by a positive
constant independent of `U`:

    exp(-|β|·#(PeriodicSite T L)·32·|β|) ≤ exp(-β·S_int(U))

This follows from `wilsonActionOSInterface_bounded` (`|S_int| ≤ C`) and the
monotonicity of `exp`: `-β·S_int ≥ -|β·S_int| ≥ -|β|·C`, so
`exp(-β·S_int) ≥ exp(-|β|·C) > 0`.

This is the key ingredient for the domination argument in the integrability
discharge (design doc §8.11.10): it provides a uniform positive lower bound
`m = exp(-|β|·C) > 0` on `exp(-β·S_int)`, allowing division by this factor to
deduce integrability of `ψ(merge)·exp(-β·S⁺(merge)/2)` from the integrability
of the full integrand `ψ(merge)·exp(-β·(S⁺(u)/2 + S⁺(merge)/2 + S_int(U)))`.
0 sorries, 0 custom axioms. -/
lemma exp_neg_beta_wilsonActionOSInterface_lower_bound (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-|β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|)) ≤
      Real.exp (-β * wilsonActionOSInterface N T L β U) := by
  apply Real.exp_le_exp.mpr
  have h_bound := wilsonActionOSInterface_bounded N T L β U
  have h_abs : |β * wilsonActionOSInterface N T L β U| ≤
      |β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h_bound (abs_nonneg _)
  have h_le : β * wilsonActionOSInterface N T L β U ≤
      |β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|) := by
    have h_self : β * wilsonActionOSInterface N T L β U ≤
        |β * wilsonActionOSInterface N T L β U| := le_abs_self _
    linarith
  linarith

#print axioms exp_neg_beta_wilsonActionOSInterface_lower_bound

/-- **G3: exp-of-sum for the interface action.** The interface Boltzmann factor
`exp(-β·S_int)` factorises as a product of per-plaquette factors, where only
interface plaquettes contribute (non-interface plaquettes contribute 1):

    exp(-β·S_int) = ∏_{n,μ,ν} (if isInterfacePlaquette then exp(-β·S_p) else 1)

This is the exp-of-sum = product-of-exps identity applied to
`wilsonActionOSInterface_eq`, combined with if-splitting
(`exp(-β·(if c then x else 0)) = if c then exp(-β·x) else 1`).  Pure algebra —
0 sorries, 0 custom axioms. -/
lemma exp_neg_beta_wilsonActionOSInterface_eq_prod (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-β * wilsonActionOSInterface N T L β U) =
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then
        Real.exp (-β * plaquetteContribution N β U n μ ν) else 1) := by
  rw [wilsonActionOSInterface_eq]
  simp only [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro n _
  apply Finset.prod_congr rfl
  intro μ _
  apply Finset.prod_congr rfl
  intro ν _
  split_ifs
  · rfl
  · simp [Real.exp_zero]

/-- **G3 composed with G2: the interface Boltzmann factor as a product of
abstract plaquette Boltzmann factors.** Combining
`exp_neg_beta_wilsonActionOSInterface_eq_prod` (G3) with
`plaquetteContribution_exp_decomp_tm` (G2), the interface Boltzmann factor
`exp(-β·S_int)` equals a product of `exp(c·Re Tr(P_p))` factors (with `c = β²/N
≥ 0`) over interface plaquettes, times a positive constant `exp(-β²)` per
interface plaquette:

    exp(-β·S_int) = ∏_{n,μ,ν} (if isInterface then exp(-β²)·exp((β²/N)·Re Tr(P_p)) else 1)

The non-interface terms are 1, so this is effectively a product over interface
plaquettes only.  The `exp(-β²)` factors are a positive constant absorbable into
normalization.  This is the form that `interface_kernel_character_expansion`
operates on (with `c = β²/N`).  Pure algebra — 0 sorries, 0 custom axioms. -/
lemma exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-β * wilsonActionOSInterface N T L β U) =
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then
        Real.exp (-(β * β)) *
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))))
        else 1) := by
  rw [exp_neg_beta_wilsonActionOSInterface_eq_prod]
  apply Finset.prod_congr rfl
  intro n _
  apply Finset.prod_congr rfl
  intro μ _
  apply Finset.prod_congr rfl
  intro ν _
  split_ifs with h
  · rw [plaquetteContribution_exp_decomp_tm]
  · rfl

#print axioms wilsonActionOSInterface_eq
#print axioms exp_neg_beta_wilsonActionOSInterface_eq_prod
#print axioms exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract

/-! ### Concrete link/plaquette structures for the character expansion

These definitions set up the concrete combinatorial data needed to apply the
abstract `interface_kernel_character_expansion` (in `PeterWeyl.lean`) to the
concrete periodic lattice.  This is sub-step (i) of Lemma 2
(`transfer_matrix_integral_reduction`) in
`docs/transfer_matrix_positivity_design.md` §8.8: identifying the link
partition `L = L_U ⊔ L_0 ⊔ L_V` (U⁺/u⁰/V⁺ links) for the concrete lattice.

All definitions and lemmas here are pure combinatorics — 0 sorries, 0 custom
axioms. -/

/-- The j-th link of a plaquette `(n, μ, ν)`.  The four links of the plaquette
product `U(n,μ) · U(n+e_μ,ν) · U(n+e_μ+e_ν,μ)⁻¹ · U(n+e_ν,ν)⁻¹` are:
  - j=0: `(n, μ)`           — the link `U(n, μ)`
  - j=1: `(n+e_μ, ν)`       — the link `U(n+e_μ, ν)`
  - j=2: `(n+e_μ+e_ν, μ)`   — the link `U(n+e_μ+e_ν, μ)`, **inverted** in the product
  - j=3: `(n+e_ν, ν)`       — the link `U(n+e_ν, ν)`, **inverted** in the product
This matches the definition of `plaquetteProduct` in `Lattice.lean`. -/
def plaquetteLinkIdx (T L : ℕ) [NeZero T] [NeZero L]
    (p : PlaquetteIndex T L) (j : Fin 4) : PeriodicSite T L × Fin 4 :=
  match j with
  | 0 => (p.1, p.2.1)
  | 1 => (addVectorPeriodic T L p.1 p.2.1, p.2.2)
  | 2 => (addVectorPeriodic T L (addVectorPeriodic T L p.1 p.2.1) p.2.2, p.2.1)
  | 3 => (addVectorPeriodic T L p.1 p.2.2, p.2.2)

/-- The plaquette product equals the product of link variables at the four
plaquette links (with the 3rd and 4th inverted).  This connects the concrete
`plaquetteProduct` to the abstract form
`g(links p 0)·g(links p 1)·g(links p 2)⁻¹·g(links p 3)⁻¹` that
`interface_kernel_character_expansion` operates on. -/
lemma plaquetteProduct_eq_linkIdx (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : PlaquetteIndex T L) :
    plaquetteProduct N U p.1 p.2.1 p.2.2 =
    U.value (plaquetteLinkIdx T L p 0).1 (plaquetteLinkIdx T L p 0).2 *
    U.value (plaquetteLinkIdx T L p 1).1 (plaquetteLinkIdx T L p 1).2 *
    (U.value (plaquetteLinkIdx T L p 2).1 (plaquetteLinkIdx T L p 2).2)⁻¹ *
    (U.value (plaquetteLinkIdx T L p 3).1 (plaquetteLinkIdx T L p 3).2)⁻¹ := by
  unfold plaquetteLinkIdx plaquetteProduct
  rfl

/-- Interface plaquettes as a subtype of `PlaquetteIndex`. -/
abbrev InterfacePlaquette (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {p : PlaquetteIndex T L // isInterfacePlaquette T L p.1 p.2.1 p.2.2}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (InterfacePlaquette T L) := by
  classical
  exact inferInstanceAs (Fintype {p : PlaquetteIndex T L //
    isInterfacePlaquette T L p.1 p.2.1 p.2.2})

instance (T L : ℕ) [NeZero T] [NeZero L] : DecidableEq (InterfacePlaquette T L) :=
  inferInstanceAs (DecidableEq {p : PlaquetteIndex T L //
    isInterfacePlaquette T L p.1 p.2.1 p.2.2})

/-- The Finset of all links appearing in at least one interface plaquette. -/
noncomputable def interfacePlaqLinkFinset (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (PeriodicSite T L × Fin 4) :=
  (Finset.univ : Finset (InterfacePlaquette T L × Fin 4)).image
    (fun x => plaquetteLinkIdx T L x.1.val x.2)

/-- The type of links appearing in interface plaquettes (subtype).  This is the
concrete `L` for `interface_kernel_character_expansion`: by construction, every
link in this type appears in at least one interface plaquette, so the
surjectivity hypothesis `hlinks_surj` holds. -/
abbrev InterfaceLink (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {l : PeriodicSite T L × Fin 4 // l ∈ interfacePlaqLinkFinset T L}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (InterfaceLink T L) := by
  classical
  exact inferInstanceAs (Fintype {l : PeriodicSite T L × Fin 4 //
    l ∈ interfacePlaqLinkFinset T L})

instance (T L : ℕ) [NeZero T] [NeZero L] : DecidableEq (InterfaceLink T L) :=
  inferInstanceAs (DecidableEq {l : PeriodicSite T L × Fin 4 //
    l ∈ interfacePlaqLinkFinset T L})

/-- The link assignment `InterfacePlaquette → Fin 4 → InterfaceLink`.  Maps each
plaquette `p` and index `j` to the j-th link of `p`, packaged as an
`InterfaceLink` (with the proof that it appears in an interface plaquette). -/
def interfaceLinkAssign (T L : ℕ) [NeZero T] [NeZero L]
    (p : InterfacePlaquette T L) (j : Fin 4) : InterfaceLink T L :=
  ⟨plaquetteLinkIdx T L p.val j, by
    simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop]
    exact ⟨p, j, rfl⟩⟩

/-- The link assignment is surjective: every `InterfaceLink` arises as some
plaquette's j-th link.  This is the `hlinks_surj` hypothesis for
`interface_kernel_character_expansion`. -/
lemma interfaceLinkAssign_surj (T L : ℕ) [NeZero T] [NeZero L] :
    ∀ l : InterfaceLink T L, ∃ p j, interfaceLinkAssign T L p j = l := by
  intro l
  have hl : l.val ∈ interfacePlaqLinkFinset T L := l.prop
  simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, exists_prop] at hl
  obtain ⟨p, j, hj⟩ := hl
  refine ⟨p, j, ?_⟩
  simp only [interfaceLinkAssign, Subtype.mk_eq_mk, hj]

/-- Extract the link variable `U(n, μ)` from a full configuration at an
`InterfaceLink` `l = (n, μ)`. -/
def interfaceLinkVar (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (l : InterfaceLink T L) : SU N :=
  U.value l.val.1 l.val.2

/-- `interfaceLinkVar · l` is measurable in `U` (a coordinate projection from `U.value`). -/
lemma measurable_interfaceLinkVar (N T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    Measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => interfaceLinkVar N T L U l) := by
  dsimp [interfaceLinkVar]
  have h_value_map : Measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value) :=
    comap_measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value)
  have h_at_n : Measurable (fun (f : PeriodicSite T L → Fin 4 → SU N) => f l.val.1) :=
    measurable_pi_apply l.val.1
  have h_at_n_μ : Measurable (fun (f : Fin 4 → SU N) => f l.val.2) :=
    measurable_pi_apply l.val.2
  exact h_at_n_μ.comp (h_at_n.comp h_value_map)

/-- The plaquette product of an interface plaquette equals the abstract form
`g(links p 0)·g(links p 1)·g(links p 2)⁻¹·g(links p 3)⁻¹` where `g` extracts
link variables via `interfaceLinkVar`. -/
lemma plaquetteProduct_interface_eq (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : InterfacePlaquette T L) :
    plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 =
    interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
    interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
    (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
    (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ := by
  unfold interfaceLinkVar interfaceLinkAssign
  exact plaquetteProduct_eq_linkIdx N T L U p.val

/-- The positive-time links among the interface links (`L_U`). -/
noncomputable def interfaceLinkPos (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (Finset.univ : Finset (InterfaceLink T L)).filter
    (fun l => signedTime T l.val.1.time > 0)

/-- The interface (time-0) links among the interface links (`L_0`). -/
noncomputable def interfaceLinkInt (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (Finset.univ : Finset (InterfaceLink T L)).filter
    (fun l => signedTime T l.val.1.time = 0)

/-- The negative-time links among the interface links (`L_V`). -/
noncomputable def interfaceLinkNeg (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (Finset.univ : Finset (InterfaceLink T L)).filter
    (fun l => signedTime T l.val.1.time < 0)

/-- Trichotomy of `signedTime`: exactly one of `> 0`, `= 0`, `< 0` holds. -/
lemma signedTime_trichotomy (T : ℕ) (t : ZMod T) :
    signedTime T t > 0 ∨ signedTime T t = 0 ∨ signedTime T t < 0 := by
  omega

/-- The three link sets are pairwise disjoint and cover all interface links. -/
lemma interfaceLinkPartition_disjoint_cover (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (interfaceLinkPos T L) (interfaceLinkInt T L) ∧
    Disjoint (interfaceLinkPos T L ∪ interfaceLinkInt T L) (interfaceLinkNeg T L) ∧
    interfaceLinkPos T L ∪ interfaceLinkInt T L ∪ interfaceLinkNeg T L = Finset.univ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint pos int
    refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [interfaceLinkPos, Finset.mem_filter] at hl
    rw [interfaceLinkInt, Finset.mem_filter] at hl'
    obtain ⟨_, hpos⟩ := hl
    obtain ⟨_, hint⟩ := hl'
    rw [hint] at hpos
    exact lt_irrefl _ hpos
  · -- Disjoint (pos ∪ int) neg
    refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [interfaceLinkNeg, Finset.mem_filter] at hl'
    obtain ⟨_, hneg⟩ := hl'
    rcases Finset.mem_union.mp hl with h | h
    · rw [interfaceLinkPos, Finset.mem_filter] at h
      obtain ⟨_, hpos⟩ := h
      exact lt_irrefl _ (lt_of_lt_of_le hpos (le_of_lt hneg))
    · rw [interfaceLinkInt, Finset.mem_filter] at h
      obtain ⟨_, hint⟩ := h
      rw [hint] at hneg
      exact lt_irrefl _ hneg
  · -- Cover
    ext l
    simp only [interfaceLinkPos, interfaceLinkInt, interfaceLinkNeg, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases signedTime_trichotomy T l.val.1.time with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- The partition in the form required by `interface_kernel_character_expansion`:
`hdisj : Disjoint L_U L_0 ∧ Disjoint (L_U ∪ L_0) L_V`. -/
lemma interfaceLinkPartition_hdisj (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (interfaceLinkPos T L) (interfaceLinkInt T L) ∧
    Disjoint (interfaceLinkPos T L ∪ interfaceLinkInt T L) (interfaceLinkNeg T L) :=
  ⟨interfaceLinkPartition_disjoint_cover T L |>.1,
   interfaceLinkPartition_disjoint_cover T L |>.2.1⟩

/-- The partition in the form required by `interface_kernel_character_expansion`:
`hcover : L_U ∪ L_0 ∪ L_V = Finset.univ`. -/
lemma interfaceLinkPartition_hcover (T L : ℕ) [NeZero T] [NeZero L] :
    interfaceLinkPos T L ∪ interfaceLinkInt T L ∪ interfaceLinkNeg T L = Finset.univ :=
  interfaceLinkPartition_disjoint_cover T L |>.2.2

/-- The product over all plaquettes with an if-condition equals the product over
interface plaquettes only (non-interface terms contribute 1).  This is the
"filter product" step connecting G3 (`exp_neg_beta_wilsonActionOSInterface_eq_prod`)
to the abstract product `∏_{p ∈ InterfacePlaquette} exp(c·Re Tr(...))`. -/
lemma prod_if_interface_eq_prod_subtype (T L : ℕ) [NeZero T] [NeZero L]
    {α : Type*} (f : PlaquetteIndex T L → α) [CommMonoid α] :
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4,
        (if isInterfacePlaquette T L n μ ν then f (n, μ, ν) else 1) =
    ∏ p : InterfacePlaquette T L, f p.val := by
  classical
  -- Merge the three nested products into one over `PlaquetteIndex T L`.
  -- `simp only` does a bottom-up traversal, so it rewrites the innermost
  -- `∏ μ, ∏ ν` first (→ `∏ q : Fin 4 × Fin 4`) and then `∏ n, ∏ q`
  -- (→ `∏ p : PeriodicSite T L × (Fin 4 × Fin 4)`), producing the
  -- *right-associated* product type `PlaquetteIndex T L`.
  simp only [← Fintype.prod_prod_type']
  -- Now: ∏ p : PlaquetteIndex T L,
  --   (if isInterfacePlaquette T L p.1 p.2.1 p.2.2 then f (p.1, p.2.1, p.2.2) else 1)
  -- Convert the if-product to a filtered product (non-interface terms are 1).
  rw [← Finset.prod_filter]
  -- Now: ∏ p ∈ Finset.univ.filter (isInterfacePlaquette …), f (p.1, p.2.1, p.2.2)
  -- Convert the filtered product to a product over the subtype `InterfacePlaquette`.
  -- (f (p.1, p.2.1, p.2.2) = f p by Prod-eta, and Subtype cond = InterfacePlaquette.)
  exact Finset.prod_subtype _ (fun x => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun p => f p)

#print axioms prod_if_interface_eq_prod_subtype

/-- **Interface Boltzmann factor as a positive constant times the abstract plaquette
product.** The concrete interface Boltzmann factor `exp(-β·S_int)` equals a positive
constant `C = ∏_{p ∈ InterfacePlaquette} exp(-β²)` times the abstract plaquette product
`∏_{p ∈ InterfacePlaquette} exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))`, where the plaquette product
is expressed via the concrete link structures (`interfaceLinkVar`, `interfaceLinkAssign`).

This combines G3 (`exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract`),
`prod_if_interface_eq_prod_subtype` (restrict to interface plaquettes), and
`plaquetteProduct_interface_eq` (concrete→abstract plaquette product).  The constant
`C > 0` is absorbable into normalization.  This is sub-step (ii) of Lemma 2
(`transfer_matrix_integral_reduction`) in
`docs/transfer_matrix_positivity_design.md` §8.8: rewriting the concrete interface
Boltzmann factor into the abstract form that `interface_kernel_character_expansion`
operates on.  Pure algebra — 0 sorries, 0 custom axioms. -/
lemma interface_boltzmann_eq_abstract_product (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :
    ∃ (C : ℝ) (hC : 0 < C),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      Real.exp (-β * wilsonActionOSInterface N T L β U) =
        C * ∏ p : InterfacePlaquette T L,
          Real.exp ((β * β / N) * Complex.re (Matrix.trace
            ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
              interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
  set C := ∏ p : InterfacePlaquette T L, Real.exp (-(β * β))
  refine ⟨C, ?_, fun U => ?_⟩
  · exact Finset.prod_pos (fun p _ => plaquetteBoltzmann_tm_const_pos β)
  · rw [exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract]
    -- Step 1: rewrite the if-product to a subtype product via prod_if_interface_eq_prod_subtype.
    -- h's LHS is defeq to the goal's LHS (beta + projection reduction); `simp only` handles this.
    have h := prod_if_interface_eq_prod_subtype T L
      (fun p : PlaquetteIndex T L =>
        Real.exp (-(β * β)) *
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace ((plaquetteProduct N U p.1 p.2.1 p.2.2 :
            Matrix (Fin N) (Fin N) ℂ)))))
    simp only [h]
    -- Step 2: split the product of products.
    rw [Finset.prod_mul_distrib]
    -- Step 3: C = ∏ p, exp(-β²) by `set`, so the first factor is C (closed by rfl below).
    -- Step 4: rewrite plaquetteProduct to the abstract link form in the second factor.
    have h_link : ∏ p : InterfacePlaquette T L,
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace ((plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 :
            Matrix (Fin N) (Fin N) ℂ)))) =
      ∏ p : InterfacePlaquette T L,
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace
            ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
              interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
      exact Finset.prod_congr rfl (fun p _ => by rw [plaquetteProduct_interface_eq N T L U p])
    rw [h_link]

#print axioms interface_boltzmann_eq_abstract_product

/-- **Character expansion of the concrete interface plaquette product.** Applying
`interface_kernel_character_expansion` (Peter-Weyl / Clebsch-Gordan) to the concrete
lattice, the abstract interface plaquette product
`∏_{p ∈ InterfacePlaquette} exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))` (viewed in `ℂ`) admits the
separable character expansion

    ∏_p exp(c·Re Tr(...)) = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))

with `F(w) ≥ 0`, where `Φ_w(U⁺) = ∏_{l ∈ L_U} χ_{w(l)}(g_l)`,
`Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(g_l)`, and the V⁺ factor uses the dual map.
This is sub-step (ii) of Lemma 2 (`transfer_matrix_integral_reduction`):
applying the abstract character expansion to the concrete lattice data.
Uses the `peterWeyl_clebschGordan_plaquette` axiom (count 6); 0 sorries. -/
lemma interface_product_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : (InterfaceLink T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      ∏ p : InterfacePlaquette T L,
        (Real.exp ((β * β / N) * Complex.re (Matrix.trace
          ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
            interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
            (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
            (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ, hexp4, hL2⟩ :=
    peterWeyl_clebschGordan_plaquette N (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN)
  letI : Fintype ι := hι
  classical
  obtain ⟨F, hF, hF_decomp⟩ := interface_kernel_character_expansion
    ρ hU coeff hcoeff cg hcg hcg_decomp dual hdual
    (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN) hexp4
    (InterfacePlaquette T L) (InterfaceLink T L) (interfaceLinkAssign T L)
    (interfaceLinkAssign_surj T L)
    (interfaceLinkPos T L) (interfaceLinkInt T L) (interfaceLinkNeg T L)
    (interfaceLinkPartition_hdisj T L) (interfaceLinkPartition_hcover T L)
  refine ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  exact hF_decomp (interfaceLinkVar N T L U)

#print axioms interface_product_character_expansion

/-- **Combined character expansion of the interface Boltzmann factor.** Composing
`interface_boltzmann_eq_abstract_product` (exp(-β·S_int) = C · ∏_p exp(c·Re Tr(...)))
with `interface_product_character_expansion` (∏_p exp(c·Re Tr(...)) = ∑_w F(w)·Φ_w·Ψ_w·V_w),
the interface Boltzmann factor admits the character expansion (viewed in ℂ)

    (exp(-β·S_int(U)) : ℂ) = (C : ℂ) · ∑_w F(w) · Φ_w(U) · Ψ_w(U) · V_w(U)

with C > 0 and F(w) ≥ 0, where Φ_w(U) = ∏_{l ∈ L_U} χ_{w(l)}(g_l),
Ψ_w(U) = ∏_{l ∈ L_0} χ_{w(l)}(g_l), V_w(U) = star(∏_{l ∈ L_V} χ_{dual(w(l))}(g_l)),
and g_l = interfaceLinkVar U l.  This is step 3 of sub-step (iii) of Lemma 2
(`transfer_matrix_integral_reduction`): substituting the character expansion
into the transfer matrix inner product. Uses `peterWeyl_clebschGordan_plaquette`
(axiom count 6, unchanged); 0 sorries. -/
lemma interface_boltzmann_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (C : ℝ) (hC : 0 < C)
      (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : (InterfaceLink T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)) := by
  -- C = ∏_p exp(-β²) is independent of U; obtain it once (uniform abstract-product form).
  obtain ⟨C, hC, hC_eq_all⟩ := interface_boltzmann_eq_abstract_product N T L β
  -- The character-expansion data (ι, ρ, dual, F) is independent of U (uniform version).
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, hF_decomp⟩ :=
    interface_product_character_expansion N T L β hN
  letI : Fintype ι := hι
  classical
  refine ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  -- Per-U: combine the abstract-product form with the character expansion.
  rw [hC_eq_all U]
  have h := hF_decomp U
  norm_cast at h
  rw [Complex.ofReal_mul, h]

#print axioms interface_boltzmann_character_expansion

/-! ### Bridge lemmas: link partition ↔ site partition

These lemmas connect the LINK-based partition (`interfaceLinkPos/Int/Neg`, used by
the character expansion) with the SITE-based partition
(`positiveSites/interfaceSites/negativeSites`, used by the measure factorization
in `TransferMatrix.lean`).  A link `(n, μ)` is in `interfaceLinkPos` iff its base
site `n` is in `positiveSites`, etc.  This compatibility is needed for sub-step
(iii) of Lemma 2 (Fubini reduction).  All 0 sorries, 0 custom axioms. -/

lemma interfaceLinkPos_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkPos T L ↔ l.val.1 ∈ positiveSites T L := by
  simp only [interfaceLinkPos, Finset.mem_filter, Finset.mem_univ, true_and,
    positiveSites]

lemma interfaceLinkInt_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkInt T L ↔ l.val.1 ∈ interfaceSites T L := by
  simp only [interfaceLinkInt, Finset.mem_filter, Finset.mem_univ, true_and,
    interfaceSites]

lemma interfaceLinkNeg_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkNeg T L ↔ l.val.1 ∈ negativeSites T L := by
  simp only [interfaceLinkNeg, Finset.mem_filter, Finset.mem_univ, true_and,
    negativeSites]

#print axioms interfaceLinkPos_mem_iff
#print axioms interfaceLinkInt_mem_iff
#print axioms interfaceLinkNeg_mem_iff


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

set_option maxHeartbeats 8000000 in
/-- **Link correspondence under reflection.** For any plaquette `p` and link position `j`,
the reflected link `(θ(link p j).1, (link p j).2)` equals `link (reflectPlaquetteIndex p) j'`
for some `j'`. The position `j'` is a permutation of `j` depending on the directions:
- (μ≠0, ν≠0): `j' = j` (spatial directions commute with reflection)
- (μ=0, ν≠0): `j' = j + 3` (time direction reversed)
- (μ≠0, ν=0): `j' = j + 1` (time direction reversed)
- (μ=0, ν=0): `j' = j + 2` (both time directions reversed)

This is the key lemma showing the reflection maps `interfacePlaqLinkFinset` to itself. -/
lemma plaquetteLinkIdx_reflect (T L : ℕ) [NeZero T] [NeZero L]
    (p : PlaquetteIndex T L) (j : Fin 4) :
    ∃ j' : Fin 4, plaquetteLinkIdx T L (reflectPlaquetteIndex T L p) j' =
      (ReflectSite.reflectSite (plaquetteLinkIdx T L p j).1, (plaquetteLinkIdx T L p j).2) := by
  rcases p with ⟨n, μ, ν⟩
  by_cases hμ : μ = 0
  · by_cases hν : ν = 0
    · subst hμ hν
      refine ⟨j + 2, ?_⟩
      fin_cases j <;>
        simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
          reflectSitePeriodic, addVectorPeriodic]
    · subst hμ
      refine ⟨j + 3, ?_⟩
      fin_cases j <;> fin_cases ν <;> first
        | contradiction
        | simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
            reflectSitePeriodic, addVectorPeriodic]
  · by_cases hν : ν = 0
    · subst hν
      refine ⟨j + 1, ?_⟩
      fin_cases j <;> fin_cases μ <;> first
        | contradiction
        | simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
            reflectSitePeriodic, addVectorPeriodic]
    · refine ⟨j, ?_⟩
      fin_cases j <;> fin_cases μ <;> fin_cases ν <;> first
        | contradiction
        | simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
            reflectSitePeriodic, addVectorPeriodic]

#print axioms plaquetteLinkIdx_reflect

set_option maxHeartbeats 1000000 in
/-- Reflection preserves the interface plaquette predicate: a plaquette is an
interface plaquette iff its reflection is. -/
lemma isInterfacePlaquette_reflect (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (p : PlaquetteIndex T L) :
    isInterfacePlaquette T L (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
        (reflectPlaquetteIndex T L p).2.2 ↔
    isInterfacePlaquette T L p.1 p.2.1 p.2.2 := by
  have h1 := reflectPlaquetteIndex_sign T L hT p
  have h2 : plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔ plaquettePositive T L p := by
    have h_inv : reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p :=
      reflectPlaquetteIndex_involution T L p
    have h' := reflectPlaquetteIndex_sign T L hT (reflectPlaquetteIndex T L p)
    simpa [h_inv] using h'.symm
  simp only [isInterfacePlaquette, plaquettePositive, plaquetteNegative]
  constructor
  · rintro ⟨hnpos, hnneg⟩
    exact ⟨mt h2.symm.mp hnneg, mt h1.symm.mp hnpos⟩
  · rintro ⟨hnpos, hnneg⟩
    exact ⟨mt h1.mp hnneg, mt h2.mp hnpos⟩

#print axioms isInterfacePlaquette_reflect

/-- The reflection of an interface link: maps `l = (n, μ)` to `(θn, μ)`.
The reflected link is again an interface link because reflection maps interface
plaquettes to interface plaquettes (`isInterfacePlaquette_reflect`) and maps
links of interface plaquettes to links of reflected interface plaquettes
(`plaquetteLinkIdx_reflect`). -/
def reflectInterfaceLink (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (l : InterfaceLink T L) : InterfaceLink T L :=
  ⟨(ReflectSite.reflectSite l.val.1, l.val.2), by
    have hl := l.prop
    simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop] at hl
    obtain ⟨p, j, hj⟩ := hl
    have hp : isInterfacePlaquette T L (reflectPlaquetteIndex T L p.val).1
        (reflectPlaquetteIndex T L p.val).2.1 (reflectPlaquetteIndex T L p.val).2.2 :=
      (isInterfacePlaquette_reflect T L hT p.val).mpr p.prop
    simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop]
    obtain ⟨j', hj'⟩ := plaquetteLinkIdx_reflect T L p.val j
    refine ⟨⟨reflectPlaquetteIndex T L p.val, hp⟩, j', ?_⟩
    rw [hj] at hj'
    exact hj'⟩

/-- `reflectInterfaceLink` is involutive: reflecting twice is the identity. -/
lemma reflectInterfaceLink_involution (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (l : InterfaceLink T L) :
    reflectInterfaceLink T L hT (reflectInterfaceLink T L hT l) = l := by
  simp only [reflectInterfaceLink, Subtype.mk_eq_mk]
  ext <;> simp [ReflectSite.involution]

#print axioms reflectInterfaceLink_involution

/-- Reflection maps positive-time interface links to negative-time interface links. -/
lemma reflectInterfaceLink_mem_neg_of_pos (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkPos T L) :
    reflectInterfaceLink T L hT l ∈ interfaceLinkNeg T L := by
  rw [interfaceLinkPos, Finset.mem_filter] at hl
  obtain ⟨_, hpos⟩ := hl
  rw [interfaceLinkNeg, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, reflectInterfaceLink]
  rw [signedTime_reflectSite hT l.val.1]
  omega

/-- Reflection maps negative-time interface links to positive-time interface links. -/
lemma reflectInterfaceLink_mem_pos_of_neg (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkNeg T L) :
    reflectInterfaceLink T L hT l ∈ interfaceLinkPos T L := by
  rw [interfaceLinkNeg, Finset.mem_filter] at hl
  obtain ⟨_, hneg⟩ := hl
  rw [interfaceLinkPos, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, reflectInterfaceLink]
  rw [signedTime_reflectSite hT l.val.1]
  omega

/-- Reflection maps interface (time-0) interface links to interface interface links. -/
lemma reflectInterfaceLink_mem_int_of_int (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkInt T L) :
    reflectInterfaceLink T L hT l ∈ interfaceLinkInt T L := by
  rw [interfaceLinkInt, Finset.mem_filter] at hl
  obtain ⟨_, hint⟩ := hl
  rw [interfaceLinkInt, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, reflectInterfaceLink]
  rw [signedTime_reflectSite hT l.val.1, hint]
  omega

#print axioms reflectInterfaceLink_mem_neg_of_pos
#print axioms reflectInterfaceLink_mem_pos_of_neg
#print axioms reflectInterfaceLink_mem_int_of_int

/-- The reflection bijection between positive-time and negative-time interface
links.  This is the map `φ : interfaceLinkNeg → interfaceLinkPos` (read in
reverse) used by the reindexing `θ` in the σ-inversion lemma. -/
def reflectInterfaceLinkPosNegEquiv (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) :
    {l : InterfaceLink T L // l ∈ interfaceLinkPos T L} ≃
    {l : InterfaceLink T L // l ∈ interfaceLinkNeg T L} where
  toFun l := ⟨reflectInterfaceLink T L hT l.val, reflectInterfaceLink_mem_neg_of_pos T L hT l.prop⟩
  invFun l := ⟨reflectInterfaceLink T L hT l.val, reflectInterfaceLink_mem_pos_of_neg T L hT l.prop⟩
  left_inv l := by
    apply Subtype.eq
    exact reflectInterfaceLink_involution T L hT l.val
  right_inv l := by
    apply Subtype.eq
    exact reflectInterfaceLink_involution T L hT l.val

#print axioms reflectInterfaceLinkPosNegEquiv

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

/-! ## Clean factorization and the PD-structure obstruction

The reflection-positivity integrand `osG(U) · osG(θU)` factorizes cleanly as
`f(U) · f(θU) · exp(-β S_W(U))` (lemma `osG_thetaG_factorization` below).
This shows that the axiom `transferMatrixPositivity_axiom` is equivalent to:

    ∫ f(U) · f(θU) · exp(-β S_W(U)) dμ₀ ≥ 0

where `exp(-β S_W)` is the full Boltzmann factor, proved positive-definite on the
full link-variable group by `boltzmannFactorPD` (in `BoltzmannFactor.lean`).

**Key obstruction**: this integral is NOT the standard positive-definite quadratic
form `∫∫ f(g) conj(f(h)) K(g⁻¹ h) dμ dμ ≥ 0` (which follows from PD-ness of `K`).
Instead, it is a *single* integral `∫ f(g) f(θg) K(g) dμ` with the geometric
reflection `θ` and `K` evaluated at `g` (not `g⁻¹ h`).  PD-ness of `K` on the
group does NOT imply this integral is non-negative; the Peter–Weyl character
expansion of `K` and character orthogonality are needed to decompose the
integrand into `|Fourier coefficients|²`.  See `docs/gap_analysis.md` for the
full analysis.
-/

/-- **Clean factorization of the reflection-positivity integrand.**

`osG(U) · osG(θU) = f(U) · f(θU) · exp(-β S_W(U))`.

This is a purely algebraic identity: it follows from the reflection symmetries
`S⁺(θU) = S⁻(U)` and `S_int(θU) = S_int(U)`, together with the action
decomposition `S_W = S⁺ + S⁻ + S_int`.  No support hypothesis on `f` is needed. -/
lemma osG_thetaG_factorization
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    osG N T L β f U * osG N T L β f (reflectLinkVariable N U) =
    f U * f (reflectLinkVariable N U) *
    Real.exp (-β * wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U) := by
  unfold osG
  have h_pos_reflect : wilsonActionOSPositive N T L β (reflectLinkVariable N U) =
      wilsonActionOSNegative N T L β U :=
    (neg_action_reflection_os_periodic N T L β hT U).symm
  have h_int_reflect : wilsonActionOSInterface N T L β (reflectLinkVariable N U) =
      wilsonActionOSInterface N T L β U :=
    interface_action_reflection_symmetric_os_periodic N T L β hT U
  have h_total : wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U =
      wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U +
      wilsonActionOSInterface N T L β U :=
    total_decomposition_os_periodic N T L β U
  rw [h_pos_reflect, h_int_reflect, h_total]
  -- Split the RHS exp(-β*(S⁺+S⁻+S_int)) into a product of four exp's matching the LHS
  rw [show (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U +
      wilsonActionOSInterface N T L β U) : ℝ) =
      (-β * wilsonActionOSPositive N T L β U) + (-β * wilsonActionOSNegative N T L β U) +
      (-β * wilsonActionOSInterface N T L β U) by ring]
  rw [Real.exp_add, Real.exp_add]
  rw [show (-β * wilsonActionOSInterface N T L β U : ℝ) =
      (-β * wilsonActionOSInterface N T L β U / 2) + (-β * wilsonActionOSInterface N T L β U / 2)
      by ring]
  rw [Real.exp_add]
  ring

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
