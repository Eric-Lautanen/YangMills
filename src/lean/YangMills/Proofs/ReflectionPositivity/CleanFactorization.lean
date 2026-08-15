/-
# Reflection Positivity: Clean Factorization and PD-Structure Obstruction
-/

import YangMills.Proofs.ReflectionPositivity.GaugeInvariance

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
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

/-- **Step 2: Pointwise character expansion of the reflection-positivity integrand.**

Substituting the character expansion of `exp(-β·S_int)` (from
`interface_boltzmann_character_expansion`) into the factorization
`osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_pos)·exp(-β·S_neg)·exp(-β·S_int)`
(from `osG_thetaG_factorization` + `total_decomposition_os_periodic`), the
integrand admits the pointwise expansion (viewed in ℂ)

    (osG(U)·osG(θU) : ℂ) = (C : ℂ) · ∑_w (F w : ℂ) · ↑r(U) · Φ_w(U) · Ψ_w(U) · V_w(U)

with `C > 0`, `F(w) ≥ 0`, and `r(U) = f(U)·f(θU)·exp(-β·S_pos(U))·exp(-β·S_neg(U))`
(the real prefactor from the positive and negative bulk actions).  The
character factors `Φ_w`, `Ψ_w`, `V_w` are the same as in
`interface_boltzmann_character_expansion`.  This is step 2 of the formalization
path in §8.11.53.  Pure algebra — 0 sorries, uses `peterWeyl_clebschGordan_plaquette`
(axiom count 6, unchanged). -/
lemma osG_thetaG_eq_char_expansion_pointwise
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T) (hN : 1 ≤ N)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) :
    ∃ (C : ℝ) (hC : 0 < C)
      (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : (InterfaceLink T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      (osG N T L β f U * osG N T L β f (reflectLinkVariable N U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          ↑(f U * f (reflectLinkVariable N U) *
            Real.exp (-β * wilsonActionOSPositive N T L β U) *
            Real.exp (-β * wilsonActionOSNegative N T L β U)) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)) := by
  -- Obtain the character-expansion data (C, ι, ρ, dual, F) from the interface Boltzmann factor.
  obtain ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, h_char⟩ :=
    interface_boltzmann_character_expansion N T L β hN
  letI : Fintype ι := hι
  classical
  refine ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  -- Factor osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_W(U)) and decompose S_W = S_pos + S_neg + S_int.
  have h_factor := osG_thetaG_factorization N T L β hT f U
  have h_total := total_decomposition_os_periodic N T L β U
  -- Sub-lemma: the LHS as a complex number, with exp(-β·S_int) split out from the real prefactor.
  have h_LHS : (osG N T L β f U * osG N T L β f (reflectLinkVariable N U) : ℂ) =
      ↑(f U * f (reflectLinkVariable N U) *
        Real.exp (-β * wilsonActionOSPositive N T L β U) *
        Real.exp (-β * wilsonActionOSNegative N T L β U)) *
        (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) := by
    -- Combine ↑(osG U) * ↑(osG θU) = ↑(osG U * osG θU), then factor and decompose.
    rw [← Complex.ofReal_mul, h_factor, h_total]
    -- Distribute -β over the sum of three actions.
    have h_dist : (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U +
        wilsonActionOSInterface N T L β U) : ℝ) =
        (-β * wilsonActionOSPositive N T L β U) + (-β * wilsonActionOSNegative N T L β U) +
        (-β * wilsonActionOSInterface N T L β U) := by ring
    rw [h_dist, Real.exp_add, Real.exp_add]
    -- Rearrange in ℝ: f·f·(exp_pos·(exp_neg·exp_int)) = (f·f·exp_pos·exp_neg)·exp_int.
    have h_rearrange :
        f U * f (reflectLinkVariable N U) *
          (Real.exp (-β * wilsonActionOSPositive N T L β U) *
            Real.exp (-β * wilsonActionOSNegative N T L β U) *
            Real.exp (-β * wilsonActionOSInterface N T L β U)) =
        (f U * f (reflectLinkVariable N U) *
          Real.exp (-β * wilsonActionOSPositive N T L β U) *
          Real.exp (-β * wilsonActionOSNegative N T L β U)) *
        Real.exp (-β * wilsonActionOSInterface N T L β U) := by ring
    -- Rearrange LHS, then combine RHS coercions to match.
    rw [h_rearrange, ← Complex.ofReal_mul]
  -- Substitute the character expansion for exp(-β·S_int) and distribute the real prefactor.
  rw [h_LHS, h_char U]
  set r := f U * f (reflectLinkVariable N U) *
    Real.exp (-β * wilsonActionOSPositive N T L β U) *
    Real.exp (-β * wilsonActionOSNegative N T L β U)
  -- Distribute C and ↑r into the sums on both sides, then match per-weight.
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  -- Per-weight: ↑r · (C · (F · Φ · Ψ · V)) = C · (F · ↑r · Φ · Ψ · V) (commutativity).
  ring

#print axioms osG_thetaG_eq_char_expansion_pointwise
#print axioms osG_thetaG_eq_char_expansion_pointwise

/-- **Step 2 (full): Pointwise character expansion of the reflection-positivity
integrand using the FULL Boltzmann factor.**

Substituting the FULL character expansion of `exp(-β·S_W)` (from
`full_boltzmann_character_expansion`) into the factorization
`osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_W(U))` (from `osG_thetaG_factorization`),
the integrand admits the pointwise expansion (viewed in ℂ)

    (osG(U)·osG(θU) : ℂ) = (C : ℂ) · ∑_w (F w : ℂ) · ↑(f(U)·f(θU)) · Φ_w(U) · Ψ_w(U) · V_w(U)

with `C > 0`, `F(w) ≥ 0`, and the character factors `Φ_w`, `Ψ_w`, `V_w` ranging
over ALL links (`allLinkPos`/`allLinkInt`/`allLinkNeg`).  This is the full-lattice
analogue of `osG_thetaG_eq_char_expansion_pointwise` (which expands only the
interface Boltzmann factor).  The real prefactor is just `f(U)·f(θU)` (no bulk
action factors, since the FULL Boltzmann is expanded).  Uses
`peterWeyl_clebschGordan_plaquette` (axiom count 6, unchanged); 0 sorries. -/
lemma full_osG_thetaG_eq_char_expansion_pointwise
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T) (hN : 1 ≤ N)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) :
    ∃ (C : ℝ) (hC : 0 < C)
      (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : ((PeriodicSite T L × Fin 4) → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      (osG N T L β f U * osG N T L β f (reflectLinkVariable N U) : ℂ) =
        (C : ℂ) * ∑ w : (PeriodicSite T L × Fin 4) → ι, (F w : ℂ) *
          ↑(f U * f (reflectLinkVariable N U)) *
          (∏ l ∈ allLinkPos T L, repCharacter (ρ (w l)) (U.value l.1 l.2)) *
          (∏ l ∈ allLinkInt T L, repCharacter (ρ (w l)) (U.value l.1 l.2)) *
          star (∏ l ∈ allLinkNeg T L, repCharacter (ρ (dual (w l))) (U.value l.1 l.2)) := by
  -- Obtain the full character-expansion data (C, ι, ρ, dual, F) from the full Boltzmann factor.
  obtain ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, h_char⟩ :=
    full_boltzmann_character_expansion N T L β hN
  letI : Fintype ι := hι
  classical
  refine ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  -- Factor osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_W(U)).
  have h_factor := osG_thetaG_factorization N T L β hT f U
  -- Sub-lemma: the LHS as a complex number, with exp(-β·S_W) split out from the real prefactor.
  have h_LHS : (osG N T L β f U * osG N T L β f (reflectLinkVariable N U) : ℂ) =
      ↑(f U * f (reflectLinkVariable N U)) *
        (Real.exp (-β * wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U) : ℂ) := by
    rw [← Complex.ofReal_mul, h_factor, Complex.ofReal_mul]
  -- Substitute the full character expansion for exp(-β·S_W) and distribute the real prefactor.
  rw [h_LHS, h_char U]
  set r := f U * f (reflectLinkVariable N U)
  -- Distribute C and ↑r into the sums on both sides, then match per-weight.
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  -- Per-weight: ↑r · (C · (F · Φ · Ψ · V)) = C · (F · ↑r · Φ · Ψ · V) (commutativity).
  ring

#print axioms full_osG_thetaG_eq_char_expansion_pointwise

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
  /-- Reflection positivity: if f depends only on positive + spatial-interface links, then ⟨f · θ(f)⟩ ≥ 0. -/
  reflectionPositive : ∀ (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ),
    dependsOnlyOnPosSpatialInterface N T L f →
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
and **spatial** interface (time-0) regions.  Temporal interface links (μ=0 at t=0)
are excluded: they are integrated out as part of the transfer matrix kernel
(Lüscher decomposition), avoiding the σ-twist obstacle.  This is the content of
the Osterwalder-Seiler theorem.
-/
theorem lattice_ym_reflection_positive_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hβ : β > 0) (hT : Odd T) :
    ∀ (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ),
      dependsOnlyOnPosSpatialInterface N T L f →
      (wilsonPeriodicExpectation N T L β hT).evaluate (λ U => f U * reflectObservable N f U) ≥ 0 := by
  intro f hf_supported
  exact (wilsonPeriodicExpectation N T L β hT).reflectionPositive f hf_supported

#print axioms lattice_ym_reflection_positive_periodic

