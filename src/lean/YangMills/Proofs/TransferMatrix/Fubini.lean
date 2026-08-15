/-
# Transfer Matrix: Fubini Steps and Fourier Coefficients
-/

import YangMills.Proofs.TransferMatrix.Integrability

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
set_option maxHeartbeats 1000000 in
/-- **Step 4c (self-contained character expansion).** Combines
`transfer_matrix_fubini_character_expansion` (the Fubini + character-expansion exchange,
which takes `h_int` as a hypothesis) with
`transfer_matrix_fubini_integrability_self` (which discharges `h_int` from `hψ_int` plus
the strengthened Peter-Weyl axiom `h_meas`). The result is a single lemma whose only
hypotheses are the character-expansion data (`C`, `h_char`), the representation data
(`h_unitary`, `h_meas`), and `hψ_int` (integrability of the full Boltzmann-weighted
observable) — no `h_int` parameter remains. This is the self-contained pointwise
character-expansion identity that step 4d will integrate over `u`. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_character_expansion_self
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u) =
    Complex.ofReal (ψ u * Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)) *
    ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L V_plus
            (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
        ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
         (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
         star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))
      ∂ haarMeasurePositive N T L) := by
  exact transfer_matrix_fubini_character_expansion N T L β ψ u C ι dims ρ dual F h_char
    (transfer_matrix_fubini_integrability_self N T L β ψ u ι dims ρ h_unitary h_meas dual F hψ_int)

#print axioms transfer_matrix_fubini_character_expansion_self

set_option maxHeartbeats 1000000 in
/-- **Step 4d (pointwise separation in the integrand).** Applies
`charTripleProduct_separate` inside the V⁺ integral of
`transfer_matrix_fubini_character_expansion_self`, rewriting the character
triple product `Φ_w(U)·Ψ_w(U)·star(V_w(U))` (with `U = extendToFullConfig
(reflectPosToNeg V⁺) u`) as the separated product
`charFactorPos (restrictToPositive u) · charFactorInt (restrictToInterface u) ·
star (charFactorNeg (reflectPosToNeg V⁺))`. The three factors now depend on
disjoint variables: the positive part of `u`, the interface part of `u`, and
`V⁺` respectively. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_character_expansion_separated
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u) =
    Complex.ofReal (ψ u * Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)) *
    ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L V_plus
            (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
        (charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
         charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
         star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus)))
      ∂ haarMeasurePositive N T L) := by
  have h := transfer_matrix_fubini_character_expansion_self N T L β ψ u C ι dims ρ
    h_unitary h_meas dual F h_char hψ_int
  simp only [charTripleProduct_separate] at h
  exact h

#print axioms transfer_matrix_fubini_character_expansion_separated

set_option maxHeartbeats 1000000 in
/-- **Step 4d (pull V⁺-independent factors out of the V⁺ integral).** Starting from
`transfer_matrix_fubini_character_expansion_separated`, the factors
`charFactorPos (restrictToPositive u)` and `charFactorInt (restrictToInterface u)`
do not depend on the integration variable `V⁺`, so they are pulled out of the
V⁺ integral via `integral_const_mul` (after a pointwise `ring` rearrangement of
the integrand). The remaining V⁺ integral depends on `u` only through the
prefactor `Complex.ofReal (ψ(merge(V⁺, σ(u⁰))) · exp(…))` and the conjugated
negative factor `star (charFactorNeg (reflectPosToNeg V⁺))`. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_character_expansion_separated_pull
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u) =
    Complex.ofReal (ψ u * Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)) *
    ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
       charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
       ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
         Complex.ofReal (ψ (mergePosInterface N T L V_plus
             (sigmaInterface N T L (restrictToInterface N T L u))) *
           Real.exp (-β * osPositiveOfPosInterface N T L β
             (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
         star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
       ∂ haarMeasurePositive N T L)) := by
  have h := transfer_matrix_fubini_character_expansion_separated N T L β ψ u C ι dims ρ
    h_unitary h_meas dual F h_char hψ_int
  -- Step 1: rearrange integrand pointwise so the V⁺-independent factors are on the left
  have hpt : ∀ (w : InterfaceLink T L → ι)
      (Vp : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Complex.ofReal (ψ (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * osPositiveOfPosInterface N T L β
          (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
        (charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
         charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
         star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L Vp))) =
      charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
        charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
        (Complex.ofReal (ψ (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * osPositiveOfPosInterface N T L β
            (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
         star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L Vp))) := by
    intro w Vp; ring
  simp only [hpt] at h
  -- Step 2: pull the V⁺-independent constant out of the V⁺ integral
  have h_factor : ∀ (w : InterfaceLink T L → ι),
      ∫ (Vp : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
        charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
        (Complex.ofReal (ψ (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * osPositiveOfPosInterface N T L β
            (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
         star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L Vp)))
      ∂ haarMeasurePositive N T L =
      charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
        charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
        ∫ (Vp : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
          Complex.ofReal (ψ (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) *
            Real.exp (-β * osPositiveOfPosInterface N T L β
              (mergePosInterface N T L Vp (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
          star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L Vp))
        ∂ haarMeasurePositive N T L := by
    intro w; rw [integral_const_mul]
  simp only [h_factor] at h
  exact h

#print axioms transfer_matrix_fubini_character_expansion_separated_pull

set_option maxHeartbeats 1000000 in
/-- **Step 4d (integrate over u + change of variables).** Integrates the pointwise
identity `transfer_matrix_fubini_character_expansion_separated_pull` over `u`
w.r.t. `haarMeasurePosInterface`, coerces the LHS to ℂ via `integral_complex_ofReal`,
and performs the change of variables `u = mergePosInterface U⁺ u⁰` via
`MeasurableEmbedding.integral_map` (using `haarMeasurePosInterface_eq` =
`Measure.map (mergePosInterface) (μ⁺ × μ⁰)`). The restrict-after-merge lemmas
`restrictToPositive_mergePosInterface` / `restrictToInterface_mergePosInterface`
then simplify `charFactorPos (restrictToPositive (merge U⁺ u⁰)) = charFactorPos U⁺`
and `charFactorInt (restrictToInterface (merge U⁺ u⁰)) = charFactorInt u⁰`, and
the inner prefactor's `σ(restrictToInterface (merge U⁺ u⁰)) = σ(u⁰)`. The three
character factors now depend on disjoint variables `U⁺`, `u⁰`, `V⁺`.
0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_integrated
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (hψ_int : ∀ (u : PosInterfaceConfig N T L), Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    Complex.ofReal (∫ (u : PosInterfaceConfig N T L),
      ψ u * transferMatrixReflected N T L β ψ u ∂ haarMeasurePosInterface N T L) =
    ∫ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
        FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
      Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L x.1 x.2) / 2)) *
      ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
        (charFactorPos N T L ι dims ρ w x.1 *
         charFactorInt N T L ι dims ρ w x.2 *
         ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
           Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) *
             Real.exp (-β * osPositiveOfPosInterface N T L β
               (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) / 2)) *
           star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
         ∂ haarMeasurePositive N T L))
    ∂ (haarMeasurePositive N T L).prod (haarMeasureInterface N T L) := by
  -- Step 1: coerce LHS to a ℂ-valued integral
  have h_ofReal : (↑(∫ (u : PosInterfaceConfig N T L),
    ψ u * transferMatrixReflected N T L β ψ u ∂ haarMeasurePosInterface N T L) : ℂ) =
      ∫ (u : PosInterfaceConfig N T L),
        Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u)
        ∂ haarMeasurePosInterface N T L := (integral_complex_ofReal).symm
  rw [h_ofReal]
  -- Step 2: rewrite the integrand using the pointwise identity (Lemma 2)
  have h_pw : ∀ (u : PosInterfaceConfig N T L),
      Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u) =
      Complex.ofReal (ψ u * Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)) *
      ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
        (charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
         charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
         ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
           Complex.ofReal (ψ (mergePosInterface N T L V_plus
               (sigmaInterface N T L (restrictToInterface N T L u))) *
             Real.exp (-β * osPositiveOfPosInterface N T L β
               (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
           star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
         ∂ haarMeasurePositive N T L)) := by
    intro u; exact transfer_matrix_fubini_character_expansion_separated_pull N T L β ψ u C ι dims ρ
      h_unitary h_meas dual F h_char (hψ_int u)
  simp only [h_pw]
  -- Step 3: change of variables u = mergePosInterface U⁺ u⁰
  rw [haarMeasurePosInterface_eq]
  have hpi : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
  have h_merge_eq : Function.uncurry (mergePosInterface N T L) =
      productHaarMeasureUnionEquiv N hpi := by
    funext ⟨Uplus, Uzero⟩; funext idx
    obtain ⟨⟨n, μ⟩, hmem⟩ := idx
    rw [productHaarMeasureUnionEquiv_apply (N := N) hpi Uplus Uzero ⟨⟨n, μ⟩, hmem⟩]
    by_cases hpos : n ∈ positiveSites T L
    · simp only [Function.uncurry, mergePosInterface, dif_pos hpos]
    · simp only [Function.uncurry, mergePosInterface, dif_neg hpos]
  have hME : MeasurableEmbedding (Function.uncurry (mergePosInterface N T L)) := by
    rw [h_merge_eq]; exact (productHaarMeasureUnionEquiv N hpi).measurableEmbedding
  rw [hME.integral_map]
  -- Step 4: simplify restrict-after-merge + uncurry
  simp only [Function.uncurry, restrictToPositive_mergePosInterface,
    restrictToInterface_mergePosInterface]

#print axioms transfer_matrix_fubini_integrated



set_option maxHeartbeats 1000000 in
/-- **Step 4d (Fubini split: (U⁺, u⁰) → ∫_{u⁰} ∫_{U⁺}).** Applies `integral_prod_symm`
to the product-measure integral from `transfer_matrix_fubini_integrated` (Lemma 3),
splitting the `(U⁺, u⁰)` integral into an iterated integral `∫_{u⁰} ∫_{U⁺}` (outer `u⁰`
w.r.t. `μ⁰`, inner `U⁺` w.r.t. `μ⁺`).

The integrability hypothesis `h_int` (integrability of the ℂ-valued inner-product
integrand `Complex.ofReal (ψ u · (Tψ)(u))` w.r.t. `haarMeasurePosInterface`) is pushed
through the change of variables `u = mergePosInterface U⁺ u⁰` via
`MeasurePreserving.integrable_comp_emb` (giving `Integrable` of the pre-CoV integrand
w.r.t. `μ⁺.prod μ⁰`), then transferred to the RHS integrand `g_RHS` via the pointwise
identity (Lemma 2 + restrict-after-merge) and `Integrable.congr`. This `Integrable g_RHS
(μ⁺.prod μ⁰)` is the key input to `integral_prod_symm`. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_integrated_prod
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (hψ_int : ∀ (u : PosInterfaceConfig N T L), Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L))
    (h_int : Integrable
      (fun (u : PosInterfaceConfig N T L) =>
        Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u))
      (haarMeasurePosInterface N T L)) :
    Complex.ofReal (∫ (u : PosInterfaceConfig N T L),
      ψ u * transferMatrixReflected N T L β ψ u ∂ haarMeasurePosInterface N T L) =
    ∫ (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
      ∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
        ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (charFactorPos N T L ι dims ρ w Upos *
           charFactorInt N T L ι dims ρ w u0 *
           ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
             Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) *
               Real.exp (-β * osPositiveOfPosInterface N T L β
                 (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) / 2)) *
             star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
           ∂ haarMeasurePositive N T L))
      ∂ haarMeasurePositive N T L
    ∂ haarMeasureInterface N T L := by
  -- Step 1: Lemma 3 gives LHS = ∫_{(U⁺,u⁰)} g_RHS ∂(μ⁺.prod μ⁰)
  have h := transfer_matrix_fubini_integrated N T L β ψ C ι dims ρ h_unitary h_meas dual F
    h_char hψ_int
  -- Step 2: establish Integrable g_RHS (μ⁺.prod μ⁰) from h_int (from-LHS approach)
  have hpi : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
  have h_merge_eq : Function.uncurry (mergePosInterface N T L) =
      productHaarMeasureUnionEquiv N hpi := by
    funext ⟨Uplus, Uzero⟩; funext idx
    obtain ⟨⟨n, μ⟩, hmem⟩ := idx
    rw [productHaarMeasureUnionEquiv_apply (N := N) hpi Uplus Uzero ⟨⟨n, μ⟩, hmem⟩]
    by_cases hpos : n ∈ positiveSites T L
    · simp only [Function.uncurry, mergePosInterface, dif_pos hpos]
    · simp only [Function.uncurry, mergePosInterface, dif_neg hpos]
  have hME : MeasurableEmbedding (Function.uncurry (mergePosInterface N T L)) := by
    rw [h_merge_eq]; exact (productHaarMeasureUnionEquiv N hpi).measurableEmbedding
  haveI : IsFiniteMeasure (haarMeasureInterface N T L) :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (interfaceSites T L)
  haveI : IsFiniteMeasure (haarMeasurePositive N T L) :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (positiveSites T L)
  have hMP : MeasurePreserving (Function.uncurry (mergePosInterface N T L))
      ((haarMeasurePositive N T L).prod (haarMeasureInterface N T L))
      (haarMeasurePosInterface N T L) :=
    ⟨hME.measurable, (haarMeasurePosInterface_eq N T L).symm⟩
  -- Push h_int through the change of variables u = merge(U⁺, u⁰)
  have h_int' : Integrable
      (fun (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
          FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) =>
        Complex.ofReal (ψ (Function.uncurry (mergePosInterface N T L) x) *
          transferMatrixReflected N T L β ψ (Function.uncurry (mergePosInterface N T L) x)))
      ((haarMeasurePositive N T L).prod (haarMeasureInterface N T L)) :=
    hMP.integrable_comp_emb hME |>.mpr h_int
  -- Unfold Function.uncurry to merge x.1 x.2
  simp only [Function.uncurry] at h_int'
  -- Pointwise identity: Complex.ofReal (ψ (merge x) · Tψ (merge x)) = g_RHS(x)
  have h_eq : ∀ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
      FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
      Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
        transferMatrixReflected N T L β ψ (mergePosInterface N T L x.1 x.2)) =
      Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L x.1 x.2) / 2)) *
      ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
        (charFactorPos N T L ι dims ρ w x.1 *
         charFactorInt N T L ι dims ρ w x.2 *
         ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
           Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) *
             Real.exp (-β * osPositiveOfPosInterface N T L β
               (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) / 2)) *
           star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
         ∂ haarMeasurePositive N T L)) := by
    intro x
    have h_pw := transfer_matrix_fubini_character_expansion_separated_pull N T L β ψ
      (mergePosInterface N T L x.1 x.2) C ι dims ρ h_unitary h_meas dual F h_char
      (hψ_int (mergePosInterface N T L x.1 x.2))
    simp only [restrictToPositive_mergePosInterface, restrictToInterface_mergePosInterface] at h_pw
    exact h_pw
  -- Transfer integrability to g_RHS via Integrable.congr
  have h_g_int : Integrable
      (fun (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
          FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) =>
        Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L x.1 x.2) / 2)) *
        ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (charFactorPos N T L ι dims ρ w x.1 *
           charFactorInt N T L ι dims ρ w x.2 *
           ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
             Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) *
               Real.exp (-β * osPositiveOfPosInterface N T L β
                 (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) / 2)) *
             star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
           ∂ haarMeasurePositive N T L)))
      ((haarMeasurePositive N T L).prod (haarMeasureInterface N T L)) :=
    h_int'.congr (ae_of_all _ h_eq)
  -- Step 3: apply integral_prod_symm to split into ∫_{u⁰} ∫_{U⁺}
  have h_split := integral_prod_symm _ h_g_int
  rw [h_split] at h
  -- Step 4: g_RHS(⟨U⁺, u⁰⟩) is defeq to the explicit form (⟨·,·⟩.1/.2 reduce by rfl)
  exact h

#print axioms transfer_matrix_fubini_integrated_prod


/-- The positive Fourier coefficient `A_w(u⁰) = ∫_{U⁺} Complex.ofReal(ψ(merge(U⁺,u⁰))·
exp(-β·S⁺(merge(U⁺,u⁰))/2)) · charFactorPos(w, U⁺) ∂μ⁺`. This is the U⁺-dependent
factor that appears after pulling U⁺-independent constants out of the inner U⁺ integral
(step 4d Lemma 4b). -/
noncomputable def fourierCoeffPos (N T L : ℕ) [NeZero T] [NeZero L]
    (β : ℝ) (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) : ℂ :=
  ∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
      Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
    charFactorPos N T L ι dims ρ w Upos
  ∂ haarMeasurePositive N T L

#print axioms fourierCoeffPos

/-- **σ-invisibility of the positive Fourier coefficient (step 4 of the closure).**
When the test function `ψ = g_posInterface N T L hT β f` with `f` satisfying
`dependsOnlyOnPosSpatialInterface`, the positive Fourier coefficient
`A_w(u⁰) = fourierCoeffPos(w, u⁰)` is invisible to the σ twist on temporal
interface links: `A_w(σ(u⁰)) = A_w(u⁰)`.  This follows because the integrand
`g(merge(U⁺, u⁰))·exp(-β·S⁺(merge(U⁺, u⁰))/2)·charFactorPos(w, U⁺)` has its
`u⁰`-dependence only through `g` and `S⁺`, both of which are σ-invisible
(`g_posInterface_sigma_invisible` + `osPositiveOfPosInterface_sigma_invariant`),
while `charFactorPos` depends only on `U⁺`.  See §8.11.40 step 4. -/
lemma fourierCoeffPos_sigma_invisible (hT : Odd T)
    (β : ℝ) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffPos N T L β (g_posInterface N T L hT β f) ι dims ρ w
        (sigmaInterface N T L u0) =
    fourierCoeffPos N T L β (g_posInterface N T L hT β f) ι dims ρ w u0 := by
  have hpointwise : ∀ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Complex.ofReal (g_posInterface N T L hT β f (mergePosInterface N T L Upos (sigmaInterface N T L u0)) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos (sigmaInterface N T L u0)) / 2)) *
      charFactorPos N T L ι dims ρ w Upos =
      Complex.ofReal (g_posInterface N T L hT β f (mergePosInterface N T L Upos u0) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
      charFactorPos N T L ι dims ρ w Upos := by
    intro Upos
    rw [g_posInterface_sigma_invisible N T L β hT f hf Upos u0,
        osPositiveOfPosInterface_sigma_invariant N T L β hT Upos u0]
  unfold fourierCoeffPos
  exact integral_congr_ae (ae_of_all _ hpointwise)

#print axioms fourierCoeffPos_sigma_invisible

/-- **Step 5 sub-lemma 2: fourierCoeffPos is independent of u⁰_t.** When the test
function `ψ = g_posInterface N T L hT β f` with `f` satisfying
`dependsOnlyOnPosSpatialInterface`, the positive Fourier coefficient
`A_w(u⁰) = fourierCoeffPos(w, u⁰)` depends only on the spatial interface links
`u⁰_s` (μ ≠ 0), not on the temporal interface links `u⁰_t` (μ = 0).  This follows
because the integrand `g(merge(U⁺, u⁰))·exp(-β·S⁺(merge(U⁺, u⁰))/2)·charFactorPos(w, U⁺)`
has its `u⁰`-dependence only through `g` and `S⁺`, both of which are invisible to
changes in temporal interface links (`g_posInterface_temporal_invisible` +
`osPositiveOfPosInterface_temporal_invariant`), while `charFactorPos` depends only
on `U⁺`.  See §8.11.40 step 5.  This generalizes `fourierCoeffPos_sigma_invisible`
(which is the special case `u⁰' = σ(u⁰)`). -/
lemma fourierCoeffPos_independent_of_temporal (hT : Odd T)
    (β : ℝ) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (U_zero U_zero' : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (h_spatial : ∀ (n : PeriodicSite T L) (μ : Fin 4),
      (hn : n ∈ interfaceSites T L) → μ ≠ (0 : Fin 4) →
      U_zero ⟨(n, μ), hn⟩ = U_zero' ⟨(n, μ), hn⟩) :
    fourierCoeffPos N T L β (g_posInterface N T L hT β f) ι dims ρ w U_zero =
    fourierCoeffPos N T L β (g_posInterface N T L hT β f) ι dims ρ w U_zero' := by
  have hpointwise : ∀ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Complex.ofReal (g_posInterface N T L hT β f (mergePosInterface N T L Upos U_zero) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos U_zero) / 2)) *
      charFactorPos N T L ι dims ρ w Upos =
      Complex.ofReal (g_posInterface N T L hT β f (mergePosInterface N T L Upos U_zero') *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos U_zero') / 2)) *
      charFactorPos N T L ι dims ρ w Upos := by
    intro Upos
    rw [g_posInterface_temporal_invisible N T L β hT f hf Upos U_zero U_zero' h_spatial,
        osPositiveOfPosInterface_temporal_invariant N T L β hT Upos U_zero U_zero' h_spatial]
  unfold fourierCoeffPos
  exact integral_congr_ae (ae_of_all _ hpointwise)

#print axioms fourierCoeffPos_independent_of_temporal

/-- The negative Fourier coefficient `B_w(u⁰) = ∫_{V⁺} Complex.ofReal(ψ(merge(V⁺,σ(u⁰)))·
exp(-β·S⁺(merge(V⁺,σ(u⁰)))/2)) · star(charFactorNeg(dual w, reflectPosToNeg V⁺)) ∂μ⁺`.
This is the V⁺-dependent factor in the character triple product (step 4d). By the
σ-inversion property (lemma 3, `matrix_element_sigma_inversion`), `B_w(u⁰) = conj(A_w(σ(u⁰)))`. -/
noncomputable def fourierCoeffNeg (N T L : ℕ) [NeZero T] [NeZero L]
    (β : ℝ) (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) : ℂ :=
  ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) *
      Real.exp (-β * osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) / 2)) *
    star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
  ∂ haarMeasurePositive N T L

#print axioms fourierCoeffNeg

set_option maxHeartbeats 1000000 in
/-- **Step 4d (Lemma 4b: pull U⁺-independent constants out of the inner U⁺ integral).**
For a fixed interface configuration `u⁰`, the inner U⁺ integral
`∫_{U⁺} prefactor(U⁺,u⁰) · (C · ∑_w F(w) · (charFactorPos(U⁺) · charFactorInt(u⁰) · B_w(u⁰))) ∂μ⁺`
is rearranged to pull out the U⁺-independent constants `C`, `F(w)`, `charFactorInt(u⁰)`,
and `B_w(u⁰) = fourierCoeffNeg`, leaving
`C · ∑_w F(w) · (charFactorInt(u⁰) · B_w(u⁰) · A_w(u⁰))`
where `A_w(u⁰) = fourierCoeffPos = ∫_{U⁺} prefactor · charFactorPos(U⁺) ∂μ⁺`.

The proof inlines the Fubini exchange steps (pointwise `ring` rearrangement +
`Finset.mul_sum` → `integral_const_mul` pulls `C` out → `integral_finsetSum` exchanges
`∑_w` with `∫ U⁺` → `integral_const_mul` pulls each `F(w)` out), then rewrites each
remaining `∫ U⁺ prefactor · charFactorPos ∂μ⁺` as `fourierCoeffPos` via a per-`w`
identity (`ring` + `integral_const_mul` + `rfl`).

The per-`w` integrability hypothesis `h_int` (each term `(F w) · (prefactor ·
(charFactorPos · charFactorInt · B_w))` is integrable w.r.t. `μ⁺`) is taken as a
parameter — it will be discharged separately using character boundedness +
half-Boltzmann integrability (see design doc §8.11.10). 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_inner_pull
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_int : ∀ w : InterfaceLink T L → ι,
      Integrable (fun (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        (F w : ℂ) *
          (Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
            Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
           (charFactorPos N T L ι dims ρ w Upos *
            charFactorInt N T L ι dims ρ w u0 *
            fourierCoeffNeg N T L β ψ ι dims ρ dual w u0)))
        (haarMeasurePositive N T L)) :
    ∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
      ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
        (charFactorPos N T L ι dims ρ w Upos *
         charFactorInt N T L ι dims ρ w u0 *
         fourierCoeffNeg N T L β ψ ι dims ρ dual w u0))
    ∂ haarMeasurePositive N T L =
    (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (charFactorInt N T L ι dims ρ w u0 *
       fourierCoeffNeg N T L β ψ ι dims ρ dual w u0 *
       fourierCoeffPos N T L β ψ ι dims ρ w u0) := by
  -- Per-w identity: pull charFactorInt * fourierCoeffNeg out of the U⁺ integral
  have h_w : ∀ (w : InterfaceLink T L → ι),
      ∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
        (charFactorPos N T L ι dims ρ w Upos *
         charFactorInt N T L ι dims ρ w u0 *
         fourierCoeffNeg N T L β ψ ι dims ρ dual w u0)
      ∂ haarMeasurePositive N T L =
      charFactorInt N T L ι dims ρ w u0 *
      fourierCoeffNeg N T L β ψ ι dims ρ dual w u0 *
      fourierCoeffPos N T L β ψ ι dims ρ w u0 := by
    intro w
    have hpt : ∀ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
        (charFactorPos N T L ι dims ρ w Upos *
         charFactorInt N T L ι dims ρ w u0 *
         fourierCoeffNeg N T L β ψ ι dims ρ dual w u0) =
        (charFactorInt N T L ι dims ρ w u0 *
         fourierCoeffNeg N T L β ψ ι dims ρ dual w u0) *
        (Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
         charFactorPos N T L ι dims ρ w Upos) := by
      intro Upos; ring
    rw [show (∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
        (charFactorPos N T L ι dims ρ w Upos *
         charFactorInt N T L ι dims ρ w u0 *
         fourierCoeffNeg N T L β ψ ι dims ρ dual w u0)
      ∂ haarMeasurePositive N T L) =
      (∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        (charFactorInt N T L ι dims ρ w u0 *
         fourierCoeffNeg N T L β ψ ι dims ρ dual w u0) *
        (Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
         charFactorPos N T L ι dims ρ w Upos)
      ∂ haarMeasurePositive N T L) from by
      congr 1; funext Upos; exact hpt Upos]
    rw [integral_const_mul]
    rfl
  -- Step 1: pointwise rearrange: A * (C * ∑ w, F w * X) = C * ∑ w, F w * (A * X)
  simp only [show ∀ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
      Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
    ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (charFactorPos N T L ι dims ρ w Upos *
       charFactorInt N T L ι dims ρ w u0 *
       fourierCoeffNeg N T L β ψ ι dims ρ dual w u0)) =
    (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
      (charFactorPos N T L ι dims ρ w Upos *
       charFactorInt N T L ι dims ρ w u0 *
       fourierCoeffNeg N T L β ψ ι dims ρ dual w u0))
    from fun Upos => by
      rw [← mul_assoc, mul_comm _ (C : ℂ), mul_assoc, Finset.mul_sum]
      refine congrArg ((C : ℂ) * ·) (Finset.sum_congr rfl (fun w _ => by ring))]
  -- Step 2: pull C out of the integral
  rw [integral_const_mul]
  -- Step 3: exchange the finite sum with the integral
  rw [integral_finsetSum Finset.univ]
  · -- Step 4: pull each (F w) out of its integral
    simp only [integral_const_mul]
    -- Step 5: rewrite each integral using h_w (pull out charFactorInt * fourierCoeffNeg)
    refine congrArg ((C : ℂ) * ·) ?_
    exact Finset.sum_congr rfl (fun w hw => by rw [h_w w])
  · exact fun w _ => h_int w

#print axioms transfer_matrix_fubini_inner_pull

set_option maxHeartbeats 1000000 in
/-- **Step 4e (integrate over u⁰: pull U⁺-independent constants out of the (U⁺, u⁰) integral).**
Starting from `transfer_matrix_fubini_integrated` (Lemma 3, product-measure integral), this
rearranges the integrand pointwise to group the u⁰-dependent factors `(charFactorInt · B_w)` with
the constant `F w`, pulls `C` out of the product-measure integral, exchanges the finite sum `∑_w`
with the integral (Fubini), then for each `w` splits the `(U⁺, u⁰)` product integral into an
iterated integral `∫_{u⁰} ∫_{U⁺}` via `integral_prod_symm`, pulls the u⁰-dependent constant
`(F w) · (charFactorInt · B_w)` out of the inner `U⁺` integral (recognizing `fourierCoeffPos`),
pulls `F w` out of the outer `u⁰` integral (recognizing `fourierCoeffNeg`), producing
`C · ∑_w (F w) · ∫_{u⁰} charFactorInt · fourierCoeffNeg · fourierCoeffPos ∂μ⁰`.

The per-`w` integrability hypothesis `h_int` (each term is integrable w.r.t. `μ⁺.prod μ⁰`) is
taken as a parameter. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_integrated_pull
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (hψ_int : ∀ (u : PosInterfaceConfig N T L), Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L))
    (h_int : ∀ w : InterfaceLink T L → ι,
      Integrable (fun (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
          FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) =>
        (F w : ℂ) *
          (charFactorInt N T L ι dims ρ w x.2 *
           fourierCoeffNeg N T L β ψ ι dims ρ dual w x.2) *
          (Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
            Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L x.1 x.2) / 2)) *
           charFactorPos N T L ι dims ρ w x.1))
        ((haarMeasurePositive N T L).prod (haarMeasureInterface N T L))) :
    Complex.ofReal (∫ (u : PosInterfaceConfig N T L),
      ψ u * transferMatrixReflected N T L β ψ u ∂ haarMeasurePosInterface N T L) =
    (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      ∫ (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
        charFactorInt N T L ι dims ρ w u0 *
        fourierCoeffNeg N T L β ψ ι dims ρ dual w u0 *
        fourierCoeffPos N T L β ψ ι dims ρ w u0
      ∂ haarMeasureInterface N T L := by
  -- Per-w iterated identity (projection-free): split + pull constants + recognize
  have h_w_iter : ∀ (w : InterfaceLink T L → ι),
      ∫ (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
        ∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
          (F w : ℂ) *
            (charFactorInt N T L ι dims ρ w u0 *
             ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
               Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) *
                 Real.exp (-β * osPositiveOfPosInterface N T L β
                   (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) / 2)) *
               star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
             ∂ haarMeasurePositive N T L) *
            (Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
              Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
             charFactorPos N T L ι dims ρ w Upos)
        ∂ haarMeasurePositive N T L
      ∂ haarMeasureInterface N T L =
      (F w : ℂ) *
        ∫ (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
          charFactorInt N T L ι dims ρ w u0 *
          fourierCoeffNeg N T L β ψ ι dims ρ dual w u0 *
          fourierCoeffPos N T L β ψ ι dims ρ w u0
        ∂ haarMeasureInterface N T L := by
    intro w
    simp only [mul_assoc, integral_const_mul]
    rfl
  -- Step 1: Lemma 3 gives LHS = ∫_{(U⁺,u⁰)} g_RHS ∂(μ⁺.prod μ⁰)
  have h := transfer_matrix_fubini_integrated N T L β ψ C ι dims ρ h_unitary h_meas dual F
    h_char hψ_int
  rw [h]
  -- Step 2: IsFiniteMeasure instances (needed for integral_prod_symm)
  haveI : IsFiniteMeasure (haarMeasureInterface N T L) :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (interfaceSites T L)
  haveI : IsFiniteMeasure (haarMeasurePositive N T L) :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (positiveSites T L)
  -- Step 3: pointwise rearrange the integrand:
  --   prefactor * (C * ∑ w, F * (Φ * Ψ * B)) = C * ∑ w, F * (Ψ * B) * (prefactor * Φ)
  rw [show (∫ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
        FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
          Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L x.1 x.2) / 2)) *
        ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (charFactorPos N T L ι dims ρ w x.1 *
           charFactorInt N T L ι dims ρ w x.2 *
           ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
             Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) *
               Real.exp (-β * osPositiveOfPosInterface N T L β
                 (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) / 2)) *
             star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
           ∂ haarMeasurePositive N T L))
      ∂ (haarMeasurePositive N T L).prod (haarMeasureInterface N T L)) =
      (∫ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
        FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (charFactorInt N T L ι dims ρ w x.2 *
           ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
             Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) *
               Real.exp (-β * osPositiveOfPosInterface N T L β
                 (mergePosInterface N T L V_plus (sigmaInterface N T L x.2)) / 2)) *
             star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus))
           ∂ haarMeasurePositive N T L) *
          (Complex.ofReal (ψ (mergePosInterface N T L x.1 x.2) *
            Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L x.1 x.2) / 2)) *
           charFactorPos N T L ι dims ρ w x.1)
      ∂ (haarMeasurePositive N T L).prod (haarMeasureInterface N T L)) from by
    congr 1; funext x
    rw [← mul_assoc, mul_comm _ (C : ℂ), mul_assoc, Finset.mul_sum]
    refine congrArg ((C : ℂ) * ·) (Finset.sum_congr rfl (fun w _ => by ring))]
  -- Step 4: pull C out of the product-measure integral
  rw [integral_const_mul]
  -- Step 5: exchange the finite sum ∑_w with the integral
  rw [integral_finsetSum Finset.univ]
  · -- Step 6: per-w rewrite via integral_prod_symm + h_w_iter (defeq handles projections)
    refine congrArg ((C : ℂ) * ·) ?_
    exact Finset.sum_congr rfl (fun w hw => by
      rw [integral_prod_symm]
      · exact h_w_iter w
      · exact h_int w)
  · -- integrability side goal (h_int uses fourierCoeffNeg, defeq to B_w_inline)
    exact fun w hw => h_int w

#print axioms transfer_matrix_fubini_integrated_pull

