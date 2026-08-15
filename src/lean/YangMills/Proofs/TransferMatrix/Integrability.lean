/-
# Transfer Matrix: Integrability Discharge
-/

import YangMills.Proofs.TransferMatrix.Bridge

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
/-! ## Integrability discharge: character-product norm bounds

These helper lemmas bound the norm of the character products
`Φ_w(U)`, `Ψ_w(U)`, `V_w(U)` (and their triple product) that appear in the
`h_int` integrability hypothesis of `transfer_matrix_fubini_character_expansion`.
They are pure norm inequalities (no measurability, no integrability) and depend
only on `repCharacter_norm_le_dim` (character boundedness) and the
`NormedCommRing` structure of `ℂ`.  0 sorries, 0 custom axioms. -/

/-- A finite product of characters is bounded by the product of the dimensions:
`‖∏ l ∈ s, χ_{w l}(g_l)‖ ≤ ∏ l ∈ s, dim(w l)`.  Uses `Finset.norm_prod_le`
(product-of-norms bound for `NormedCommRing`) and `repCharacter_norm_le_dim`
(each character bounded by its dimension).  0 sorries, 0 custom axioms. -/
lemma charProduct_norm_le
    (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (s : Finset (InterfaceLink T L)) (w : InterfaceLink T L → ι)
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    ‖∏ l ∈ s, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)‖ ≤
      ∏ l ∈ s, (dims (w l) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hdim := repCharacter_norm_le_dim (ρ (w a)) (h_unitary (w a))
      (interfaceLinkVar N T L U a)
    calc ‖repCharacter (ρ (w a)) (interfaceLinkVar N T L U a) *
          ∏ l ∈ s, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)‖
        = ‖repCharacter (ρ (w a)) (interfaceLinkVar N T L U a)‖ *
          ‖∏ l ∈ s, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)‖ := Complex.norm_mul _ _
      _ ≤ (dims (w a) : ℝ) * ∏ l ∈ s, (dims (w l) : ℝ) :=
        mul_le_mul hdim ih (norm_nonneg _) (Nat.cast_nonneg _)

#print axioms charProduct_norm_le

set_option maxHeartbeats 1000000 in
/-- The triple character product `Φ_w(U)·Ψ_w(U)·V_w(U)` (positive-time, interface,
and conjugated negative-time character products) is bounded by the product of the
corresponding dimension-products.  This is the uniform-in-`U` bound `M_w` needed
for the domination argument in the integrability discharge (design doc §8.11.10):
`‖Φ_w(U)·Ψ_w(U)·V_w(U)‖ ≤ M_w` where `M_w` is independent of `U` (hence of `V⁺`).
Uses `charProduct_norm_le` (three times), `Complex.norm_mul` (equality), and
`norm_star` (`‖star z‖ = ‖z‖` via the `CStarRing`/`NormedStarGroup` structure of
`ℂ`).  0 sorries, 0 custom axioms. -/
lemma charTripleProduct_norm_le
    (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    ‖(∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
      (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
      star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l))‖ ≤
    (∏ l ∈ interfaceLinkPos T L, (dims (w l) : ℝ)) *
      (∏ l ∈ interfaceLinkInt T L, (dims (w l) : ℝ)) *
      (∏ l ∈ interfaceLinkNeg T L, (dims (dual (w l)) : ℝ)) := by
  set Φ := ∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)
  set Ψ := ∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)
  set Χ := ∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)
  have hΦ : ‖Φ‖ ≤ ∏ l ∈ interfaceLinkPos T L, (dims (w l) : ℝ) :=
    charProduct_norm_le N T L ι dims ρ h_unitary _ w U
  have hΨ : ‖Ψ‖ ≤ ∏ l ∈ interfaceLinkInt T L, (dims (w l) : ℝ) :=
    charProduct_norm_le N T L ι dims ρ h_unitary _ w U
  have hΧ : ‖Χ‖ ≤ ∏ l ∈ interfaceLinkNeg T L, (dims (dual (w l)) : ℝ) :=
    charProduct_norm_le N T L ι dims ρ h_unitary _ (fun l => dual (w l)) U
  -- ‖(Φ * Ψ) * star Χ‖ = ‖Φ * Ψ‖ * ‖star Χ‖ = (‖Φ‖ * ‖Ψ‖) * ‖Χ‖
  have h_eq : ‖(Φ * Ψ) * star Χ‖ = (‖Φ‖ * ‖Ψ‖) * ‖Χ‖ := by
    rw [Complex.norm_mul, Complex.norm_mul, norm_star]
  rw [h_eq]
  gcongr <;> positivity

#print axioms charTripleProduct_norm_le

set_option maxHeartbeats 1000000 in
/-- **Step 4c integrability discharge (domination argument).** Discharges the
`h_int` integrability hypothesis of `transfer_matrix_fubini_character_expansion`
using the domination `‖integrand_w(V⁺)‖ ≤ K_w · |full(V⁺)|`, where
`K_w = |F w| · M_w / (c_u · m)` is a constant (independent of `V⁺`), `M_w` is the
character-product norm bound (`charTripleProduct_norm_le`), `c_u = exp(-β·S⁺(u)/2) > 0`,
and `m = exp(-|β|·C) > 0` is the uniform lower bound on `exp(-β·S_int(U))`
(`exp_neg_beta_wilsonActionOSInterface_lower_bound`). The dominator `K_w · |full|`
is integrable via `Integrable.norm` + `Integrable.const_mul` from `hψ_int`, and
`Integrable.mono'` closes the goal. The `AEStronglyMeasurable` hypothesis
`h_integrand_ae` is taken as a parameter (to be discharged separately via
measurability of the component functions + axiom strengthening). 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_integrability
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L))
    (h_integrand_ae : ∀ w : InterfaceLink T L → ι,
      AEStronglyMeasurable (fun V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) =>
        (F w : ℂ) *
          (Complex.ofReal (ψ (mergePosInterface N T L V_plus
              (sigmaInterface N T L (restrictToInterface N T L u))) *
            Real.exp (-β * osPositiveOfPosInterface N T L β
              (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
          ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))))
        (haarMeasurePositive N T L)) :
    ∀ w : InterfaceLink T L → ι,
      Integrable (fun V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) =>
        (F w : ℂ) *
          (Complex.ofReal (ψ (mergePosInterface N T L V_plus
              (sigmaInterface N T L (restrictToInterface N T L u))) *
            Real.exp (-β * osPositiveOfPosInterface N T L β
              (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
          ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))))
        (haarMeasurePositive N T L) := by
  intro w
  -- Constants for the domination bound
  set c_u := Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)
  set m := Real.exp (-|β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|))
  set M_w := (∏ l ∈ interfaceLinkPos T L, (dims (w l) : ℝ)) *
    (∏ l ∈ interfaceLinkInt T L, (dims (w l) : ℝ)) *
    (∏ l ∈ interfaceLinkNeg T L, (dims (dual (w l)) : ℝ))
  set K_w := |F w| * M_w / (c_u * m)
  -- Pointwise domination: ‖integrand_w(V⁺)‖ ≤ K_w * |full(V⁺)|
  have h_bound : ∀ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    ‖(F w : ℂ) *
      (Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
      ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
       (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
       star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l))))‖ ≤
    K_w * |ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))| := by
    intro V_plus
    set merge := mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))
    set U := extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u
    -- Character triple product bound: ‖B‖ ≤ M_w
    have hB : ‖((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
        (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
        star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))‖ ≤
        M_w :=
      charTripleProduct_norm_le N T L ι dims ρ h_unitary dual w U
    -- ‖(F w : ℂ)‖ = |F w|
    have hFw : ‖(F w : ℂ)‖ = |F w| := RCLike.norm_ofReal (F w)
    -- ‖A‖ = |ψ merge| * exp(-β * S⁺(merge)/2)
    have hA : ‖Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))‖ =
        |ψ merge| * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2) := by
      have h := @RCLike.norm_ofReal ℂ _ (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))
      exact h.trans (by rw [abs_mul, Real.abs_exp])
    -- exp(-β * S_int(U)) ≥ m
    have h_e_int : m ≤ Real.exp (-β * wilsonActionOSInterface N T L β U) :=
      exp_neg_beta_wilsonActionOSInterface_lower_bound N T L β U
    -- Positivity
    have h_c_u_pos : 0 < c_u := Real.exp_pos _
    have h_m_pos : 0 < m := Real.exp_pos _
    -- |full| = |ψ merge| * c_u * exp(-β * S⁺(merge)/2) * exp(-β * S_int(U))
    have hfull : |ψ merge * Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U))| =
        |ψ merge| * c_u * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2) *
        Real.exp (-β * wilsonActionOSInterface N T L β U) := by
      rw [abs_mul, Real.abs_exp]
      have h_arg : -β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U) =
        (-β * osPositiveOfPosInterface N T L β u / 2) +
        (-β * osPositiveOfPosInterface N T L β merge / 2) +
        (-β * wilsonActionOSInterface N T L β U) := by ring
      rw [h_arg, Real.exp_add, Real.exp_add]
      rw [show Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) = c_u from rfl]
      ring
    -- |full| = ‖A‖ * (c_u * exp(-β * S_int(U)))
    have hfull_eq : |ψ merge * Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U))| =
        ‖Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))‖ *
        (c_u * Real.exp (-β * wilsonActionOSInterface N T L β U)) := by
      rw [hA, hfull]; ring
    -- ‖A‖ ≤ |full| / (c_u * m)
    have hA_le : ‖Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))‖ ≤
        |ψ merge * Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U))| / (c_u * m) := by
      rw [hfull_eq, le_div_iff₀ (mul_pos h_c_u_pos h_m_pos)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_e_int h_c_u_pos.le) (norm_nonneg _)
    -- Main bound via calc
    calc ‖(F w : ℂ) *
        (Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2)) *
        ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
         (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
         star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l))))‖
        = |F w| * (‖Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))‖ *
          ‖((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
           (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
           star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))‖) := by
          rw [Complex.norm_mul, Complex.norm_mul, hFw]
      _ ≤ |F w| * (‖Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))‖ * M_w) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (norm_nonneg _)) (abs_nonneg _)
      _ = |F w| * M_w * ‖Complex.ofReal (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2))‖ := by ring
      _ ≤ |F w| * M_w * (|ψ merge * Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U))| / (c_u * m)) := by
          exact mul_le_mul_of_nonneg_left hA_le (by positivity)
      _ = K_w * |ψ merge * Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U))| := by
          rw [show K_w = |F w| * M_w / (c_u * m) from rfl]; ring
  -- Dominator integrability: K_w * |full| is integrable
  have h_dom : Integrable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
    K_w * |ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))|)
    (haarMeasurePositive N T L) := by
    exact Integrable.smul K_w (Integrable.norm hψ_int)
  -- Apply Integrable.mono'
  exact Integrable.mono' h_dom (h_integrand_ae w) (ae_of_all (haarMeasurePositive N T L) h_bound)

#print axioms transfer_matrix_fubini_integrability

/-- **Step 4a of the Fubini reduction (sub-step (iii) of Lemma 2).** The transfer
matrix inner product `∫_{u} g(u)·(Tg)(u) dμ⁺⁰(u)`, coerced to `ℂ`, equals the
`ℂ`-valued integral over the product measure `μ⁺ × μ⁰` (via `haarMeasurePosInterface_eq`
and `MeasurableEmbedding.integral_map`). This is the first step of the Fubini
reduction: coercing the `ℝ`-valued inner product to `ℂ` (so the character expansion
can be substituted) and applying the measure factorization that converts the
`μ⁺⁰` integral to a `(U⁺, u⁰)` product-measure integral. 0 sorries, 0 custom axioms. -/
lemma inner_product_complex_eq_product_integral
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) :
    (↑(∫ (u : PosInterfaceConfig N T L),
      g_posInterface N T L hT β f u * transferMatrixReflected N T L β (g_posInterface N T L hT β f) u
      ∂ haarMeasurePosInterface N T L) : ℂ) =
    ∫ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
        FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
      Complex.ofReal (g_posInterface N T L hT β f (Function.uncurry (mergePosInterface N T L) x) *
        transferMatrixReflected N T L β (g_posInterface N T L hT β f)
          (Function.uncurry (mergePosInterface N T L) x))
      ∂ (haarMeasurePositive N T L).prod (haarMeasureInterface N T L) := by
  -- Step 1: coerce to ℂ (integral_complex_ofReal: ∫ (Complex.ofReal ∘ f) = ↑(∫ f))
  -- Use `Complex.ofReal` explicitly (not `(... : ℂ)`) to keep the coercion on the whole
  -- product, matching `integral_complex_ofReal`. The `(... : ℂ)` annotation distributes
  -- the coercion over `*`, giving `↑a * ↑b` instead of `↑(a * b)`.
  have h_ofReal : (↑(∫ (u : PosInterfaceConfig N T L),
    g_posInterface N T L hT β f u * transferMatrixReflected N T L β (g_posInterface N T L hT β f) u
    ∂ haarMeasurePosInterface N T L) : ℂ) =
    ∫ (u : PosInterfaceConfig N T L),
      Complex.ofReal (g_posInterface N T L hT β f u * transferMatrixReflected N T L β (g_posInterface N T L hT β f) u)
      ∂ haarMeasurePosInterface N T L := (integral_complex_ofReal).symm
  rw [h_ofReal]
  -- Step 2: use haarMeasurePosInterface_eq (μ⁺⁰ = map merge (μ⁺ × μ⁰))
  rw [haarMeasurePosInterface_eq]
  -- Step 3: set up MeasurableEmbedding for mergePosInterface
  have hpi : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
  have h_merge_eq : Function.uncurry (mergePosInterface N T L) = productHaarMeasureUnionEquiv N hpi := by
    funext ⟨Uplus, Uzero⟩
    funext idx
    obtain ⟨⟨n, μ⟩, hmem⟩ := idx
    rw [productHaarMeasureUnionEquiv_apply (N := N) hpi Uplus Uzero ⟨⟨n, μ⟩, hmem⟩]
    by_cases hpos : n ∈ positiveSites T L
    · simp only [Function.uncurry, mergePosInterface, dif_pos hpos]
    · simp only [Function.uncurry, mergePosInterface, dif_neg hpos]
  have hME : MeasurableEmbedding (Function.uncurry (mergePosInterface N T L)) := by
    rw [h_merge_eq]; exact (productHaarMeasureUnionEquiv N hpi).measurableEmbedding
  -- Step 4: use MeasurableEmbedding.integral_map to convert ∫_u to ∫_{(U⁺, u⁰)}
  exact hME.integral_map (fun u =>
    Complex.ofReal (g_posInterface N T L hT β f u * transferMatrixReflected N T L β (g_posInterface N T L hT β f) u))

#print axioms inner_product_complex_eq_product_integral

lemma G_thetaG_factorization (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)

    (hf_supported : dependsOnlyOnPosInterface N T L f) (U : LinkVariable (SU N) (PeriodicSite T L)) :

    G N T L hT β f U * G N T L hT β f (reflectLinkVariable N U) =

    g_posInterface N T L hT β f (restrictPosInterface N T L

      (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)) *

    g_posInterface N T L hT β f (reflectToPosInterface N T L

      (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

      (restrictToInterface N T L (restrictPosInterface N T L

        (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)))) *

    Real.exp (-β * (osPositiveOfPosInterface N T L β

                      (restrictPosInterface N T L

                        (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)) / 2 +

                    wilsonActionOSNegative N T L β (extendToFullConfig N T L

                      (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

                      (restrictPosInterface N T L

                        (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U))) / 2 +

                    wilsonActionOSInterface N T L β (extendToFullConfig N T L

                      (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

                      (restrictPosInterface N T L

                        (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U))))) := by

  let u := restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)

  let U_minus := restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U

  let u_int := restrictToInterface N T L u

  let θU := reflectLinkVariable N U

  let θu_restrict := restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) θU)



  have h_ext_full : extendToFullConfig N T L U_minus u = U := by

    dsimp [extendToFullConfig]

    have h_merge_eq : mergeConfigurations N T L U_minus u =

        restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U := by

      calc

        mergeConfigurations N T L U_minus u

            = mergeConfigurations N T L

                (λ ⟨(n, μ), hn⟩ => (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U) ⟨(n, μ), Finset.mem_univ n⟩)

                (restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)) := rfl

        _ = restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U :=

          mergeConfigurations_restore N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)

    calc

      extendToFullConfig N T L U_minus u

          = extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))

              (mergeConfigurations N T L U_minus u) := rfl

      _ = extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))

              (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U) := by

        rw [h_merge_eq]

      _ = U := by

        simp [extendLinkVariable, restrictLinkVariable]

  

  have h_os_pos : osPositiveOfPosInterface N T L β u = wilsonActionOSPositive N T L β U :=

    osPositiveOfPosInterface_restrict_eq N T L β U



  have h_S_neg : wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) = wilsonActionOSNegative N T L β U := by

    rw [h_ext_full]



  have h_S_int : wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u) = wilsonActionOSInterface N T L β U := by

    rw [h_ext_full]



  have h_f_u : g_posInterface N T L hT β f u = f U * Real.exp (-β * wilsonActionOSPositive N T L β U / 2) := by

    dsimp [g_posInterface, u]

    have h_agrees : ∀ (n : PeriodicSite T L) (μ : Fin 4),

        n ∈ (positiveSites T L ∪ interfaceSites T L) →

        U.value n μ = (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u).value n μ := by

      intro n μ hn

      have h := extend_of_restrictPosInterface_agrees N T L U n μ hn

      exact h.symm

    have h_f_eq : f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u) = f U := by

      have h := hf_supported U (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u) h_agrees

      exact h.symm

    rw [h_f_eq, h_os_pos]



  have h_reflect_eq : reflectToPosInterface N T L U_minus u_int = θu_restrict :=

    reflectToPosInterface_eq_restrict N T L hT U



  have h_f_θu : g_posInterface N T L hT β f (reflectToPosInterface N T L U_minus u_int) =

      f (reflectLinkVariable N U) * Real.exp (-β * wilsonActionOSNegative N T L β U / 2) := by

    dsimp [g_posInterface]

    rw [h_reflect_eq]

    dsimp [θu_restrict]

    have h_agrees_θU : ∀ (n : PeriodicSite T L) (μ : Fin 4),

        n ∈ (positiveSites T L ∪ interfaceSites T L) →

        (reflectLinkVariable N U).value n μ =

        (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) θu_restrict).value n μ := by

      intro n μ hn

      rcases Finset.mem_union.mp hn with (hn_pos | hn_int)

      · simp [hn_pos, θu_restrict, θU, extendLinkVariable, restrictPosInterface, restrictLinkVariable]

      · simp [hn_int, θu_restrict, θU, extendLinkVariable, restrictPosInterface, restrictLinkVariable]

    have h_f_θU : f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) θu_restrict) = f (reflectLinkVariable N U) := by

      have h := hf_supported (reflectLinkVariable N U)

        (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) θu_restrict) h_agrees_θU

      exact h.symm

    rw [h_f_θU]

    have h_os_pos_θu : osPositiveOfPosInterface N T L β θu_restrict = wilsonActionOSPositive N T L β (reflectLinkVariable N U) :=

      osPositiveOfPosInterface_restrict_eq N T L β (reflectLinkVariable N U)

    rw [h_os_pos_θu, neg_action_reflection_os_periodic N T L β hT U]



  calc

    G N T L hT β f U * G N T L hT β f (reflectLinkVariable N U)

        = (f U * Real.exp (-β * wilsonActionOSPositive N T L β U / 2)) *

          (f (reflectLinkVariable N U) * Real.exp (-β * wilsonActionOSNegative N T L β U / 2)) *

          Real.exp (-β * (wilsonActionOSPositive N T L β U / 2 + wilsonActionOSNegative N T L β U / 2 +

                          wilsonActionOSInterface N T L β U)) :=

      G_thetaG_factorization_clean N T L hT β f U

    _ = g_posInterface N T L hT β f u *

        g_posInterface N T L hT β f (reflectToPosInterface N T L U_minus u_int) *

        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +

          wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) / 2 +

          wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u))) := by

      rw [h_f_u, h_f_θu, h_os_pos, h_S_neg, h_S_int]

    _ = g_posInterface N T L hT β f (restrictPosInterface N T L

          (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)) *

        g_posInterface N T L hT β f (reflectToPosInterface N T L

          (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

          (restrictToInterface N T L (restrictPosInterface N T L

            (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)))) *

        Real.exp (-β * (osPositiveOfPosInterface N T L β

                          (restrictPosInterface N T L

                            (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)) / 2 +

                        wilsonActionOSNegative N T L β (extendToFullConfig N T L

                          (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

                          (restrictPosInterface N T L

                            (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U))) / 2 +

                        wilsonActionOSInterface N T L β (extendToFullConfig N T L

                          (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

                          (restrictPosInterface N T L

                            (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U))))) := by

      simp [u, U_minus, u_int]



/-- The plaquette contribution is measurable as a function of the link variable,

  because it involves only finitely many matrix entries (multiplication, inversion,

  trace, and real part are all continuous, hence measurable). -/

lemma measurable_plaquetteContribution (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]

    (n : Λ) (μ ν : Fin 4) : Measurable (λ (U : LinkVariable (SU N) Λ) => plaquetteContribution N β U n μ ν) := by

  unfold plaquetteContribution

  -- The map U ↦ U.value is measurable (comap definition)

  have h_value_map : Measurable (fun (U : LinkVariable (SU N) Λ) => U.value) :=

    comap_measurable (fun (U : LinkVariable (SU N) Λ) => U.value)

  -- For each n', μ', the map U ↦ U.value n' μ' is measurable

  have h_val_meas (n' : Λ) (μ' : Fin 4) : Measurable (λ (U : LinkVariable (SU N) Λ) => U.value n' μ') := by

    have h_at_n : Measurable (λ (f : Λ → Fin 4 → SU N) => f n') := measurable_pi_apply n'

    have h_at_n_μ' : Measurable (λ (f : Fin 4 → SU N) => f μ') := measurable_pi_apply μ'

    exact h_at_n_μ'.comp (h_at_n.comp h_value_map)

  -- The plaquetteProduct is a product of four SU(N) entries, each measurable

  have h_pp_meas : Measurable (λ (U : LinkVariable (SU N) Λ) => plaquetteProduct N U n μ ν) := by

    unfold plaquetteProduct

    have h_inv_meas : Measurable (λ (g : SU N) => g⁻¹) := (Continuous.inv continuous_id).measurable

    -- Build the product: A * B * C⁻¹ * D⁻¹

    -- Using Measurable.mul repeatedly with right-associativity

    have h_A : Measurable (λ (U : LinkVariable (SU N) Λ) => U.value n μ) := h_val_meas n μ

    have h_B : Measurable (λ (U : LinkVariable (SU N) Λ) => U.value (AddVector.addVector n μ) ν) :=

      h_val_meas (AddVector.addVector n μ) ν

    have h_C_inv : Measurable (λ (U : LinkVariable (SU N) Λ) => (U.value (AddVector.addVector (AddVector.addVector n μ) ν) μ)⁻¹) :=

      h_inv_meas.comp (h_val_meas (AddVector.addVector (AddVector.addVector n μ) ν) μ)

    have h_D_inv : Measurable (λ (U : LinkVariable (SU N) Λ) => (U.value (AddVector.addVector n ν) ν)⁻¹) :=

      h_inv_meas.comp (h_val_meas (AddVector.addVector n ν) ν)

    -- A * B * C⁻¹ * D⁻¹ = ((A * B) * C⁻¹) * D⁻¹

    have h_AB : Measurable (λ (U : LinkVariable (SU N) Λ) => U.value n μ * U.value (AddVector.addVector n μ) ν) :=

      Measurable.mul h_A h_B

    have h_AB_Cinv : Measurable (λ (U : LinkVariable (SU N) Λ) => (U.value n μ * U.value (AddVector.addVector n μ) ν) *

      (U.value (AddVector.addVector (AddVector.addVector n μ) ν) μ)⁻¹) :=

      Measurable.mul h_AB h_C_inv

    have h_ABCD : Measurable (λ (U : LinkVariable (SU N) Λ) => (U.value n μ * U.value (AddVector.addVector n μ) ν) *

      (U.value (AddVector.addVector (AddVector.addVector n μ) ν) μ)⁻¹ * (U.value (AddVector.addVector n ν) ν)⁻¹) :=

      Measurable.mul h_AB_Cinv h_D_inv

    -- The expression is now grouped as (A*B)*C⁻¹*D⁻¹ but the goal has A*B*C⁻¹*D⁻¹ (left-assoc)

    -- The grouping doesn't matter for measurability

    simpa [mul_assoc] using h_ABCD

  -- Now handle the trace and real part

  have h_cont_trace_re : Continuous (λ (g : SU N) => ((trace ((g : Matrix (Fin N) (Fin N) ℂ))).re : ℝ)) := by

    have h_cont_trace : Continuous (trace : Matrix (Fin N) (Fin N) ℂ → ℂ) := by

      have h_eq : trace = λ (A : Matrix (Fin N) (Fin N) ℂ) => ∑ i : Fin N, A i i := by

        ext A; simp [Matrix.trace]

      rw [h_eq]

      apply continuous_finsetSum

      intro i hi

      have h_entry : Continuous (λ (A : Matrix (Fin N) (Fin N) ℂ) => A i i) :=

        (continuous_apply i).comp (continuous_apply i)

      exact h_entry

    have h_cont_val : Continuous (Subtype.val : SU N → Matrix (Fin N) (Fin N) ℂ) :=

      continuous_subtype_val

    have h_cont_re : Continuous (Complex.re : ℂ → ℝ) := Complex.continuous_re

    exact h_cont_re.comp (h_cont_trace.comp h_cont_val)

  have h_trace_re_meas : Measurable (λ (U : LinkVariable (SU N) Λ) =>

    ((trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ)) :=

    h_cont_trace_re.measurable.comp h_pp_meas

  -- Now combine with constants: β * (1 - (1/N) * (...))

  have h_inner : Measurable (λ (U : LinkVariable (SU N) Λ) =>

    (1 : ℝ) - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ)) := by

    refine Measurable.sub measurable_const (Measurable.mul measurable_const h_trace_re_meas)

  exact (measurable_const_mul β).comp h_inner



/-- The positive-time part of the OS Wilson action is measurable. -/

lemma measurable_wilsonActionOSPositive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :

    Measurable (wilsonActionOSPositive N T L β) := by

  unfold wilsonActionOSPositive

  refine Finset.measurable_sum _ (λ n hn => ?_)

  refine Finset.measurable_sum _ (λ μ hμ => ?_)

  refine Finset.measurable_sum _ (λ ν hν => ?_)

  split_ifs

  · exact measurable_plaquetteContribution N β (PeriodicSite T L) n μ ν

  · exact measurable_const



/-- The interface part of the OS Wilson action is measurable. -/

lemma measurable_wilsonActionOSInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :

    Measurable (wilsonActionOSInterface N T L β) := by

  unfold wilsonActionOSInterface

  refine Finset.measurable_sum _ (λ n hn => ?_)

  refine Finset.measurable_sum _ (λ μ hμ => ?_)

  refine Finset.measurable_sum _ (λ ν hν => ?_)

  split_ifs

  · exact measurable_plaquetteContribution N β (PeriodicSite T L) n μ ν

  · exact measurable_const



/-- The negative-time part of the OS Wilson action is measurable. -/

lemma measurable_wilsonActionOSNegative (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :

    Measurable (wilsonActionOSNegative N T L β) := by

  unfold wilsonActionOSNegative

  refine Finset.measurable_sum _ (λ n hn => ?_)

  refine Finset.measurable_sum _ (λ μ hμ => ?_)

  refine Finset.measurable_sum _ (λ ν hν => ?_)

  split_ifs

  · exact measurable_plaquetteContribution N β (PeriodicSite T L) n μ ν

  · exact measurable_const



/-- G(U) is measurable when f is measurable. -/

lemma measurable_G (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) (hf : Measurable f) :

    Measurable (G N T L hT β f) := by

  unfold G

  have h_pos_meas : Measurable (wilsonActionOSPositive N T L β) :=

    measurable_wilsonActionOSPositive N T L β

  have h_int_meas : Measurable (wilsonActionOSInterface N T L β) :=

    measurable_wilsonActionOSInterface N T L β

  have h_exp_pos : Measurable (λ (U : LinkVariable (SU N) (PeriodicSite T L)) =>

    Real.exp (-β * wilsonActionOSPositive N T L β U)) := by

    have h_mul : Measurable (λ (U : LinkVariable (SU N) (PeriodicSite T L)) => -β * wilsonActionOSPositive N T L β U) :=

      (measurable_const_mul (-β)).comp h_pos_meas

    exact Real.measurable_exp.comp h_mul

  have h_exp_int : Measurable (λ (U : LinkVariable (SU N) (PeriodicSite T L)) =>

    Real.exp (-β * wilsonActionOSInterface N T L β U / 2)) := by

    have h_mul : Measurable (λ (U : LinkVariable (SU N) (PeriodicSite T L)) => -β * wilsonActionOSInterface N T L β U / 2) :=

      ((measurable_const_mul (-β)).comp h_int_meas).div_const (2 : ℝ)

    exact Real.measurable_exp.comp h_mul

  -- G = f * exp1 * exp2. The goal after unfold G is Measurable (λ U => (f U * exp1 U) * exp2 U),

  -- while hf.mul (h_exp_pos.mul h_exp_int) gives Measurable (f * (exp1 * exp2)).

  -- We show the two function expressions are equal.

  have h_eq : f * ((λ (U : LinkVariable (SU N) (PeriodicSite T L)) => Real.exp (-β * wilsonActionOSPositive N T L β U)) *

      (λ (U : LinkVariable (SU N) (PeriodicSite T L)) => Real.exp (-β * wilsonActionOSInterface N T L β U / 2))) =

    (λ (U : LinkVariable (SU N) (PeriodicSite T L)) => f U * Real.exp (-β * wilsonActionOSPositive N T L β U) *

      Real.exp (-β * wilsonActionOSInterface N T L β U / 2)) := by

    ext U; simp [Pi.mul_apply, mul_assoc]

  rw [← h_eq]

  exact hf.mul (h_exp_pos.mul h_exp_int)



/-- The integrand in the LHS of the key identity is measurable (hence AEStronglyMeasurable).

  This follows because G, extendLinkVariable and reflectLinkVariable are all continuous

  (or at least measurable) functions on a compact group. -/

lemma integrand_measurable (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) (hf : Measurable f) :

    Measurable (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>

      G N T L hT β f (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg) *

      G N T L hT β f (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg))) := by

  have hG_meas : Measurable (G N T L hT β f) := measurable_G N T L hT β f hf

  have h_ext_meas : Measurable (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :=

    measurable_extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))

  have h_reflect_meas : Measurable (reflectLinkVariable N : LinkVariable (SU N) (PeriodicSite T L) → LinkVariable (SU N) (PeriodicSite T L)) :=

    measurable_reflectLinkVariable N T L

  have h_first : Measurable (λ (cfg : _) => G N T L hT β f (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg)) :=

    hG_meas.comp h_ext_meas

  have h_second : Measurable (λ (cfg : _) => G N T L hT β f (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg))) :=

    hG_meas.comp (h_reflect_meas.comp h_ext_meas)

  exact Measurable.mul h_first h_second



/-- `linkVariableRestrict` is measurable (each coordinate is a projection from `U.value`). -/

lemma measurable_linkVariableRestrict (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :

    Measurable (linkVariableRestrict N Λ sites) := by

  rw [measurable_pi_iff]

  intro idx

  rcases idx with ⟨⟨n, μ⟩, hn⟩

  dsimp [linkVariableRestrict]

  have h_value_map : Measurable (fun (U : LinkVariable (SU N) Λ) => U.value) :=

    comap_measurable (fun (U : LinkVariable (SU N) Λ) => U.value)

  have h_at_n : Measurable (λ (f : Λ → Fin 4 → SU N) => f n) := measurable_pi_apply n

  have h_at_n_μ : Measurable (λ (f : Fin 4 → SU N) => f μ) := measurable_pi_apply μ

  exact h_at_n_μ.comp (h_at_n.comp h_value_map)



/-- `mergeConfigurations` is measurable in its first argument when the second is fixed. -/

lemma measurable_mergeConfigurations_first (U_plus_zero : PosInterfaceConfig N T L) :

    Measurable (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

      mergeConfigurations N T L U_minus U_plus_zero) := by

  rw [measurable_pi_iff]

  intro idx

  rcases idx with ⟨⟨n, μ⟩, hn⟩

  by_cases hpos : n ∈ positiveSites T L

  · -- At a positive site, the value is constant (from U_plus_zero)

    have h_const : (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

      (mergeConfigurations N T L U_minus U_plus_zero) ⟨(n, μ), hn⟩) =

      λ _ => U_plus_zero ⟨(n, μ), Finset.mem_union_left (interfaceSites T L) hpos⟩ := by

      ext U_minus; simp [mergeConfigurations, hpos]

    rw [h_const]

    exact measurable_const

  · by_cases hneg : n ∈ negativeSites T L

    · -- At a negative site, the value is a projection from U_minus

      have h_proj : (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

        (mergeConfigurations N T L U_minus U_plus_zero) ⟨(n, μ), hn⟩) =

        λ U_minus => U_minus ⟨(n, μ), hneg⟩ := by

        ext U_minus; simp [mergeConfigurations, hpos, hneg]

      rw [h_proj]

      refine measurable_pi_apply (⟨(n, μ), hneg⟩ : FiniteLinkIndex (PeriodicSite T L) (negativeSites T L))

    · -- At an interface site, the value is constant (from U_plus_zero)

      have hint : n ∈ interfaceSites T L := by

        have h_cover := sites_cover T L

        have hn_univ : n ∈ Finset.univ := hn

        have h_mem : n ∈ (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) := by

          rw [h_cover]; exact hn_univ

        rcases Finset.mem_union.mp h_mem with (h | h)

        · rcases Finset.mem_union.mp h with (h' | h')

          · exfalso; exact hpos h'

          · exfalso; exact hneg h'

        · exact h

      have h_const : (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

        (mergeConfigurations N T L U_minus U_plus_zero) ⟨(n, μ), hn⟩) =

        λ _ => U_plus_zero ⟨(n, μ), Finset.mem_union_right (positiveSites T L) hint⟩ := by

        ext U_minus; simp [mergeConfigurations, hpos, hneg, hint]

      rw [h_const]

      exact measurable_const



/-- `reflectToPosInterface` is measurable in its first argument when the second is fixed. -/

lemma measurable_reflectToPosInterface_first (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :

    Measurable (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

      reflectToPosInterface N T L U_minus U_zero) := by

  -- Define the constant second argument to mergeConfigurations

  let c : PosInterfaceConfig N T L := λ idx =>

    match idx with

    | ⟨(n, μ), hmem⟩ =>

      if hpos : n ∈ positiveSites T L then (1 : SU N)

      else

        have hint : n ∈ interfaceSites T L := by

          rcases Finset.mem_union.mp hmem with (hpos' | hint')

          · exact (hpos hpos').elim

          · exact hint'

        U_zero ⟨(n, μ), hint⟩

  have h_merge : Measurable (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

      mergeConfigurations N T L U_minus c) :=

    measurable_mergeConfigurations_first N T L c

  have h_ext : Measurable (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :=

    measurable_extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))

  have h_reflect : Measurable (reflectLinkVariable N : LinkVariable (SU N) (PeriodicSite T L) → LinkVariable (SU N) (PeriodicSite T L)) :=

    measurable_reflectLinkVariable N T L

  have h_restrict : Measurable (linkVariableRestrict N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)) :=

    measurable_linkVariableRestrict N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)

  have h_comp : Measurable (linkVariableRestrict N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) ∘

      reflectLinkVariable N ∘

      extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) ∘

      (λ U_minus => mergeConfigurations N T L U_minus c)) := by

    refine h_restrict.comp ?_

    refine h_reflect.comp ?_

    refine h_ext.comp ?_

    exact h_merge

  have h_eq : (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

      reflectToPosInterface N T L U_minus U_zero) =

    (linkVariableRestrict N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) ∘

      reflectLinkVariable N ∘

      extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) ∘

      (λ U_minus => mergeConfigurations N T L U_minus c)) := by

    rfl

  rw [h_eq]

  exact h_comp



/-- `extendToFullConfig` is measurable in its first argument when the second is fixed. -/

lemma measurable_extendToFullConfig_first (u : PosInterfaceConfig N T L) :

    Measurable (λ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>

      extendToFullConfig N T L U_minus u) := by

  dsimp [extendToFullConfig]

  refine (measurable_extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))).comp ?_

  exact measurable_mergeConfigurations_first N T L u

/-- `restrictLinkVariable` is measurable (each coordinate is a projection from `U.value`). -/
lemma measurable_restrictLinkVariable (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :
    Measurable (restrictLinkVariable N Λ sites) := by
  rw [measurable_pi_iff]
  intro idx
  rcases idx with ⟨⟨n, μ⟩, hn⟩
  dsimp [restrictLinkVariable]
  have h_value_map : Measurable (fun (U : LinkVariable (SU N) Λ) => U.value) :=
    comap_measurable (fun (U : LinkVariable (SU N) Λ) => U.value)
  have h_at_n : Measurable (fun (f : Λ → Fin 4 → SU N) => f n) := measurable_pi_apply n
  have h_at_n_μ : Measurable (fun (f : Fin 4 → SU N) => f μ) := measurable_pi_apply μ
  exact h_at_n_μ.comp (h_at_n.comp h_value_map)

/-- `reflectPosToNeg` is measurable: it is the composition
`restrictLinkVariable ∘ reflectLinkVariable ∘ extendLinkVariable`, each measurable. -/
lemma measurable_reflectPosToNeg (N T L : ℕ) [NeZero T] [NeZero L] :
    Measurable (reflectPosToNeg N T L) := by
  have h_ext : Measurable (extendLinkVariable N (PeriodicSite T L) (positiveSites T L)) :=
    measurable_extendLinkVariable N (PeriodicSite T L) (positiveSites T L)
  have h_reflect : Measurable
      (reflectLinkVariable N : LinkVariable (SU N) (PeriodicSite T L) → LinkVariable (SU N) (PeriodicSite T L)) :=
    measurable_reflectLinkVariable N T L
  have h_restrict : Measurable (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L)) :=
    measurable_restrictLinkVariable N (PeriodicSite T L) (negativeSites T L)
  have h : reflectPosToNeg N T L =
      restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) ∘
      reflectLinkVariable N ∘ extendLinkVariable N (PeriodicSite T L) (positiveSites T L) := by
    funext V_plus; simp [reflectPosToNeg]
  rw [h]
  exact h_restrict.comp (h_reflect.comp h_ext)

/-- `extendToFullConfig (reflectPosToNeg V⁺) u` is measurable in `V⁺`. -/
lemma measurable_extendToFullConfig_reflectPosToNeg (N T L : ℕ) [NeZero T] [NeZero L]
    (u : PosInterfaceConfig N T L) :
    Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) := by
  have h_rpn : Measurable (reflectPosToNeg N T L) := measurable_reflectPosToNeg N T L
  have h_ext : Measurable (fun (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) =>
      extendToFullConfig N T L U_minus u) := measurable_extendToFullConfig_first N T L u
  exact h_ext.comp h_rpn

/-- Each character factor `repCharacter (ρ i) (interfaceLinkVar U l)` is measurable in `V⁺`,
where `U = extendToFullConfig (reflectPosToNeg V⁺) u`. This composes the measurability of
`reflectPosToNeg`, `extendToFullConfig`, `interfaceLinkVar`, and `repCharacter (ρ i)`
(the latter from the strengthened Peter-Weyl axiom `hMeas`). -/
lemma measurable_integrand_char_factor (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (u : PosInterfaceConfig N T L) (i : ι) (l : InterfaceLink T L) :
    Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      repCharacter (ρ i) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) :=
  (h_meas i).comp ((measurable_interfaceLinkVar N T L l).comp
    (measurable_extendToFullConfig_reflectPosToNeg N T L u))

set_option maxHeartbeats 1000000 in
/-- The character triple product `B(V⁺) = Φ_w(U)·Ψ_w(U)·star(V_w(U))` (where
`U = extendToFullConfig (reflectPosToNeg V⁺) u`) is measurable in `V⁺`. This follows from
`measurable_integrand_char_factor` (each factor measurable) + `Finset.measurable_prod`
(finite products) + `Measurable.mul` + continuity of `star` (conjugation). -/
lemma measurable_integrand_B (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (u : PosInterfaceConfig N T L) :
    Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
       (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
       star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))) := by
  have h_pos : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      ∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) :=
    Finset.measurable_prod (interfaceLinkPos T L)
      (fun l _ => measurable_integrand_char_factor N T L ι dims ρ h_meas u (w l) l)
  have h_int : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      ∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) :=
    Finset.measurable_prod (interfaceLinkInt T L)
      (fun l _ => measurable_integrand_char_factor N T L ι dims ρ h_meas u (w l) l)
  have h_neg : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      ∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) :=
    Finset.measurable_prod (interfaceLinkNeg T L)
      (fun l _ => measurable_integrand_char_factor N T L ι dims ρ h_meas u (dual (w l)) l)
  have h_neg_star : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l))) :=
    continuous_star.measurable.comp h_neg
  exact Measurable.mul (Measurable.mul h_pos h_int) h_neg_star

set_option maxHeartbeats 1000000 in
/-- **AEStronglyMeasurable of the `A` factor** `Complex.ofReal (ψ(merge)·exp(-β·S⁺(merge)/2))`.
Derived from `hψ_int` (integrability of the full integrand) by dividing by the measurable
nonzero factor `exp(-β·S⁺(u)/2)·exp(-β·S_int(U))` (which is positive, hence nonzero). 0 sorries. -/
lemma integrand_A_ae
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    AEStronglyMeasurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)))
      (haarMeasurePositive N T L) := by
  -- full(V⁺) = ψ(merge)·exp(-β·(S⁺(u)/2 + S⁺(merge)/2 + S_int(U))) is AEStronglyMeasurable
  have h_full_ae := hψ_int.aestronglyMeasurable
  -- factor(V⁺) = exp(-β·S⁺(u)/2)·exp(-β·S_int(U)) is measurable (S⁺(u) const, S_int(U) measurable)
  have h_factor_meas : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) *
      Real.exp (-β * wilsonActionOSInterface N T L β
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) := by
    have hU : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) :=
      measurable_extendToFullConfig_reflectPosToNeg N T L u
    have hS_int : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        wilsonActionOSInterface N T L β (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)) :=
      (measurable_wilsonActionOSInterface N T L β).comp hU
    have h_mul_int : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        -β * wilsonActionOSInterface N T L β (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)) :=
      Measurable.mul measurable_const hS_int
    have h_exp_int : Measurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        Real.exp (-β * wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) :=
      Real.measurable_exp.comp h_mul_int
    exact Measurable.mul measurable_const h_exp_int
  have h_factor_ae : AEStronglyMeasurable _ (haarMeasurePositive N T L) :=
    h_factor_meas.aestronglyMeasurable
  -- full / factor is AEStronglyMeasurable (use mul + inv, then congr to convert * ⁻¹ to /)
  have h_inv_factor : AEStronglyMeasurable _ (haarMeasurePositive N T L) :=
    (Measurable.inv h_factor_meas).aestronglyMeasurable
  have h_mul_ae := AEStronglyMeasurable.mul h_full_ae h_inv_factor
  have h_div_ae : AEStronglyMeasurable _ (haarMeasurePositive N T L) :=
    h_mul_ae.congr (ae_of_all (haarMeasurePositive N T L)
      (fun V_plus => (div_eq_mul_inv _ _).symm))
  -- pointwise: full / factor = ψ(merge)·exp(-β·S⁺(merge)/2)
  have h_eq : ∀ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))) /
    (Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) *
      Real.exp (-β * wilsonActionOSInterface N T L β
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) =
    ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2) := by
    intro V_plus
    set merge := mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))
    set U := extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u
    have h_arg : -β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β merge / 2 + wilsonActionOSInterface N T L β U) =
      (-β * osPositiveOfPosInterface N T L β u / 2) +
      (-β * osPositiveOfPosInterface N T L β merge / 2) +
      (-β * wilsonActionOSInterface N T L β U) := by ring
    rw [h_arg, Real.exp_add, Real.exp_add]
    field_simp [Real.exp_pos]
  have h_target_ae := h_div_ae.congr (ae_of_all (haarMeasurePositive N T L) h_eq)
  -- A = Complex.ofReal ∘ target
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable h_target_ae

set_option maxHeartbeats 1000000 in
/-- **Discharge of `h_integrand_ae`.** The character-expansion integrand
`(F w : ℂ)·(A(V⁺)·B(V⁺))` is AEStronglyMeasurable w.r.t. `μ⁺`, where `A` is the
Boltzmann-prefactor (AEStronglyMeasurable from `hψ_int` via `integrand_A_ae`) and `B` is the
character triple product (Measurable from `measurable_integrand_B`, using the strengthened
Peter-Weyl axiom `hMeas`). This discharges the `h_integrand_ae` hypothesis of
`transfer_matrix_fubini_integrability`. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_integrand_ae
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    ∀ w : InterfaceLink T L → ι,
      AEStronglyMeasurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        (F w : ℂ) *
          (Complex.ofReal (ψ (mergePosInterface N T L V_plus
              (sigmaInterface N T L (restrictToInterface N T L u))) *
            Real.exp (-β * osPositiveOfPosInterface N T L β
              (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
          ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))))
        (haarMeasurePositive N T L) := by
  intro w
  have hA_ae := integrand_A_ae N T L β ψ u hψ_int
  have hB := measurable_integrand_B N T L ι dims ρ h_meas dual w u
  have hB_ae : AEStronglyMeasurable _ (haarMeasurePositive N T L) := hB.aestronglyMeasurable
  have hAB := AEStronglyMeasurable.mul hA_ae hB_ae
  have hF : AEStronglyMeasurable (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
      (F w : ℂ)) (haarMeasurePositive N T L) := measurable_const.aestronglyMeasurable
  exact AEStronglyMeasurable.mul hF hAB

#print axioms transfer_matrix_integrand_ae

set_option maxHeartbeats 1000000 in
/-- **Step 4c (self-contained integrability).** Combines
`transfer_matrix_fubini_integrability` (the domination argument, which takes
`h_integrand_ae` as a hypothesis) with `transfer_matrix_integrand_ae` (which
discharges `h_integrand_ae` from `hψ_int` plus the strengthened Peter-Weyl axiom
`h_meas : ∀ i, Measurable (repCharacter (ρ i))`). The result is a single lemma
whose only hypotheses are `hψ_int` (integrability of the full Boltzmann-weighted
observable) and `h_meas` (character measurability, supplied by the axiom) —
no `h_int` / `h_integrand_ae` parameter remains. This is the self-contained
step-4c integrability discharge used to close
`transfer_matrix_fubini_character_expansion`. 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_integrability_self
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (hψ_int : Integrable
      (fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
        ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      (haarMeasurePositive N T L)) :
    ∀ w : InterfaceLink T L → ι,
      Integrable (fun V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) =>
        (F w : ℂ) *
          (Complex.ofReal (ψ (mergePosInterface N T L V_plus
              (sigmaInterface N T L (restrictToInterface N T L u))) *
            Real.exp (-β * osPositiveOfPosInterface N T L β
              (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
          ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
           star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))))
        (haarMeasurePositive N T L) := by
  exact transfer_matrix_fubini_integrability N T L β ψ u ι dims ρ h_unitary dual F hψ_int
    (transfer_matrix_integrand_ae N T L β ψ u ι dims ρ h_unitary h_meas dual F hψ_int)

#print axioms transfer_matrix_fubini_integrability_self

