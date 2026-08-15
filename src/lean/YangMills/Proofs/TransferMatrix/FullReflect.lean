/-
# Transfer Matrix: Full Reflection Reindexing
-/

import YangMills.Proofs.TransferMatrix.ThetaInvariance

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
/-!
## Lemma 3 alternative: full reflection reindexing `w*` (swaps pos ↔ neg)

The `thetaReindex` (θ) is a PROJECTION (idempotent, not a bijection), so the sum
reindexing `w ↦ θw` is INVALID (see §8.11.24).  The CORRECT reflection symmetry
uses the FULL reflection reindexing `w* = fullReflectReindex`, which swaps
pos ↔ neg via `reflectInterfaceLink` (φ), applying `dual` on time-like links.

`w*` is defined by:
- `l ∈ pos`, time-like: `w*(l) = dual(w(φ(l)))`  (φ(l) ∈ neg, inverted link)
- `l ∈ pos`, spatial:   `w*(l) = w(φ(l))`         (φ(l) ∈ neg, unchanged link)
- `l ∈ int`:            `w*(l) = w(l)`             (unchanged)
- `l ∈ neg`:            `w*(l) = w(l)`             (arbitrary, not used in identities)

The key identity is `star(charFactorNeg dual w (reflectPosToNeg V⁺)) =
charFactorPos (fullReflectReindex dual w) V⁺`, which gives
`B_w(u⁰) = A_{w*}(σ(u⁰))` (the "plain form" relationship, without reindexing the sum).
This is proved WITHOUT `dual` involutivity — the double `conj` cancels via `conj_conj`.
See §8.11.25 for the full analysis.
-/

/-- The full reflection reindexing `w* : (InterfaceLink → ι) → (InterfaceLink → ι)`.
For pos links, `w*` is determined by the neg link `φ(l)` (via `reflectInterfaceLink`),
with `dual` applied on time-like links.  For int and neg links, `w*` is the identity.
This is the reindexing that makes `star(charFactorNeg dual w (reflectPosToNeg V⁺)) =
charFactorPos (fullReflectReindex dual w) V⁺` hold (Lemma 3 alternative). -/
noncomputable def fullReflectReindex (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι) :
    InterfaceLink T L → ι :=
  fun l =>
    if hl_pos : l ∈ interfaceLinkPos T L then
      if hμ : l.val.2 = 0 then dual (w (reflectInterfaceLink T L hT l))
      else w (reflectInterfaceLink T L hT l)
    else w l

#print axioms fullReflectReindex

/-- For a positive-time interface link `l` with `μ(l) = 0` (time-like),
`w*(l) = dual(w(φ(l)))`. -/
lemma fullReflectReindex_pos_time (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkPos T L) (hμ : l.val.2 = 0) :
    fullReflectReindex T L hT ι dual w l = dual (w (reflectInterfaceLink T L hT l)) := by
  show (if hl_pos : l ∈ interfaceLinkPos T L then
        if hμ : l.val.2 = 0 then dual (w (reflectInterfaceLink T L hT l))
        else w (reflectInterfaceLink T L hT l)
      else w l) = dual (w (reflectInterfaceLink T L hT l))
  rw [dif_pos hl, dif_pos hμ]

#print axioms fullReflectReindex_pos_time

/-- For a positive-time interface link `l` with `μ(l) ≠ 0` (spatial),
`w*(l) = w(φ(l))`. -/
lemma fullReflectReindex_pos_spatial (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkPos T L) (hμ : l.val.2 ≠ 0) :
    fullReflectReindex T L hT ι dual w l = w (reflectInterfaceLink T L hT l) := by
  show (if hl_pos : l ∈ interfaceLinkPos T L then
        if hμ : l.val.2 = 0 then dual (w (reflectInterfaceLink T L hT l))
        else w (reflectInterfaceLink T L hT l)
      else w l) = w (reflectInterfaceLink T L hT l)
  rw [dif_pos hl, dif_neg hμ]

#print axioms fullReflectReindex_pos_spatial

set_option maxHeartbeats 1000000 in
/-- **Per-link identity (Lemma 3 alternative core).** For `b ∈ interfaceLinkPos`,
the negative-link character factor at the reflected link `reflectInterfaceLink b`
(with weight `w`) equals `star` of the positive-link character factor at `b`
(with weight `w* = fullReflectReindex`):
`χ_{dual(w(φ b))}(reflectPosToNeg V⁺_{φ b}) = star(χ_{w*(b)}(V⁺_b))`.

Time-like: `χ_{dual(w(φb))}((V⁺_b)⁻¹) = conj(χ_{dual(w(φb))}(V⁺_b))` (repCharacter_inv)
  = `star(χ_{dual(w(φb))}(V⁺_b))` (conj = star), and `w*(b) = dual(w(φb))`.
Spatial: `χ_{dual(w(φb))}(V⁺_b) = conj(χ_{w(φb))}(V⁺_b))` (hdual)
  = `star(χ_{w(φb))}(V⁺_b))` (conj = star), and `w*(b) = w(φb)`.
0 sorries, 0 custom axioms. -/
lemma charFactorNeg_eq_star_charFactorPos_link_fullReflect
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (b : InterfaceLink T L) (hb : b ∈ interfaceLinkPos T L) :
    (if hneg : (reflectInterfaceLink T L hT b).val.1 ∈ negativeSites T L then
       repCharacter (ρ (dual (w (reflectInterfaceLink T L hT b))))
         (reflectPosToNeg N T L V_plus ⟨((reflectInterfaceLink T L hT b).val.1,
            (reflectInterfaceLink T L hT b).val.2), hneg⟩)
     else 1) =
    (if hpos : b.val.1 ∈ positiveSites T L then
       star (repCharacter (ρ (fullReflectReindex T L hT ι dual w b)))
         (V_plus ⟨(b.val.1, b.val.2), hpos⟩)
     else 1) := by
  set l := reflectInterfaceLink T L hT b with hl_def
  have hb_neg : l ∈ interfaceLinkNeg T L := reflectInterfaceLink_mem_neg_of_pos T L hT hb
  have hneg' : l.val.1 ∈ negativeSites T L := (interfaceLinkNeg_mem_iff T L l).mp hb_neg
  have hpos' : b.val.1 ∈ positiveSites T L := (interfaceLinkPos_mem_iff T L b).mp hb
  have hl_val2 : l.val.2 = b.val.2 := by simp [l, reflectInterfaceLink]
  have hinv : ReflectSite.reflectSite l.val.1 = b.val.1 := by
    simp [l, reflectInterfaceLink, ReflectSite.involution]
  rw [dif_pos hneg', dif_pos hpos']
  by_cases hμ : b.val.2 = 0
  · -- time-like: w*(b) = dual(w(l)), link inverted
    have hμ' : l.val.2 = 0 := by rw [hl_val2]; exact hμ
    have hwstar : fullReflectReindex T L hT ι dual w b = dual (w l) := by
      rw [fullReflectReindex_pos_time T L hT ι dual w hb hμ]
    rw [hwstar]
    have hrt : reflectPosToNeg N T L V_plus ⟨(l.val.1, l.val.2), hneg'⟩ =
        (V_plus ⟨(b.val.1, b.val.2), hpos'⟩)⁻¹ := by
      have hpos'' := reflectSite_mem_positive_of_negative hT hneg'
      rw [reflectPosToNeg_apply N T L hT V_plus hneg' l.val.2]
      have heq : (⟨(ReflectSite.reflectSite l.val.1, l.val.2), hpos''⟩ :
          FiniteLinkIndex (PeriodicSite T L) (positiveSites T L)) =
          ⟨(b.val.1, b.val.2), hpos'⟩ := by
        congr 1
        rw [hinv, hl_val2]
      rw [heq, hl_val2, if_pos hμ]
    rw [hrt]
    rw [repCharacter_inv (ρ (dual (w l))) (h_unitary (dual (w l)))]
    -- LHS: conj(χ_{dual(w(l))}(V⁺_b)), RHS: star(χ_{dual(w(l))}(V⁺_b))
    -- conj = star (defeq), so rfl
    rfl
  · -- spatial: w*(b) = w(l), link unchanged
    have hμ' : l.val.2 ≠ 0 := by rw [hl_val2]; exact hμ
    have hwstar : fullReflectReindex T L hT ι dual w b = w l := by
      rw [fullReflectReindex_pos_spatial T L hT ι dual w hb hμ]
    rw [hwstar]
    have hrt : reflectPosToNeg N T L V_plus ⟨(l.val.1, l.val.2), hneg'⟩ =
        V_plus ⟨(b.val.1, b.val.2), hpos'⟩ := by
      have hpos'' := reflectSite_mem_positive_of_negative hT hneg'
      rw [reflectPosToNeg_apply N T L hT V_plus hneg' l.val.2]
      have heq : (⟨(ReflectSite.reflectSite l.val.1, l.val.2), hpos''⟩ :
          FiniteLinkIndex (PeriodicSite T L) (positiveSites T L)) =
          ⟨(b.val.1, b.val.2), hpos'⟩ := by
        congr 1
        rw [hinv, hl_val2]
      rw [heq, hl_val2, if_neg hμ]
    rw [hrt]
    -- LHS: χ_{dual(w(l))}(V⁺_b) = conj(χ_{w(l))}(V⁺_b)) (hdual)
    -- RHS: star(χ_{w(l))}(V⁺_b)) = conj(χ_{w(l))}(V⁺_b)) (star = conj)
    rw [hdual (w l)]
    -- LHS: conj(χ_{w(l))}(V⁺_b)), RHS: star(χ_{w(l))}(V⁺_b))
    -- conj = star (defeq), so rfl
    rfl

#print axioms charFactorNeg_eq_star_charFactorPos_link_fullReflect

set_option maxHeartbeats 1000000 in
/-- **Lemma 3 alternative: product identity.** The negative-link character factor at
`reflectPosToNeg V⁺` (with weight `w`) equals `star` of the positive-link character
factor at `V⁺` (with weight `w* = fullReflectReindex`):
`charFactorNeg dual w (reflectPosToNeg V⁺) = star (charFactorPos (fullReflectReindex dual w) V⁺)`.

This reindexes the product over `interfaceLinkNeg` to a product over `interfaceLinkPos`
via the reflection bijection `reflectInterfaceLink` (an involution mapping neg ↔ pos),
using `Finset.prod_bij` and the per-link identity
`charFactorNeg_eq_star_charFactorPos_link_fullReflect`.
0 sorries, 0 custom axioms. -/
lemma charFactorNeg_eq_star_charFactorPos_fullReflect
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus) =
    star (charFactorPos N T L ι dims ρ (fullReflectReindex T L hT ι dual w) V_plus) := by
  simp only [charFactorNeg, charFactorPos]
  -- Push star inside the charFactorPos product on the RHS
  rw [show star (∏ b ∈ interfaceLinkPos T L,
      (if hpos : b.val.1 ∈ positiveSites T L then
        repCharacter (ρ (fullReflectReindex T L hT ι dual w b)) (V_plus ⟨(b.val.1, b.val.2), hpos⟩)
      else (1 : ℂ))) =
      ∏ b ∈ interfaceLinkPos T L,
      (if hpos : b.val.1 ∈ positiveSites T L then
        star (repCharacter (ρ (fullReflectReindex T L hT ι dual w b)) (V_plus ⟨(b.val.1, b.val.2), hpos⟩))
      else (1 : ℂ)) from by
      rw [← starRingEnd_apply, map_prod]
      refine Finset.prod_congr rfl (fun b hb => ?_)
      rw [starRingEnd_apply]
      split_ifs with h
      · rfl
      · simp]
  -- Now both sides are products; reindex neg → pos via reflectInterfaceLink
  refine Finset.prod_bij (fun a ha => reflectInterfaceLink T L hT a) ?hi ?i_inj ?i_surj ?h
  · -- hi : reflectInterfaceLink maps interfaceLinkNeg into interfaceLinkPos
    intro a ha
    exact reflectInterfaceLink_mem_pos_of_neg T L hT ha
  · -- i_inj : reflectInterfaceLink is injective (it is an involution)
    intro a₁ ha₁ a₂ ha₂ heq
    rw [← reflectInterfaceLink_involution T L hT a₁, ← reflectInterfaceLink_involution T L hT a₂,
      heq]
  · -- i_surj : reflectInterfaceLink is surjective onto interfaceLinkPos (involution)
    intro b hb
    refine ⟨reflectInterfaceLink T L hT b, reflectInterfaceLink_mem_neg_of_pos T L hT hb, ?_⟩
    exact reflectInterfaceLink_involution T L hT b
  · -- h : per-link identity f a = g (reflectInterfaceLink a)
    intro a ha
    have hb : reflectInterfaceLink T L hT a ∈ interfaceLinkPos T L :=
      reflectInterfaceLink_mem_pos_of_neg T L hT ha
    have hlink := charFactorNeg_eq_star_charFactorPos_link_fullReflect N T L hT ι dims ρ h_unitary dual hdual w V_plus
      (reflectInterfaceLink T L hT a) hb
    rw [reflectInterfaceLink_involution T L hT a] at hlink
    exact hlink

#print axioms charFactorNeg_eq_star_charFactorPos_fullReflect

/-- The `star` (complex conjugate) version of
`charFactorNeg_eq_star_charFactorPos_fullReflect`:
`star(charFactorNeg dual w (reflectPosToNeg V⁺)) = charFactorPos (fullReflectReindex dual w) V⁺`.
This follows by applying `star` to both sides and using `star(star x) = x` (conj_conj).
0 sorries, 0 custom axioms. -/
lemma star_charFactorNeg_eq_charFactorPos_fullReflect
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus)) =
    charFactorPos N T L ι dims ρ (fullReflectReindex T L hT ι dual w) V_plus := by
  have h := charFactorNeg_eq_star_charFactorPos_fullReflect N T L hT ι dims ρ h_unitary dual hdual w V_plus
  rw [h]
  -- Goal: star (star (charFactorPos ...)) = charFactorPos ...
  -- star(star x) = conj(conj x) = x (Complex.conj_conj)
  exact Complex.conj_conj _

#print axioms star_charFactorNeg_eq_charFactorPos_fullReflect

set_option maxHeartbeats 1000000 in
/-- **Lemma 3 alternative: Fourier coefficient identity (plain form).** The negative
Fourier coefficient at weight `w` equals the positive Fourier coefficient at weight
`w* = fullReflectReindex` evaluated at `σ(u⁰)`:
`fourierCoeffNeg dual w u⁰ = fourierCoeffPos (fullReflectReindex dual w) (σ(u⁰))`.

This is the "plain form" relationship `B_w(u⁰) = A_{w*}(σ(u⁰))`, which follows from
`star_charFactorNeg_eq_charFactorPos_fullReflect` combined with `star` commuting with
the integral (`integral_conj`) and `star` distributing over the product with the real
Boltzmann prefactor (`star_mul'` + `conj_ofReal`).
0 sorries, 0 custom axioms. -/
lemma fourierCoeffNeg_eq_fourierCoeffPos_fullReflect
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffNeg N T L β ψ ι dims ρ dual w u0 =
    fourierCoeffPos N T L β ψ ι dims ρ (fullReflectReindex T L hT ι dual w)
      (sigmaInterface N T L u0) := by
  simp only [fourierCoeffNeg, fourierCoeffPos]
  -- The `star` is inside the LHS integral (on `charFactorNeg`), not outside the RHS integral.
  -- So we use `integral_congr_ae` directly to match integrands.
  refine integral_congr_ae (ae_of_all (haarMeasurePositive N T L) ?_)
  intro V
  dsimp only
  rw [star_charFactorNeg_eq_charFactorPos_fullReflect N T L hT ι dims ρ h_unitary dual hdual w V]

#print axioms fourierCoeffNeg_eq_fourierCoeffPos_fullReflect

set_option maxHeartbeats 1000000 in
/-- **Step 4e + Lemma 3 substitution: the fullReflect form.** Combines
`transfer_matrix_fubini_integrated_pull` (Step 4e) with
`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect` (Lemma 3 plain form) to rewrite the
negative Fourier coefficient `B_w(u⁰) = fourierCoeffNeg dual w u⁰` as the positive
Fourier coefficient at the reflected weight and reflected interface:
`A_{w*}(σ(u⁰)) = fourierCoeffPos (fullReflectReindex dual w) (σ(u⁰))`.

This gives the "fullReflect form" of the transfer-matrix inner product:
`Complex.ofReal(∫ ψ·Tψ dμ⁺⁰) = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰`
where `w* = fullReflectReindex dual w`. This is the starting point for the L² expansion
approach (Lemma 5 Step 4a). 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_integrated_pull_fullReflect
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (ψ : PosInterfaceConfig N T L → ℝ)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (h_meas : ∀ i, Measurable (repCharacter (ρ i)))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (F : (InterfaceLink T L → ι) → ℝ)
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
        fourierCoeffPos N T L β ψ ι dims ρ (fullReflectReindex T L hT ι dual w)
          (sigmaInterface N T L u0) *
        fourierCoeffPos N T L β ψ ι dims ρ w u0
      ∂ haarMeasureInterface N T L := by
  have h := transfer_matrix_fubini_integrated_pull N T L β ψ C ι dims ρ h_unitary h_meas dual F
    h_char hψ_int h_int
  rw [h]
  -- Rewrite fourierCoeffNeg dual w u0 → fourierCoeffPos (fullReflectReindex dual w) (σ u0) pointwise
  simp only [fourierCoeffNeg_eq_fourierCoeffPos_fullReflect N T L β hT ψ ι dims ρ h_unitary dual hdual]

#print axioms transfer_matrix_fubini_integrated_pull_fullReflect

