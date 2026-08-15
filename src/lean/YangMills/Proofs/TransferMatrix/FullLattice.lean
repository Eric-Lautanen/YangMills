/-
# Transfer Matrix: Full-Lattice Character Factors
-/

import YangMills.Proofs.TransferMatrix.FullReflect

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
/-! ### Step 4: Full-lattice character factor lemmas (§8.11.65)

These are the full-lattice analogues of the interface-only lemmas
`fullReflectReindex`, `charFactorPos`/`charFactorNeg`, and the per-link/product
identities `charFactorNeg_eq_star_charFactorPos_link_fullReflect` /
`charFactorNeg_eq_star_charFactorPos_fullReflect` /
`star_charFactorNeg_eq_charFactorPos_fullReflect`.

The key difference: the interface-only versions work over `InterfaceLink T L`
(a Subtype of `PeriodicSite T L × Fin 4` restricted to interface plaquette
links), while these full-lattice versions work over `PeriodicSite T L × Fin 4`
directly (ALL links), using `allLinkPos`/`allLinkNeg` (Finsets over ALL links)
instead of `interfaceLinkPos`/`interfaceLinkNeg`.  The reflection on links is
the simple `(n, μ) ↦ (reflectSite n, μ)` (no Subtype wrapping).

These lemmas show that the positive/negative link integral gives `|Â_w|²`,
which is Step 4 of the §8.11.61 plan.  0 sorries, 0 custom axioms. -/

/-- The full-lattice reflection reindexing `w* : ((PeriodicSite T L × Fin 4) → ι) → ((PeriodicSite T L × Fin 4) → ι)`.
For pos links, `w*` is determined by the neg link `(reflectSite l.1, l.2)` (the
reflected link), with `dual` applied on time-like links.  For int and neg
links, `w*` is the identity.
This is the full-lattice analogue of `fullReflectReindex` (which works for
`InterfaceLink T L`). -/
noncomputable def fullReflectReindexLink (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : (PeriodicSite T L × Fin 4) → ι) :
    (PeriodicSite T L × Fin 4) → ι :=
  fun l =>
    if hl_pos : l ∈ allLinkPos T L then
      if hμ : l.2 = 0 then dual (w (ReflectSite.reflectSite l.1, l.2))
      else w (ReflectSite.reflectSite l.1, l.2)
    else w l

#print axioms fullReflectReindexLink

/-- For a positive-time link `l` with `μ(l) = 0` (time-like),
`w*(l) = dual(w(reflectSite l.1, l.2))`. -/
lemma fullReflectReindexLink_pos_time (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : (PeriodicSite T L × Fin 4) → ι)
    {l : PeriodicSite T L × Fin 4} (hl : l ∈ allLinkPos T L) (hμ : l.2 = 0) :
    fullReflectReindexLink T L hT ι dual w l = dual (w (ReflectSite.reflectSite l.1, l.2)) := by
  show (if hl_pos : l ∈ allLinkPos T L then
        if hμ : l.2 = 0 then dual (w (ReflectSite.reflectSite l.1, l.2))
        else w (ReflectSite.reflectSite l.1, l.2)
      else w l) = dual (w (ReflectSite.reflectSite l.1, l.2))
  rw [dif_pos hl, dif_pos hμ]

#print axioms fullReflectReindexLink_pos_time

/-- For a positive-time link `l` with `μ(l) ≠ 0` (spatial),
`w*(l) = w(reflectSite l.1, l.2)`. -/
lemma fullReflectReindexLink_pos_spatial (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : (PeriodicSite T L × Fin 4) → ι)
    {l : PeriodicSite T L × Fin 4} (hl : l ∈ allLinkPos T L) (hμ : l.2 ≠ 0) :
    fullReflectReindexLink T L hT ι dual w l = w (ReflectSite.reflectSite l.1, l.2) := by
  show (if hl_pos : l ∈ allLinkPos T L then
        if hμ : l.2 = 0 then dual (w (ReflectSite.reflectSite l.1, l.2))
        else w (ReflectSite.reflectSite l.1, l.2)
      else w l) = w (ReflectSite.reflectSite l.1, l.2)
  rw [dif_pos hl, dif_neg hμ]

#print axioms fullReflectReindexLink_pos_spatial

/-- The full-lattice positive-link character factor `Φ_w(U⁺) = ∏_{l ∈ L_U} χ_{w(l)}(U⁺_l)`.
This is the full-lattice analogue of `charFactorPos` (which works for
`InterfaceLink T L`).  The product is over `allLinkPos T L` (ALL positive-time
links, not just interface links). -/
noncomputable def charFactorPosAll (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : (PeriodicSite T L × Fin 4) → ι)
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) : ℂ :=
  ∏ l ∈ allLinkPos T L,
    if hpos : l.1 ∈ positiveSites T L then
      repCharacter (ρ (w l)) (U_plus ⟨(l.1, l.2), hpos⟩)
    else 1

#print axioms charFactorPosAll

/-- The full-lattice negative-link character factor `V_w(U⁻) = ∏_{l ∈ L_V} χ_{dual(w(l))}(U⁻_l)`.
This is the full-lattice analogue of `charFactorNeg` (which works for
`InterfaceLink T L`).  The product is over `allLinkNeg T L` (ALL negative-time
links, not just interface links). -/
noncomputable def charFactorNegAll (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : (PeriodicSite T L × Fin 4) → ι)
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) : ℂ :=
  ∏ l ∈ allLinkNeg T L,
    if hneg : l.1 ∈ negativeSites T L then
      repCharacter (ρ (dual (w l))) (U_minus ⟨(l.1, l.2), hneg⟩)
    else 1

#print axioms charFactorNegAll

set_option maxHeartbeats 1000000 in
/-- **Per-link identity (full-lattice, Step 4 core).** For `b ∈ allLinkPos`,
the negative-link character factor at the reflected link `(reflectSite b.1, b.2)`
(with weight `w`) equals `star` of the positive-link character factor at `b`
(with weight `w* = fullReflectReindexLink`).

This is the full-lattice analogue of
`charFactorNeg_eq_star_charFactorPos_link_fullReflect` (which works for
`InterfaceLink T L`).  0 sorries, 0 custom axioms. -/
lemma charFactorNegAll_eq_star_charFactorPosAll_link_fullReflect
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : (PeriodicSite T L × Fin 4) → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (b : PeriodicSite T L × Fin 4) (hb : b ∈ allLinkPos T L) :
    (if hneg : (ReflectSite.reflectSite b.1, b.2).1 ∈ negativeSites T L then
       repCharacter (ρ (dual (w (ReflectSite.reflectSite b.1, b.2))))
         (reflectPosToNeg N T L V_plus ⟨((ReflectSite.reflectSite b.1, b.2).1,
            (ReflectSite.reflectSite b.1, b.2).2), hneg⟩)
     else 1) =
    (if hpos : b.1 ∈ positiveSites T L then
       star (repCharacter (ρ (fullReflectReindexLink T L hT ι dual w b)))
         (V_plus ⟨(b.1, b.2), hpos⟩)
     else 1) := by
  set a := (ReflectSite.reflectSite b.1, b.2) with ha_def
  have hpos' : b.1 ∈ positiveSites T L := (allLinkPos_mem_iff T L b).mp hb
  have hb_neg : a ∈ allLinkNeg T L := by
    rw [allLinkNeg_mem_iff]
    exact reflectSite_mem_negative_of_positive hT hpos'
  have hneg' : a.1 ∈ negativeSites T L := (allLinkNeg_mem_iff T L a).mp hb_neg
  have ha_val2 : a.2 = b.2 := by simp [a]
  have hinv : ReflectSite.reflectSite a.1 = b.1 := by
    simp [a, ReflectSite.involution]
  rw [dif_pos hneg', dif_pos hpos']
  by_cases hμ : b.2 = 0
  · -- time-like: w*(b) = dual(w(a)), link inverted
    have hμ' : a.2 = 0 := by rw [ha_val2]; exact hμ
    have hwstar : fullReflectReindexLink T L hT ι dual w b = dual (w a) := by
      rw [fullReflectReindexLink_pos_time T L hT ι dual w hb hμ]
    rw [hwstar]
    have hrt : reflectPosToNeg N T L V_plus ⟨(a.1, a.2), hneg'⟩ =
        (V_plus ⟨(b.1, b.2), hpos'⟩)⁻¹ := by
      have hpos'' := reflectSite_mem_positive_of_negative hT hneg'
      rw [reflectPosToNeg_apply N T L hT V_plus hneg' a.2]
      have heq : (⟨(ReflectSite.reflectSite a.1, a.2), hpos''⟩ :
          FiniteLinkIndex (PeriodicSite T L) (positiveSites T L)) =
          ⟨(b.1, b.2), hpos'⟩ := by
        congr 1
        rw [hinv, ha_val2]
      rw [heq, ha_val2, if_pos hμ]
    rw [hrt]
    rw [repCharacter_inv (ρ (dual (w a))) (h_unitary (dual (w a)))]
    rfl
  · -- spatial: w*(b) = w(a), link unchanged
    have hμ' : a.2 ≠ 0 := by rw [ha_val2]; exact hμ
    have hwstar : fullReflectReindexLink T L hT ι dual w b = w a := by
      rw [fullReflectReindexLink_pos_spatial T L hT ι dual w hb hμ]
    rw [hwstar]
    have hrt : reflectPosToNeg N T L V_plus ⟨(a.1, a.2), hneg'⟩ =
        V_plus ⟨(b.1, b.2), hpos'⟩ := by
      have hpos'' := reflectSite_mem_positive_of_negative hT hneg'
      rw [reflectPosToNeg_apply N T L hT V_plus hneg' a.2]
      have heq : (⟨(ReflectSite.reflectSite a.1, a.2), hpos''⟩ :
          FiniteLinkIndex (PeriodicSite T L) (positiveSites T L)) =
          ⟨(b.1, b.2), hpos'⟩ := by
        congr 1
        rw [hinv, ha_val2]
      rw [heq, ha_val2, if_neg hμ]
    rw [hrt]
    rw [hdual (w a)]
    rfl

#print axioms charFactorNegAll_eq_star_charFactorPosAll_link_fullReflect

set_option maxHeartbeats 1000000 in
/-- **Step 4 product identity (full-lattice).** The negative-link character
factor at `reflectPosToNeg V⁺` (with weight `w`) equals `star` of the
positive-link character factor at `V⁺` (with weight
`w* = fullReflectReindexLink`):
`charFactorNegAll dual w (reflectPosToNeg V⁺) = star (charFactorPosAll (fullReflectReindexLink dual w) V⁺)`.

This reindexes the product over `allLinkNeg` to a product over `allLinkPos`
via the reflection bijection `(n, μ) ↦ (reflectSite n, μ)` (an involution
mapping neg ↔ pos), using `Finset.prod_bij` and the per-link identity
`charFactorNegAll_eq_star_charFactorPosAll_link_fullReflect`.

This is the full-lattice analogue of
`charFactorNeg_eq_star_charFactorPos_fullReflect` (which works for
`InterfaceLink T L`).  0 sorries, 0 custom axioms. -/
lemma charFactorNegAll_eq_star_charFactorPosAll_fullReflect
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : (PeriodicSite T L × Fin 4) → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    charFactorNegAll N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus) =
    star (charFactorPosAll N T L ι dims ρ (fullReflectReindexLink T L hT ι dual w) V_plus) := by
  simp only [charFactorNegAll, charFactorPosAll]
  -- Push star inside the charFactorPosAll product on the RHS
  rw [show star (∏ b ∈ allLinkPos T L,
      (if hpos : b.1 ∈ positiveSites T L then
        repCharacter (ρ (fullReflectReindexLink T L hT ι dual w b)) (V_plus ⟨(b.1, b.2), hpos⟩)
      else (1 : ℂ))) =
      ∏ b ∈ allLinkPos T L,
      (if hpos : b.1 ∈ positiveSites T L then
        star (repCharacter (ρ (fullReflectReindexLink T L hT ι dual w b)) (V_plus ⟨(b.1, b.2), hpos⟩))
      else (1 : ℂ)) from by
      rw [← starRingEnd_apply, map_prod]
      refine Finset.prod_congr rfl (fun b hb => ?_)
      rw [starRingEnd_apply]
      split_ifs with h
      · rfl
      · simp]
  -- Now both sides are products; reindex neg → pos via (reflectSite a.1, a.2)
  refine Finset.prod_bij (fun a ha => (ReflectSite.reflectSite a.1, a.2)) ?hi ?i_inj ?i_surj ?h
  · -- hi : (reflectSite a.1, a.2) maps allLinkNeg into allLinkPos
    intro a ha
    rw [allLinkPos_mem_iff]
    exact reflectSite_mem_positive_of_negative hT ((allLinkNeg_mem_iff T L a).mp ha)
  · -- i_inj : (reflectSite a₁.1, a₁.2) = (reflectSite a₂.1, a₂.2) → a₁ = a₂
    intro a₁ ha₁ a₂ ha₂ heq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
    have h1' : a₁.1 = a₂.1 := by
      have hcc := congrArg ReflectSite.reflectSite h1
      rw [ReflectSite.involution a₁.1, ReflectSite.involution a₂.1] at hcc
      exact hcc
    exact Prod.ext h1' h2
  · -- i_surj : (reflectSite b.1, b.2) is surjective onto allLinkPos (involution)
    intro b hb
    refine ⟨(ReflectSite.reflectSite b.1, b.2), ?_, ?_⟩
    · -- (reflectSite b.1, b.2) ∈ allLinkNeg
      rw [allLinkNeg_mem_iff]
      exact reflectSite_mem_negative_of_positive hT ((allLinkPos_mem_iff T L b).mp hb)
    · -- (reflectSite (reflectSite b.1), b.2) = b
      simp [ReflectSite.involution]
  · -- h : per-link identity f a = g (reflectSite a.1, a.2)
    intro a ha
    have hb : (ReflectSite.reflectSite a.1, a.2) ∈ allLinkPos T L := by
      rw [allLinkPos_mem_iff]
      exact reflectSite_mem_positive_of_negative hT ((allLinkNeg_mem_iff T L a).mp ha)
    have hlink := charFactorNegAll_eq_star_charFactorPosAll_link_fullReflect
      N T L hT ι dims ρ h_unitary dual hdual w V_plus
      (ReflectSite.reflectSite a.1, a.2) hb
    have hinvol : ReflectSite.reflectSite (ReflectSite.reflectSite a.1) = a.1 :=
      ReflectSite.involution a.1
    rw [hinvol] at hlink
    exact hlink

#print axioms charFactorNegAll_eq_star_charFactorPosAll_fullReflect

/-- The `star` (complex conjugate) version of
`charFactorNegAll_eq_star_charFactorPosAll_fullReflect`:
`star(charFactorNegAll dual w (reflectPosToNeg V⁺)) = charFactorPosAll (fullReflectReindexLink dual w) V⁺`.
This follows by applying `star` to both sides and using `star(star x) = x`
(`Complex.conj_conj`).

This is the full-lattice analogue of
`star_charFactorNeg_eq_charFactorPos_fullReflect` (which works for
`InterfaceLink T L`).  0 sorries, 0 custom axioms. -/
lemma star_charFactorNegAll_eq_charFactorPosAll_fullReflect
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : (PeriodicSite T L × Fin 4) → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    star (charFactorNegAll N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus)) =
    charFactorPosAll N T L ι dims ρ (fullReflectReindexLink T L hT ι dual w) V_plus := by
  have h := charFactorNegAll_eq_star_charFactorPosAll_fullReflect
    N T L hT ι dims ρ h_unitary dual hdual w V_plus
  rw [h]
  exact Complex.conj_conj _

#print axioms star_charFactorNegAll_eq_charFactorPosAll_fullReflect
