/-
# Transfer Matrix: Lemma 3 Sigma-Inversion
-/

import YangMills.Proofs.TransferMatrix.KeyIdentity

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
## Lemma 3: σ-inversion with reindexing

The reindexing `θ : (InterfaceLink → ι) → (InterfaceLink → ι)` and the pointwise
character identity `star(charFactorNeg dual (θw) (reflectPosToNeg V⁺)) =
star(charFactorPos w V⁺)`.  See `docs/transfer_matrix_positivity_design.md` §8.11.22.
-/

/-- The reindexing `θ : (InterfaceLink → ι) → (InterfaceLink → ι)` for the σ-inversion
lemma (Lemma 3).  For a link `l`:
- `l ∈ interfaceLinkPos ∪ interfaceLinkInt`: `θw(l) = w(l)` (unchanged);
- `l ∈ interfaceLinkNeg`, `μ(l) = 0` (time-like): `θw(l) = w(φ(l))` where `φ = reflectInterfaceLink`;
- `l ∈ interfaceLinkNeg`, `μ(l) ≠ 0` (spatial): `θw(l) = dual(w(φ(l)))`.

This reindexing makes the negative-link character product, after reflection of the
link variables, match the positive-link character product (up to the per-link
character identities `repCharacter_inv` and `hdual`). -/
noncomputable def thetaReindex (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι) :
    InterfaceLink T L → ι :=
  fun l =>
    if hl_pos : l ∈ interfaceLinkPos T L then w l
    else if hl_int : l ∈ interfaceLinkInt T L then w l
    else if hμ : l.val.2 = 0 then w (reflectInterfaceLink T L hT l)
    else dual (w (reflectInterfaceLink T L hT l))

#print axioms thetaReindex

/-- For a positive-time interface link, `θw(l) = w(l)`. -/
lemma thetaReindex_pos (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkPos T L) :
    thetaReindex T L hT ι dual w l = w l := by
  show (if hl_pos : l ∈ interfaceLinkPos T L then w l
        else if hl_int : l ∈ interfaceLinkInt T L then w l
        else if hμ : l.val.2 = 0 then w (reflectInterfaceLink T L hT l)
        else dual (w (reflectInterfaceLink T L hT l))) = w l
  rw [dif_pos hl]

#print axioms thetaReindex_pos

/-- For an interface (time-0) interface link, `θw(l) = w(l)`. -/
lemma thetaReindex_int (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkInt T L) :
    thetaReindex T L hT ι dual w l = w l := by
  have hnpos : l ∉ interfaceLinkPos T L := by
    intro hpos
    rw [interfaceLinkPos, Finset.mem_filter] at hpos
    rw [interfaceLinkInt, Finset.mem_filter] at hl
    obtain ⟨_, hpos⟩ := hpos
    obtain ⟨_, hint⟩ := hl
    rw [hint] at hpos
    exact lt_irrefl _ hpos
  show (if hl_pos : l ∈ interfaceLinkPos T L then w l
        else if hl_int : l ∈ interfaceLinkInt T L then w l
        else if hμ : l.val.2 = 0 then w (reflectInterfaceLink T L hT l)
        else dual (w (reflectInterfaceLink T L hT l))) = w l
  rw [dif_neg hnpos, dif_pos hl]

#print axioms thetaReindex_int

/-- For a negative-time interface link `l` with `μ(l) = 0` (time-like),
`θw(l) = w(reflectInterfaceLink l)`. -/
lemma thetaReindex_neg_time (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkNeg T L) (hμ : l.val.2 = 0) :
    thetaReindex T L hT ι dual w l = w (reflectInterfaceLink T L hT l) := by
  have hnpos : l ∉ interfaceLinkPos T L := by
    intro hpos
    rw [interfaceLinkPos, Finset.mem_filter] at hpos
    rw [interfaceLinkNeg, Finset.mem_filter] at hl
    obtain ⟨_, hpos⟩ := hpos
    obtain ⟨_, hneg⟩ := hl
    exact lt_irrefl _ (lt_of_lt_of_le hpos (le_of_lt hneg))
  have hnint : l ∉ interfaceLinkInt T L := by
    intro hint
    rw [interfaceLinkInt, Finset.mem_filter] at hint
    rw [interfaceLinkNeg, Finset.mem_filter] at hl
    obtain ⟨_, hint⟩ := hint
    obtain ⟨_, hneg⟩ := hl
    rw [hint] at hneg
    exact lt_irrefl _ hneg
  show (if hl_pos : l ∈ interfaceLinkPos T L then w l
        else if hl_int : l ∈ interfaceLinkInt T L then w l
        else if hμ : l.val.2 = 0 then w (reflectInterfaceLink T L hT l)
        else dual (w (reflectInterfaceLink T L hT l))) = w (reflectInterfaceLink T L hT l)
  rw [dif_neg hnpos, dif_neg hnint, dif_pos hμ]

#print axioms thetaReindex_neg_time

/-- For a negative-time interface link `l` with `μ(l) ≠ 0` (spatial),
`θw(l) = dual(w(reflectInterfaceLink l))`. -/
lemma thetaReindex_neg_spatial (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkNeg T L) (hμ : l.val.2 ≠ 0) :
    thetaReindex T L hT ι dual w l = dual (w (reflectInterfaceLink T L hT l)) := by
  have hnpos : l ∉ interfaceLinkPos T L := by
    intro hpos
    rw [interfaceLinkPos, Finset.mem_filter] at hpos
    rw [interfaceLinkNeg, Finset.mem_filter] at hl
    obtain ⟨_, hpos⟩ := hpos
    obtain ⟨_, hneg⟩ := hl
    exact lt_irrefl _ (lt_of_lt_of_le hpos (le_of_lt hneg))
  have hnint : l ∉ interfaceLinkInt T L := by
    intro hint
    rw [interfaceLinkInt, Finset.mem_filter] at hint
    rw [interfaceLinkNeg, Finset.mem_filter] at hl
    obtain ⟨_, hint⟩ := hint
    obtain ⟨_, hneg⟩ := hl
    rw [hint] at hneg
    exact lt_irrefl _ hneg
  show (if hl_pos : l ∈ interfaceLinkPos T L then w l
        else if hl_int : l ∈ interfaceLinkInt T L then w l
        else if hμ : l.val.2 = 0 then w (reflectInterfaceLink T L hT l)
        else dual (w (reflectInterfaceLink T L hT l))) = dual (w (reflectInterfaceLink T L hT l))
  rw [dif_neg hnpos, dif_neg hnint, dif_neg hμ]

#print axioms thetaReindex_neg_spatial

set_option maxHeartbeats 1000000 in
/-- **Per-link character identity (Lemma 3 core).** For `b ∈ interfaceLinkPos`, the
negative-link character factor at the reflected link `reflectInterfaceLink b`
(equipped with the reindexing `θ`) equals the positive-link character factor at `b`:
`χ_{dual(θw(φ b))}(reflectPosToNeg V⁺_{φ b}) = χ_{w b}(V⁺_b)`.

This is proved by case analysis on `μ(b) = 0` (time-like) vs `μ(b) ≠ 0` (spatial):
- **Time-like** (`μ = 0`): `θw(φ b) = w b`, link inverted → `(V⁺_b)⁻¹`.
  `χ_{dual(w b)}((V⁺_b)⁻¹) = conj(χ_{dual(w b)}(V⁺_b))` (repCharacter_inv)
  `= conj(conj(χ_{w b}(V⁺_b)))` (hdual) `= χ_{w b}(V⁺_b)` (conj_conj).
- **Spatial** (`μ ≠ 0`): `θw(φ b) = dual(w b)`, link unchanged → `V⁺_b`.
  `χ_{dual(dual(w b))}(V⁺_b) = conj(χ_{dual(w b)}(V⁺_b))` (hdual)
  `= conj(conj(χ_{w b}(V⁺_b)))` (hdual) `= χ_{w b}(V⁺_b)` (conj_conj).

No `dual(dual(i)) = i` is needed — the double `conj` cancels via `conj_conj`.
0 sorries, 0 custom axioms. -/
lemma charFactorNeg_thetaReindex_link_eq
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
       repCharacter (ρ (dual (thetaReindex T L hT ι dual w (reflectInterfaceLink T L hT b))))
         (reflectPosToNeg N T L V_plus ⟨((reflectInterfaceLink T L hT b).val.1,
            (reflectInterfaceLink T L hT b).val.2), hneg⟩)
     else 1) =
    (if hpos : b.val.1 ∈ positiveSites T L then
       repCharacter (ρ (w b)) (V_plus ⟨(b.val.1, b.val.2), hpos⟩)
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
  · -- time-like: θw(φ b) = w b, link inverted
    have hμ' : l.val.2 = 0 := by rw [hl_val2]; exact hμ
    have hθ : thetaReindex T L hT ι dual w l = w b := by
      rw [thetaReindex_neg_time T L hT ι dual w hb_neg hμ', reflectInterfaceLink_involution]
    rw [hθ]
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
    rw [repCharacter_inv (ρ (dual (w b))) (h_unitary (dual (w b)))]
    rw [hdual (w b)]
    exact Complex.conj_conj _
  · -- spatial: θw(φ b) = dual(w b), link unchanged
    have hμ' : l.val.2 ≠ 0 := by rw [hl_val2]; exact hμ
    have hθ : thetaReindex T L hT ι dual w l = dual (w b) := by
      rw [thetaReindex_neg_spatial T L hT ι dual w hb_neg hμ', reflectInterfaceLink_involution]
    rw [hθ]
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
    rw [hdual (dual (w b)), hdual (w b)]
    exact Complex.conj_conj _

#print axioms charFactorNeg_thetaReindex_link_eq

set_option maxHeartbeats 1000000 in
/-- **Lemma 3 main pointwise identity.** The negative-link character factor at the
reflected configuration `reflectPosToNeg V⁺`, equipped with the reindexing weight
`θw = thetaReindex dual w`, equals the positive-link character factor at `V⁺` with
the original weight `w`:
`charFactorNeg dual (θw) (reflectPosToNeg V⁺) = charFactorPos w V⁺`.

This reindexes the product over `interfaceLinkNeg` to a product over `interfaceLinkPos`
via the reflection bijection `reflectInterfaceLink` (an involution mapping neg ↔ pos),
using `Finset.prod_bij` and the per-link identity `charFactorNeg_thetaReindex_link_eq`.
0 sorries, 0 custom axioms. -/
lemma charFactorNeg_thetaReindex_eq_charFactorPos
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    charFactorNeg N T L ι dims ρ dual (thetaReindex T L hT ι dual w) (reflectPosToNeg N T L V_plus) =
    charFactorPos N T L ι dims ρ w V_plus := by
  simp only [charFactorNeg, charFactorPos]
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
    have hlink := charFactorNeg_thetaReindex_link_eq N T L hT ι dims ρ h_unitary dual hdual w V_plus
      (reflectInterfaceLink T L hT a) hb
    rw [reflectInterfaceLink_involution T L hT a] at hlink
    exact hlink

#print axioms charFactorNeg_thetaReindex_eq_charFactorPos

/-- The `star` (complex conjugate) version of `charFactorNeg_thetaReindex_eq_charFactorPos`:
the conjugate of the negative-link character factor (with reindexing `θw`) at
`reflectPosToNeg V⁺` equals the conjugate of the positive-link character factor at `V⁺`.
0 sorries, 0 custom axioms. -/
lemma charFactorNeg_thetaReindex_eq_charFactorPos_star
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    star (charFactorNeg N T L ι dims ρ dual (thetaReindex T L hT ι dual w)
      (reflectPosToNeg N T L V_plus)) =
    star (charFactorPos N T L ι dims ρ w V_plus) := by
  exact congrArg star (charFactorNeg_thetaReindex_eq_charFactorPos N T L hT ι dims ρ
    h_unitary dual hdual w V_plus)

#print axioms charFactorNeg_thetaReindex_eq_charFactorPos_star

set_option maxHeartbeats 1000000 in
/-- **Lemma 3 sub-step 4: Fourier coefficient identity.** The negative Fourier coefficient
at the reindexed weight `θw = thetaReindex dual w` equals the conjugate of the positive
Fourier coefficient at `σ(u⁰)`:
`fourierCoeffNeg(θw, u⁰) = star(fourierCoeffPos(w, σ(u⁰)))`.

This follows from the main pointwise identity `charFactorNeg_thetaReindex_eq_charFactorPos_star`
(`star(charFactorNeg dual θw (reflectPosToNeg V⁺)) = star(charFactorPos w V⁺)`) combined with
`star` commuting with the integral (`integral_conj`) and `star` distributing over the product
with the real Boltzmann prefactor (`star_mul'` + `conj_ofReal`).
0 sorries, 0 custom axioms. -/
lemma fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdual : ∀ i (g : SU N),
      repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g))
    (w : InterfaceLink T L → ι)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffNeg N T L β ψ ι dims ρ dual (thetaReindex T L hT ι dual w) u0 =
    star (fourierCoeffPos N T L β ψ ι dims ρ w (sigmaInterface N T L u0)) := by
  simp only [fourierCoeffNeg, fourierCoeffPos]
  -- `star` is `@Star.star ℂ _`; `conj` (from `open scoped ComplexConjugate`) is `starRingEnd _`.
  -- They are defeq (`starRingEnd_apply := rfl`) but `rw` matches syntactically, so convert
  -- `star` → `starRingEnd _` (= `conj`) to use `integral_conj`, then convert back.
  rw [← starRingEnd_apply, ← integral_conj]
  refine integral_congr_ae (ae_of_all (haarMeasurePositive N T L) ?_)
  intro V
  dsimp only
  rw [RingHom.map_mul, Complex.conj_ofReal, starRingEnd_apply,
    charFactorNeg_thetaReindex_eq_charFactorPos_star N T L hT ι dims ρ h_unitary dual hdual w V]

#print axioms fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos


