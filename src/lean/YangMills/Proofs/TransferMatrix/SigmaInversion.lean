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

/-!
## Matrix-element lift of the σ-inversion identity (step iv-b3′, §8.11.99/§8.11.103)

The character-level identity `charFactorNeg_thetaReindex_eq_charFactorPos` lifts to
individual matrix elements.  This requires TWO hypotheses beyond the character-level
`hdual` (see design doc §8.11.103):
- `hdims : ∀ i, dims (dual i) = dims i` (dual preserves dimension);
- `hdual_me` : the ELEMENTWISE dual-conjugation identity
  `(ρ (dual i) g) (cast a) (cast b) = conj ((ρ i) g a b)`
  (satisfied when the dual rep is the conjugate rep — standard for SU(N) Peter–Weyl).

Index-swap subtlety: for time-like negative links the matrix indices SWAP
(`(ρ (dual i) g⁻¹) (cast b) (cast a) = (ρ i) g a b` via `repMatrixElement_inv` +
`hdual_me` + `conj_conj`), while for spatial negative links they do NOT
(`(ρ (dual (dual i)) g) (cast a) (cast b) = (ρ i) g a b` via double `hdual_me`).
Hence `thetaReindexMatrixElem` swaps the index pair for negative time-like links only.
-/

/-- Congruence for representation matrix elements across equal representation labels:
if `i₁ = i₂` and the matrix indices agree on `.val`, the matrix elements agree.
This avoids dependent-type `rw` failures ("motive is not type correct") when comparing
`(ρ i₁ g) a b` with `(ρ i₂ g) a' b'` where `a' = Fin.cast _ a`. -/
lemma repMatrixElement_apply_congr {ι : Type} {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    {i₁ i₂ : ι} (h : i₁ = i₂) (g : SU N)
    {a : Fin (dims i₁)} {a' : Fin (dims i₂)} (ha : a.val = a'.val)
    {b : Fin (dims i₁)} {b' : Fin (dims i₂)} (hb : b.val = b'.val) :
    (ρ i₁ g) a b = (ρ i₂ g) a' b' := by
  subst h
  rw [Fin.ext ha, Fin.ext hb]

#print axioms repMatrixElement_apply_congr

/-- **Group-level time-like identity.** Under elementwise dual-conjugation (`hdual_me`),
the dual-rep matrix element at `g⁻¹` with SWAPPED indices equals the original matrix
element at `g`: `(ρ (dual i) g⁻¹) (cast b) (cast a) = (ρ i) g a b`.
Proof: `repMatrixElement_inv` gives `conj` of the swapped dual element at `g`;
`hdual_me` turns that into `conj (conj ((ρ i) g a b))`; `conj_conj` closes. -/
lemma repMatrixElement_dual_inv_eq {ι : Type} {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (i : ι) (g : SU N) (a b : Fin (dims i)) :
    (ρ (dual i) g⁻¹) (Fin.cast (hdims i).symm b) (Fin.cast (hdims i).symm a) =
      (ρ i) g a b := by
  rw [repMatrixElement_inv (ρ (dual i)) (h_unitary (dual i)) g
      (Fin.cast (hdims i).symm b) (Fin.cast (hdims i).symm a),
    hdual_me i g a b, Complex.conj_conj]

#print axioms repMatrixElement_dual_inv_eq

/-- **Group-level spatial identity.** Under elementwise dual-conjugation (`hdual_me`),
the double-dual-rep matrix element at `g` (indices cast through `dims (dual (dual i))
= dims (dual i) = dims i`) equals the original matrix element:
`(ρ (dual (dual i)) g) (cast a) (cast b) = (ρ i) g a b`.
Proof: `hdual_me` twice + `conj_conj`; the two cast chains are identified via
`repMatrixElement_apply_congr` (their `.val`s agree). -/
lemma repMatrixElement_dual_dual_eq {ι : Type} {dims : ι → ℕ}
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (i : ι) (g : SU N) (a b : Fin (dims i)) :
    (ρ (dual (dual i)) g)
      (Fin.cast ((hdims (dual i)).trans (hdims i)).symm a)
      (Fin.cast ((hdims (dual i)).trans (hdims i)).symm b) = (ρ i) g a b := by
  have h1 := hdual_me (dual i) g (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b)
  rw [hdual_me i g a b, Complex.conj_conj] at h1
  exact (repMatrixElement_apply_congr (N := N) ρ rfl g
    (by simp only [Fin.coe_cast]) (by simp only [Fin.coe_cast])).trans h1

#print axioms repMatrixElement_dual_dual_eq

/-- The positive-link matrix-element factor: `∏_{l ∈ L_U} (ρ (w l) (U⁺_l)) (κ l).1 (κ l).2`.
Matrix-element analogue of `charFactorPos` (Bridge.lean), with `κ` assigning a pair of
matrix indices to each interface link. -/
noncomputable def matrixElemFactorPos (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) : ℂ :=
  ∏ l ∈ interfaceLinkPos T L,
    if hpos : l.val.1 ∈ positiveSites T L then
      (ρ (w l) (U_plus ⟨(l.val.1, l.val.2), hpos⟩)) (κ l).1 (κ l).2
    else 1

#print axioms matrixElemFactorPos

/-- The negative-link matrix-element factor:
`∏_{l ∈ L_V} (ρ (dual (w l)) (U⁻_l)) (cast (κ l).1) (cast (κ l).2)`.
Matrix-element analogue of `charFactorNeg`; the indices are cast into
`Fin (dims (dual (w l)))` via `hdims`. -/
noncomputable def matrixElemFactorNeg (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) : ℂ :=
  ∏ l ∈ interfaceLinkNeg T L,
    if hneg : l.val.1 ∈ negativeSites T L then
      (ρ (dual (w l)) (U_minus ⟨(l.val.1, l.val.2), hneg⟩))
        (Fin.cast (hdims (w l)).symm (κ l).1) (Fin.cast (hdims (w l)).symm (κ l).2)
    else 1

#print axioms matrixElemFactorNeg

/-- Trichotomy: an interface link that is neither positive-time nor time-0 is
negative-time.  Follows from `signedTime_trichotomy` by `omega`. -/
lemma mem_interfaceLinkNeg_of_not_pos_not_int (T L : ℕ) [NeZero T] [NeZero L]
    {l : InterfaceLink T L}
    (hpos : l ∉ interfaceLinkPos T L) (hint : l ∉ interfaceLinkInt T L) :
    l ∈ interfaceLinkNeg T L := by
  rw [interfaceLinkPos, Finset.mem_filter] at hpos
  rw [interfaceLinkInt, Finset.mem_filter] at hint
  rw [interfaceLinkNeg, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h1 : ¬ signedTime T l.val.1.time > 0 := fun h => hpos ⟨Finset.mem_univ _, h⟩
  have h2 : ¬ signedTime T l.val.1.time = 0 := fun h => hint ⟨Finset.mem_univ _, h⟩
  omega

#print axioms mem_interfaceLinkNeg_of_not_pos_not_int

/-- The matrix-element reindexing `θκ` accompanying `thetaReindex` (step iv-b3′).
For a link `l`:
- `l ∈ interfaceLinkPos ∪ interfaceLinkInt`: `θκ(l) = κ(l)` (cast along `θw(l) = w(l)`);
- `l ∈ interfaceLinkNeg`, `μ(l) = 0` (time-like): `θκ(l) = SWAP(κ(φ(l)))` (cast along
  `θw(l) = w(φ(l))`) — the swap matches the index swap in `repMatrixElement_dual_inv_eq`;
- `l ∈ interfaceLinkNeg`, `μ(l) ≠ 0` (spatial): `θκ(l) = κ(φ(l))` unswapped (cast along
  `θw(l) = dual(w(φ(l)))` and `hdims`) — matching `repMatrixElement_dual_dual_eq`.

Defined with `l` as an explicit last argument so the equation lemma rewrites applied
occurrences directly. -/
noncomputable def thetaReindexMatrixElem (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ) (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (l : InterfaceLink T L) :
    Fin (dims (thetaReindex T L hT ι dual w l)) ×
      Fin (dims (thetaReindex T L hT ι dual w l)) :=
  if hl_pos : l ∈ interfaceLinkPos T L then
    (Fin.cast (congrArg dims (thetaReindex_pos T L hT ι dual w hl_pos)).symm (κ l).1,
     Fin.cast (congrArg dims (thetaReindex_pos T L hT ι dual w hl_pos)).symm (κ l).2)
  else if hl_int : l ∈ interfaceLinkInt T L then
    (Fin.cast (congrArg dims (thetaReindex_int T L hT ι dual w hl_int)).symm (κ l).1,
     Fin.cast (congrArg dims (thetaReindex_int T L hT ι dual w hl_int)).symm (κ l).2)
  else if hμ : l.val.2 = 0 then
    (Fin.cast (congrArg dims (thetaReindex_neg_time T L hT ι dual w
        (mem_interfaceLinkNeg_of_not_pos_not_int T L hl_pos hl_int) hμ)).symm
      (κ (reflectInterfaceLink T L hT l)).2,
     Fin.cast (congrArg dims (thetaReindex_neg_time T L hT ι dual w
        (mem_interfaceLinkNeg_of_not_pos_not_int T L hl_pos hl_int) hμ)).symm
      (κ (reflectInterfaceLink T L hT l)).1)
  else
    (Fin.cast ((congrArg dims (thetaReindex_neg_spatial T L hT ι dual w
        (mem_interfaceLinkNeg_of_not_pos_not_int T L hl_pos hl_int) hμ)).trans
      (hdims (w (reflectInterfaceLink T L hT l)))).symm
      (κ (reflectInterfaceLink T L hT l)).1,
     Fin.cast ((congrArg dims (thetaReindex_neg_spatial T L hT ι dual w
        (mem_interfaceLinkNeg_of_not_pos_not_int T L hl_pos hl_int) hμ)).trans
      (hdims (w (reflectInterfaceLink T L hT l)))).symm
      (κ (reflectInterfaceLink T L hT l)).2)

#print axioms thetaReindexMatrixElem

/-- Branch values of `thetaReindexMatrixElem` for a negative TIME-LIKE link:
the index pair is the SWAPPED pair at the reflected link (stated at `.val` level to be
proof-irrelevance-immune). -/
lemma thetaReindexMatrixElem_neg_time_vals (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ) (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkNeg T L) (hμ : l.val.2 = 0) :
    (thetaReindexMatrixElem T L hT ι dims dual hdims w κ l).1.val =
      (κ (reflectInterfaceLink T L hT l)).2.val ∧
    (thetaReindexMatrixElem T L hT ι dims dual hdims w κ l).2.val =
      (κ (reflectInterfaceLink T L hT l)).1.val := by
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
  simp only [thetaReindexMatrixElem, dif_neg hnpos, dif_neg hnint, dif_pos hμ]
  exact ⟨rfl, rfl⟩

#print axioms thetaReindexMatrixElem_neg_time_vals

/-- Branch values of `thetaReindexMatrixElem` for a negative SPATIAL link:
the index pair is the UNSWAPPED pair at the reflected link (stated at `.val` level). -/
lemma thetaReindexMatrixElem_neg_spatial_vals (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ) (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkNeg T L) (hμ : l.val.2 ≠ 0) :
    (thetaReindexMatrixElem T L hT ι dims dual hdims w κ l).1.val =
      (κ (reflectInterfaceLink T L hT l)).1.val ∧
    (thetaReindexMatrixElem T L hT ι dims dual hdims w κ l).2.val =
      (κ (reflectInterfaceLink T L hT l)).2.val := by
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
  simp only [thetaReindexMatrixElem, dif_neg hnpos, dif_neg hnint, dif_neg hμ]
  exact ⟨rfl, rfl⟩

#print axioms thetaReindexMatrixElem_neg_spatial_vals

set_option maxHeartbeats 1000000 in
/-- **Per-link matrix-element identity (step iv-b3′ core).** For `b ∈ interfaceLinkPos`,
the negative-link matrix-element factor at the reflected link `reflectInterfaceLink b`
(equipped with the reindexings `θw`, `θκ`) equals the positive-link matrix-element
factor at `b`:
`(ρ (dual (θw(φ b)))) (reflectPosToNeg V⁺_{φ b}) (cast (θκ(φ b)).1) (cast (θκ(φ b)).2)
  = (ρ (w b)) (V⁺_b) (κ b).1 (κ b).2`.

Case analysis on `μ(b) = 0` (time-like) vs `μ(b) ≠ 0` (spatial):
- **Time-like**: `θw(φ b) = w b`, link inverted, indices SWAPPED — closed by
  `repMatrixElement_dual_inv_eq` (= `repMatrixElement_inv` + `hdual_me` + `conj_conj`).
- **Spatial**: `θw(φ b) = dual(w b)`, link unchanged, indices UNSWAPPED — closed by
  `repMatrixElement_dual_dual_eq` (double `hdual_me` + `conj_conj`).

The dependent-type comparisons are handled at the `.val` level via
`repMatrixElement_apply_congr` and the branch val-lemmas
`thetaReindexMatrixElem_neg_time_vals` / `_neg_spatial_vals`.
0 sorries, 0 custom axioms. -/
lemma matrixElemFactorNeg_thetaReindex_link_eq
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (b : InterfaceLink T L) (hb : b ∈ interfaceLinkPos T L) :
    (if hneg : (reflectInterfaceLink T L hT b).val.1 ∈ negativeSites T L then
       (ρ (dual (thetaReindex T L hT ι dual w (reflectInterfaceLink T L hT b)))
         (reflectPosToNeg N T L V_plus ⟨((reflectInterfaceLink T L hT b).val.1,
            (reflectInterfaceLink T L hT b).val.2), hneg⟩))
         (Fin.cast (hdims _).symm
           (thetaReindexMatrixElem T L hT ι dims dual hdims w κ
             (reflectInterfaceLink T L hT b)).1)
         (Fin.cast (hdims _).symm
           (thetaReindexMatrixElem T L hT ι dims dual hdims w κ
             (reflectInterfaceLink T L hT b)).2)
     else 1) =
    (if hpos : b.val.1 ∈ positiveSites T L then
       (ρ (w b) (V_plus ⟨(b.val.1, b.val.2), hpos⟩)) (κ b).1 (κ b).2
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
  · -- time-like: θw(φ b) = w b, link inverted, indices swapped
    have hμ' : l.val.2 = 0 := by rw [hl_val2]; exact hμ
    have hθ : thetaReindex T L hT ι dual w l = w b := by
      rw [thetaReindex_neg_time T L hT ι dual w hb_neg hμ', reflectInterfaceLink_involution]
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
    have hmain := repMatrixElement_dual_inv_eq (N := N) ρ h_unitary dual hdims hdual_me (w b)
      (V_plus ⟨(b.val.1, b.val.2), hpos'⟩) (κ b).1 (κ b).2
    rw [← hmain]
    apply repMatrixElement_apply_congr (N := N) ρ (congrArg dual hθ)
      (V_plus ⟨(b.val.1, b.val.2), hpos'⟩)⁻¹
    · simp only [Fin.coe_cast]
      rw [(thetaReindexMatrixElem_neg_time_vals T L hT ι dims dual hdims w κ hb_neg hμ').1,
        hl_def, reflectInterfaceLink_involution]
    · simp only [Fin.coe_cast]
      rw [(thetaReindexMatrixElem_neg_time_vals T L hT ι dims dual hdims w κ hb_neg hμ').2,
        hl_def, reflectInterfaceLink_involution]
  · -- spatial: θw(φ b) = dual(w b), link unchanged, indices unswapped
    have hμ' : l.val.2 ≠ 0 := by rw [hl_val2]; exact hμ
    have hθ : thetaReindex T L hT ι dual w l = dual (w b) := by
      rw [thetaReindex_neg_spatial T L hT ι dual w hb_neg hμ', reflectInterfaceLink_involution]
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
    have hmain := repMatrixElement_dual_dual_eq (N := N) ρ dual hdims hdual_me (w b)
      (V_plus ⟨(b.val.1, b.val.2), hpos'⟩) (κ b).1 (κ b).2
    rw [← hmain]
    apply repMatrixElement_apply_congr (N := N) ρ (congrArg dual hθ)
      (V_plus ⟨(b.val.1, b.val.2), hpos'⟩)
    · simp only [Fin.coe_cast]
      rw [(thetaReindexMatrixElem_neg_spatial_vals T L hT ι dims dual hdims w κ hb_neg hμ').1,
        hl_def, reflectInterfaceLink_involution]
    · simp only [Fin.coe_cast]
      rw [(thetaReindexMatrixElem_neg_spatial_vals T L hT ι dims dual hdims w κ hb_neg hμ').2,
        hl_def, reflectInterfaceLink_involution]

#print axioms matrixElemFactorNeg_thetaReindex_link_eq

set_option maxHeartbeats 1000000 in
/-- **Matrix-element σ-inversion identity (step iv-b3′ main).** The negative-link
matrix-element factor at the reflected configuration `reflectPosToNeg V⁺`, equipped with
the reindexed weight `θw = thetaReindex dual w` and reindexed indices
`θκ = thetaReindexMatrixElem κ`, equals the positive-link matrix-element factor at `V⁺`
with the original weight and indices:
`matrixElemFactorNeg dual hdims (θw) (θκ) (reflectPosToNeg V⁺)
  = matrixElemFactorPos w κ V⁺`.

This reindexes the product over `interfaceLinkNeg` to a product over `interfaceLinkPos`
via the reflection bijection `reflectInterfaceLink` (an involution), using
`Finset.prod_bij` and the per-link identity
`matrixElemFactorNeg_thetaReindex_link_eq`.  It is the matrix-element lift of
`charFactorNeg_thetaReindex_eq_charFactorPos`, and the pointwise identity that — combined
with `crossing_prod_boltzmann_matrixElement_expansion` and interface Schur orthogonality —
gives the sum-of-squares form of the transfer-matrix kernel (§8.11.99).
0 sorries, 0 custom axioms. -/
lemma matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    matrixElemFactorNeg N T L ι dims ρ dual hdims (thetaReindex T L hT ι dual w)
      (thetaReindexMatrixElem T L hT ι dims dual hdims w κ)
      (reflectPosToNeg N T L V_plus) =
    matrixElemFactorPos N T L ι dims ρ w κ V_plus := by
  simp only [matrixElemFactorNeg, matrixElemFactorPos]
  refine Finset.prod_bij (fun a _ => reflectInterfaceLink T L hT a) ?hi ?i_inj ?i_surj ?h
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
    have hlink := matrixElemFactorNeg_thetaReindex_link_eq N T L hT ι dims ρ h_unitary dual
      hdims hdual_me w κ V_plus (reflectInterfaceLink T L hT a) hb
    rw [reflectInterfaceLink_involution T L hT a] at hlink
    exact hlink

#print axioms matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos

/-- The `star` version of `matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos`. -/
lemma matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos_star
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    star (matrixElemFactorNeg N T L ι dims ρ dual hdims (thetaReindex T L hT ι dual w)
      (thetaReindexMatrixElem T L hT ι dims dual hdims w κ)
      (reflectPosToNeg N T L V_plus)) =
    star (matrixElemFactorPos N T L ι dims ρ w κ V_plus) :=
  congrArg star (matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos N T L hT ι dims ρ
    h_unitary dual hdims hdual_me w κ V_plus)

#print axioms matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos_star

/-- The positive matrix-element Fourier coefficient
`A^{ME}_{w,κ}(u⁰) = ∫_{U⁺} ofReal(ψ(merge(U⁺,u⁰))·exp(-β·S⁺(merge(U⁺,u⁰))/2)) ·
matrixElemFactorPos(w, κ, U⁺) ∂μ⁺`.
Matrix-element analogue of `fourierCoeffPos` (Fubini.lean). -/
noncomputable def fourierCoeffPosME (N T L : ℕ) [NeZero T] [NeZero L]
    (β : ℝ) (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) : ℂ :=
  ∫ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    Complex.ofReal (ψ (mergePosInterface N T L Upos u0) *
      Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
    matrixElemFactorPos N T L ι dims ρ w κ Upos
  ∂ haarMeasurePositive N T L

#print axioms fourierCoeffPosME

/-- The negative matrix-element Fourier coefficient
`B^{ME}_{w,κ}(u⁰) = ∫_{V⁺} ofReal(ψ(merge(V⁺,σ(u⁰)))·exp(-β·S⁺(merge(V⁺,σ(u⁰)))/2)) ·
star(matrixElemFactorNeg(dual, hdims, w, κ, reflectPosToNeg V⁺)) ∂μ⁺`.
Matrix-element analogue of `fourierCoeffNeg` (Fubini.lean). -/
noncomputable def fourierCoeffNegME (N T L : ℕ) [NeZero T] [NeZero L]
    (β : ℝ) (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) : ℂ :=
  ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) *
      Real.exp (-β * osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L u0)) / 2)) *
    star (matrixElemFactorNeg N T L ι dims ρ dual hdims w κ (reflectPosToNeg N T L V_plus))
  ∂ haarMeasurePositive N T L

#print axioms fourierCoeffNegME

set_option maxHeartbeats 1000000 in
/-- **Matrix-element Fourier coefficient σ-inversion identity (step iv-b3′, Fourier
level).**  The negative matrix-element Fourier coefficient at the reindexed weight and
indices `(θw, θκ)` equals the conjugate of the positive matrix-element Fourier
coefficient at `σ(u⁰)`:
`fourierCoeffNegME(θw, θκ, u⁰) = star(fourierCoeffPosME(w, κ, σ(u⁰)))`.

This is the matrix-element lift of
`fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos`, and is exactly the relation
`B_{Rkl}(u⁰) = conj(A(σ u⁰))` of the integrated assembly (§8.11.99 KEY OBSERVATION).
Proof: `star` commutes with the integral (`integral_conj`) and distributes over the
product with the real Boltzmann prefactor (`star_mul'` + `conj_ofReal`), reducing to
the pointwise identity `matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos_star`.
0 sorries, 0 custom axioms. -/
lemma fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffNegME N T L β ψ ι dims ρ dual hdims (thetaReindex T L hT ι dual w)
      (thetaReindexMatrixElem T L hT ι dims dual hdims w κ) u0 =
    star (fourierCoeffPosME N T L β ψ ι dims ρ w κ (sigmaInterface N T L u0)) := by
  simp only [fourierCoeffNegME, fourierCoeffPosME]
  rw [← starRingEnd_apply, ← integral_conj]
  refine integral_congr_ae (ae_of_all (haarMeasurePositive N T L) ?_)
  intro V
  dsimp only
  rw [RingHom.map_mul, Complex.conj_ofReal, starRingEnd_apply,
    matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos_star N T L hT ι dims ρ
      h_unitary dual hdims hdual_me w κ V]

#print axioms fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME

/-- **σ-invisibility of the positive matrix-element Fourier coefficient.**  When the
test function `ψ = g_posInterface N T L hT β f` with `f` satisfying
`dependsOnlyOnPosSpatialInterface`, `A^{ME}_{w,κ}(u⁰) = fourierCoeffPosME(w, κ, u⁰)` is
invisible to the σ twist: `A^{ME}_{w,κ}(σ(u⁰)) = A^{ME}_{w,κ}(u⁰)`.  Mirrors
`fourierCoeffPos_sigma_invisible`: the `u⁰`-dependence of the integrand is only through
`g` and `S⁺` (both σ-invisible), while `matrixElemFactorPos` depends only on `U⁺`.
Combined with `fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME` this gives
`B^{ME}_{θw,θκ}(u⁰) = star(A^{ME}_{w,κ}(u⁰))` — the sum-of-squares pairing of §8.11.99.
0 sorries, 0 custom axioms. -/
lemma fourierCoeffPosME_sigma_invisible (hT : Odd T)
    (β : ℝ) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffPosME N T L β (g_posInterface N T L hT β f) ι dims ρ w κ
        (sigmaInterface N T L u0) =
    fourierCoeffPosME N T L β (g_posInterface N T L hT β f) ι dims ρ w κ u0 := by
  have hpointwise : ∀ (Upos : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Complex.ofReal (g_posInterface N T L hT β f (mergePosInterface N T L Upos (sigmaInterface N T L u0)) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos (sigmaInterface N T L u0)) / 2)) *
      matrixElemFactorPos N T L ι dims ρ w κ Upos =
      Complex.ofReal (g_posInterface N T L hT β f (mergePosInterface N T L Upos u0) *
        Real.exp (-β * osPositiveOfPosInterface N T L β (mergePosInterface N T L Upos u0) / 2)) *
      matrixElemFactorPos N T L ι dims ρ w κ Upos := by
    intro Upos
    rw [g_posInterface_sigma_invisible N T L β hT f hf Upos u0,
        osPositiveOfPosInterface_sigma_invariant N T L β hT Upos u0]
  unfold fourierCoeffPosME
  exact integral_congr_ae (ae_of_all _ hpointwise)

#print axioms fourierCoeffPosME_sigma_invisible

/-- **The sum-of-squares pairing (step iv-b3′, assembled).**  For the σ-invisible test
function `ψ = g_posInterface f`, the negative matrix-element Fourier coefficient at the
reindexed `(θw, θκ)` equals the conjugate of the positive one at the SAME `u⁰`:
`B^{ME}_{θw,θκ}(u⁰) = star(A^{ME}_{w,κ}(u⁰))`.
This is the exact pairing needed for the RP quadratic form to become
`∑_{R,k,l} c_R · ∫_{u⁰} |A|² · (interface factor) ≥ 0` (§8.11.99).
0 sorries, 0 custom axioms. -/
lemma fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME_of_sigma_invisible
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (h_unitary : ∀ i, IsUnitaryRepresentation (ρ i))
    (dual : ι → ι) (hdims : ∀ i, dims (dual i) = dims i)
    (hdual_me : ∀ i (g : SU N) (a b : Fin (dims i)),
      (ρ (dual i) g) (Fin.cast (hdims i).symm a) (Fin.cast (hdims i).symm b) =
        conj ((ρ i) g a b))
    (w : InterfaceLink T L → ι)
    (κ : ∀ l : InterfaceLink T L, Fin (dims (w l)) × Fin (dims (w l)))
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffNegME N T L β (g_posInterface N T L hT β f) ι dims ρ dual hdims
      (thetaReindex T L hT ι dual w) (thetaReindexMatrixElem T L hT ι dims dual hdims w κ) u0 =
    star (fourierCoeffPosME N T L β (g_posInterface N T L hT β f) ι dims ρ w κ u0) := by
  rw [fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME N T L β hT _ ι dims ρ
    h_unitary dual hdims hdual_me w κ u0,
    fourierCoeffPosME_sigma_invisible N T L hT β f hf ι dims ρ w κ u0]

#print axioms fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME_of_sigma_invisible


