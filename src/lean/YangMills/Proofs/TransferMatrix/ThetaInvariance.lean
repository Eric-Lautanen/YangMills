/-
# Transfer Matrix: Lemma 3 Theta Invariance
-/

import YangMills.Proofs.TransferMatrix.SigmaInversion

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
## Lemma 3 sub-step 5: invariance lemmas under the reindexing `θ`

The reindexing `θ = thetaReindex` leaves the positive-time and interface links
unchanged (`θw(l) = w(l)` for `l ∈ interfaceLinkPos ∪ interfaceLinkInt`), so the
positive-link character factor `charFactorPos`, the interface-link character factor
`charFactorInt`, and the positive Fourier coefficient `fourierCoeffPos` are all
invariant under `θ`.  These invariance lemmas are needed for the σ-inversion
sum reindexing (see `docs/transfer_matrix_positivity_design.md` §8.11.21).

**Key structural fact**: `thetaReindex` is IDEMPOTENT (`θ(θw) = θw`), not
involutive (`θ(θw) = w`).  It is a projection: it replaces `w|_{neg}` with a
function of `w|_{pos}` (via `reflectInterfaceLink` and `dual`), and leaves
`w|_{pos ∪ int}` unchanged.  Applying `θ` again gives the same result, since
`θw|_{pos ∪ int} = w|_{pos ∪ int}` and `θ(θw)|_{neg}` depends on
`θw|_{pos} = w|_{pos}` (same as `θw|_{neg}`).  Consequently `θ` is NOT a
bijection on `(InterfaceLink → ι)` — it forgets `w|_{neg}`.  The sum
reindexing `∑_w F(w)·G(w) = ∑_w F(θw)·G(θw)` therefore does NOT follow from
`Fintype.sum_bijective`.  See §8.11.24 for the corrected reindexing analysis.
-/
set_option maxHeartbeats 1000000 in
/-- The reindexing `θ = thetaReindex` is idempotent: `θ(θw) = θw`.
This holds because `θ` is a projection: it replaces `w|_{neg}` with a function
of `w|_{pos}` (via `reflectInterfaceLink` and `dual`), and leaves
`w|_{pos ∪ int}` unchanged.  Applying `θ` again gives the same result.
0 sorries, 0 custom axioms. -/
lemma thetaReindex_idempotent (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dual : ι → ι) (w : InterfaceLink T L → ι) :
    thetaReindex T L hT ι dual (thetaReindex T L hT ι dual w) =
    thetaReindex T L hT ι dual w := by
  funext l
  by_cases hpos : l ∈ interfaceLinkPos T L
  · rw [thetaReindex_pos T L hT ι dual (thetaReindex T L hT ι dual w) hpos,
        thetaReindex_pos T L hT ι dual w hpos]
  · by_cases hint : l ∈ interfaceLinkInt T L
    · rw [thetaReindex_int T L hT ι dual (thetaReindex T L hT ι dual w) hint,
          thetaReindex_int T L hT ι dual w hint]
    · -- l ∈ neg (from partition: pos ∪ int ∪ neg = univ)
      have hneg : l ∈ interfaceLinkNeg T L := by
        have hcover := (interfaceLinkPartition_disjoint_cover T L).2.2
        have hl : l ∈ interfaceLinkPos T L ∪ interfaceLinkInt T L ∪ interfaceLinkNeg T L := by
          rw [hcover]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp hl with h | hneg
        · rcases Finset.mem_union.mp h with hpos' | hint'
          · exact absurd hpos' hpos
          · exact absurd hint' hint
        · exact hneg
      by_cases hμ : l.val.2 = 0
      · -- time-like: θw(l) = w(φ l), φ l ∈ pos, θ(θw)(l) = θw(φ l) = w(φ l) = θw(l)
        have hφpos : reflectInterfaceLink T L hT l ∈ interfaceLinkPos T L :=
          reflectInterfaceLink_mem_pos_of_neg T L hT hneg
        rw [thetaReindex_neg_time T L hT ι dual (thetaReindex T L hT ι dual w) hneg hμ,
            thetaReindex_pos T L hT ι dual w hφpos,
            thetaReindex_neg_time T L hT ι dual w hneg hμ]
      · -- spatial: θw(l) = dual(w(φ l)), φ l ∈ pos, θ(θw)(l) = dual(θw(φ l)) = dual(w(φ l)) = θw(l)
        have hφpos : reflectInterfaceLink T L hT l ∈ interfaceLinkPos T L :=
          reflectInterfaceLink_mem_pos_of_neg T L hT hneg
        rw [thetaReindex_neg_spatial T L hT ι dual (thetaReindex T L hT ι dual w) hneg hμ,
            thetaReindex_pos T L hT ι dual w hφpos,
            thetaReindex_neg_spatial T L hT ι dual w hneg hμ]
#print axioms thetaReindex_idempotent

/-- The positive-link character factor is invariant under the reindexing `θ`:
`charFactorPos(θw, U⁺) = charFactorPos(w, U⁺)`, since `θw|_{pos} = w|_{pos}`.
0 sorries, 0 custom axioms. -/
lemma charFactorPos_thetaReindex_eq (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    charFactorPos N T L ι dims ρ (thetaReindex T L hT ι dual w) U_plus =
    charFactorPos N T L ι dims ρ w U_plus := by
  simp only [charFactorPos]
  refine Finset.prod_congr rfl (fun l hl => ?_)
  split_ifs with h
  · rw [thetaReindex_pos T L hT ι dual w hl]
  · rfl

#print axioms charFactorPos_thetaReindex_eq

/-- The interface-link character factor is invariant under the reindexing `θ`:
`charFactorInt(θw, u⁰) = charFactorInt(w, u⁰)`, since `θw|_{int} = w|_{int}`.
0 sorries, 0 custom axioms. -/
lemma charFactorInt_thetaReindex_eq (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    charFactorInt N T L ι dims ρ (thetaReindex T L hT ι dual w) U_zero =
    charFactorInt N T L ι dims ρ w U_zero := by
  simp only [charFactorInt]
  refine Finset.prod_congr rfl (fun l hl => ?_)
  split_ifs with h
  · rw [thetaReindex_int T L hT ι dual w hl]
  · rfl

#print axioms charFactorInt_thetaReindex_eq

/-- The positive Fourier coefficient is invariant under the reindexing `θ`:
`fourierCoeffPos(θw, u⁰) = fourierCoeffPos(w, u⁰)`, since `charFactorPos` is
`θ`-invariant (the integrand is pointwise equal).  0 sorries, 0 custom axioms. -/
lemma fourierCoeffPos_thetaReindex_eq (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] (hT : Odd T)
    (ψ : PosInterfaceConfig N T L → ℝ)
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (u0 : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    fourierCoeffPos N T L β ψ ι dims ρ (thetaReindex T L hT ι dual w) u0 =
    fourierCoeffPos N T L β ψ ι dims ρ w u0 := by
  simp only [fourierCoeffPos]
  refine integral_congr_ae (ae_of_all (haarMeasurePositive N T L) ?_)
  intro V
  dsimp only
  rw [charFactorPos_thetaReindex_eq N T L hT ι dims ρ dual w V]

  #print axioms fourierCoeffPos_thetaReindex_eq


