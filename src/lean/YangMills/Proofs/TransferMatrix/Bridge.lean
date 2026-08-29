/-
# Transfer Matrix: Bridge Lemmas and Character Factors
-/

import YangMills.Proofs.TransferMatrix.Step5
import YangMills.Proofs.PositiveDefiniteIntegral.CascadeNonneg
import YangMills.Proofs.PeterWeyl.Separable

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
/-! ### Bridge lemmas: `interfaceLinkVar` ↔ `extendToFullConfig`

These lemmas connect the LINK-based `interfaceLinkVar` (used by the character
expansion in `ReflectionPositivity.lean`) with the SITE-based `extendToFullConfig`
(used by the transfer matrix in `TransferMatrix.lean`).  They show that evaluating
`interfaceLinkVar` on `extendToFullConfig(U_minus, mergePosInterface(U_plus, U_zero))`
recovers `U_plus` / `U_zero` / `U_minus` according to whether the link's base site is
positive / interface / negative.  This is step 2 of sub-step (iii) of Lemma 2
(`transfer_matrix_integral_reduction`): the "trivial integration" / variable
identification step.  All 0 sorries, 0 custom axioms. -/

lemma interfaceLinkVar_extendToFullConfig_pos (N T L : ℕ) [NeZero T] [NeZero L]
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (l : InterfaceLink T L) (hpos : l.val.1 ∈ positiveSites T L) :
    interfaceLinkVar N T L (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)) l =
      U_plus ⟨(l.val.1, l.val.2), hpos⟩ := by
  have h1 : interfaceLinkVar N T L
      (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)) l =
      restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L)
        (Finset.univ : Finset (PeriodicSite T L))
        (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)))
        ⟨(l.val.1, l.val.2), Finset.mem_union_left (interfaceSites T L) hpos⟩ := by
    simp only [interfaceLinkVar, restrictPosInterface, restrictLinkVariable]
  rw [h1, restrictPosInterface_extendToFullConfig]
  simp only [mergePosInterface, dif_pos hpos]

#print axioms interfaceLinkVar_extendToFullConfig_pos

lemma interfaceLinkVar_extendToFullConfig_int (N T L : ℕ) [NeZero T] [NeZero L]
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (l : InterfaceLink T L) (hint : l.val.1 ∈ interfaceSites T L) :
    interfaceLinkVar N T L (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)) l =
      U_zero ⟨(l.val.1, l.val.2), hint⟩ := by
  have hnpos : l.val.1 ∉ positiveSites T L := by
    intro h
    have hdisj : Disjoint (positiveSites T L) (interfaceSites T L) := by
      unfold positiveSites interfaceSites
      rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
    exact Finset.disjoint_left.mp hdisj h hint
  have h1 : interfaceLinkVar N T L
      (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)) l =
      restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L)
        (Finset.univ : Finset (PeriodicSite T L))
        (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)))
        ⟨(l.val.1, l.val.2), Finset.mem_union_right (positiveSites T L) hint⟩ := by
    simp only [interfaceLinkVar, restrictPosInterface, restrictLinkVariable]
  rw [h1, restrictPosInterface_extendToFullConfig]
  simp only [mergePosInterface, dif_neg hnpos]

#print axioms interfaceLinkVar_extendToFullConfig_int

lemma interfaceLinkVar_extendToFullConfig_neg (N T L : ℕ) [NeZero T] [NeZero L]
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (l : InterfaceLink T L) (hneg : l.val.1 ∈ negativeSites T L) :
    interfaceLinkVar N T L (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)) l =
      U_minus ⟨(l.val.1, l.val.2), hneg⟩ := by
  have h1 : interfaceLinkVar N T L
      (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero)) l =
      restrictLinkVariable N (PeriodicSite T L) (negativeSites T L)
        (extendToFullConfig N T L U_minus (mergePosInterface N T L U_plus U_zero))
        ⟨(l.val.1, l.val.2), hneg⟩ := by
    simp only [interfaceLinkVar, restrictLinkVariable]
  rw [h1, restrictLinkVariable_negative_extendToFullConfig]

#print axioms interfaceLinkVar_extendToFullConfig_neg

/-- Specialized bridge lemma (positive links): for `U = extendToFullConfig(reflectPosToNeg V⁺) u`,
the interface link variable at a positive link `l` equals `u` at the corresponding positive-site
index (i.e. `restrictToPositive u` at `l`). This depends only on `u`'s positive part.
Uses the decomposition `u = mergePosInterface (restrictToPositive u) (restrictToInterface u)`
+ `interfaceLinkVar_extendToFullConfig_pos`. 0 sorries, 0 custom axioms. -/
lemma interfaceLinkVar_extendToFullConfig_pos' (N T L : ℕ) [NeZero T] [NeZero L]
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) (l : InterfaceLink T L) (hpos : l.val.1 ∈ positiveSites T L) :
    interfaceLinkVar N T L (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l =
      u ⟨(l.val.1, l.val.2), Finset.mem_union_left (interfaceSites T L) hpos⟩ := by
  have hdecomp := mergePosInterface_restrictToPositive_restrictToInterface N T L u
  have h := interfaceLinkVar_extendToFullConfig_pos N T L (reflectPosToNeg N T L V_plus)
    (restrictToPositive N T L u) (restrictToInterface N T L u) l hpos
  rw [hdecomp] at h
  rw [h]
  rfl

#print axioms interfaceLinkVar_extendToFullConfig_pos'

/-- Specialized bridge lemma (interface links): for `U = extendToFullConfig(reflectPosToNeg V⁺) u`,
the interface link variable at an interface link `l` equals `u` at the corresponding interface-site
index (i.e. `restrictToInterface u` at `l`). This depends only on `u`'s interface part.
0 sorries, 0 custom axioms. -/
lemma interfaceLinkVar_extendToFullConfig_int' (N T L : ℕ) [NeZero T] [NeZero L]
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) (l : InterfaceLink T L) (hint : l.val.1 ∈ interfaceSites T L) :
    interfaceLinkVar N T L (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l =
      u ⟨(l.val.1, l.val.2), Finset.mem_union_right (positiveSites T L) hint⟩ := by
  have hdecomp := mergePosInterface_restrictToPositive_restrictToInterface N T L u
  have h := interfaceLinkVar_extendToFullConfig_int N T L (reflectPosToNeg N T L V_plus)
    (restrictToPositive N T L u) (restrictToInterface N T L u) l hint
  rw [hdecomp] at h
  rw [h]
  rfl

#print axioms interfaceLinkVar_extendToFullConfig_int'

/-- Specialized bridge lemma (negative links): for `U = extendToFullConfig(reflectPosToNeg V⁺) u`,
the interface link variable at a negative link `l` equals `reflectPosToNeg V⁺` at the corresponding
negative-site index. This depends only on `V⁺` (not on `u`). 0 sorries, 0 custom axioms. -/
lemma interfaceLinkVar_extendToFullConfig_neg' (N T L : ℕ) [NeZero T] [NeZero L]
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) (l : InterfaceLink T L) (hneg : l.val.1 ∈ negativeSites T L) :
    interfaceLinkVar N T L (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l =
      reflectPosToNeg N T L V_plus ⟨(l.val.1, l.val.2), hneg⟩ := by
  have hdecomp := mergePosInterface_restrictToPositive_restrictToInterface N T L u
  have h := interfaceLinkVar_extendToFullConfig_neg N T L (reflectPosToNeg N T L V_plus)
    (restrictToPositive N T L u) (restrictToInterface N T L u) l hneg
  rw [hdecomp] at h
  rw [h]

#print axioms interfaceLinkVar_extendToFullConfig_neg'
#print axioms interfaceLinkVar_extendToFullConfig_neg'

/-! ### Crossing plaquette word evaluation (B.2e.3 step (i), §8.11.99)

The crossing plaquette based at a site `n` with `signedTime = -1` in directions `(0, ν)`
(`ν ≠ 0`) has two temporal links (one negative, one interface) and two spatial links
(one interface, one negative).  In the merged configuration
`extendToFullConfig (reflectPosToNeg V⁺) u` its plaquette word evaluates to

  `(V⁺_{θn,0})⁻¹ · u_{n+e₀,ν} · (u_{n+e₀+e_ν,0})⁻¹ · (V⁺_{θ(n+e_ν),ν})⁻¹`.

This is the per-plaquette word evaluation lemma of §8.11.99 step (i). -/

/-- Pointwise evaluation of `extendToFullConfig` on a negative-site link. -/
lemma extendToFullConfig_apply_neg (N T L : ℕ) [NeZero T] [NeZero L]
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (μ : Fin 4) (hneg : n ∈ negativeSites T L) :
    (extendToFullConfig N T L U_minus u).value n μ = U_minus ⟨(n, μ), hneg⟩ := by
  have hnpos : n ∉ positiveSites T L := by
    have hdisj : Disjoint (positiveSites T L) (negativeSites T L) := by
      unfold positiveSites negativeSites
      rw [Finset.disjoint_filter]; intro m hm hpos hneg'; linarith
    exact fun h => Finset.disjoint_left.mp hdisj h hneg
  simp only [extendToFullConfig, extendLinkVariable, mergeConfigurations,
    dif_pos (Finset.mem_univ n), dif_neg hnpos, dif_pos hneg]

/-- Pointwise evaluation of `extendToFullConfig` on an interface-site link. -/
lemma extendToFullConfig_apply_int (N T L : ℕ) [NeZero T] [NeZero L]
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (μ : Fin 4) (hint : n ∈ interfaceSites T L) :
    (extendToFullConfig N T L U_minus u).value n μ =
      u ⟨(n, μ), Finset.mem_union_right (positiveSites T L) hint⟩ := by
  have hnpos : n ∉ positiveSites T L := by
    have hdisj : Disjoint (positiveSites T L) (interfaceSites T L) := by
      unfold positiveSites interfaceSites
      rw [Finset.disjoint_filter]; intro m hm hpos hzero; linarith
    exact fun h => Finset.disjoint_left.mp hdisj h hint
  have hnneg : n ∉ negativeSites T L := by
    have hdisj : Disjoint (negativeSites T L) (interfaceSites T L) := by
      unfold negativeSites interfaceSites
      rw [Finset.disjoint_filter]; intro m hm hneg hzero; linarith
    exact fun h => Finset.disjoint_left.mp hdisj h hint
  simp only [extendToFullConfig, extendLinkVariable, mergeConfigurations,
    dif_pos (Finset.mem_univ n), dif_neg hnpos, dif_neg hnneg]

/-- If `t` has signed time `-1`, then `t + 1` has signed time `0`. -/
lemma signedTime_succ_of_eq_neg_one (T : ℕ) [NeZero T] (t : ZMod T)
    (h : signedTime T t = -1) : signedTime T (t + 1) = 0 := by
  have hval : t.val = T - 1 := by
    have hlt := ZMod.val_lt t
    by_cases hle : t.val ≤ (T - 1) / 2
    · have hpos : signedTime T t = (t.val : ℤ) := dif_pos hle
      rw [hpos] at h; omega
    · have hneg : signedTime T t = (t.val : ℤ) - (T : ℤ) := dif_neg hle
      rw [hneg] at h; omega
  have ht1 : t + 1 = (0 : ZMod T) := by
    have ht : t = ((T - 1 : ℕ) : ZMod T) := by
      apply ZMod.val_injective T
      rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.sub_lt (NeZero.pos T) Nat.one_pos)]
    rw [ht]
    have hcast : ((T - 1 : ℕ) : ZMod T) = ((T : ℕ) : ZMod T) - 1 := by
      rw [Nat.cast_sub (NeZero.pos T), Nat.cast_one]
    rw [hcast, sub_add_cancel, ZMod.natCast_self]
  rw [ht1]; simp [signedTime, ZMod.val_zero]

/-- The time coordinate of `n + e₀`. -/
lemma addVector_zero_time (T L : ℕ) (n : PeriodicSite T L) :
    (AddVector.addVector n (0 : Fin 4) : PeriodicSite T L).time = n.time + 1 := by
  show (addVectorPeriodic T L n 0).time = n.time + 1
  simp [addVectorPeriodic]

/-- The time coordinate of `n + e_ν` for spatial `ν`. -/
lemma addVector_spatial_time (T L : ℕ) (n : PeriodicSite T L) (ν : Fin 4) (hν : ν ≠ 0) :
    (AddVector.addVector n ν : PeriodicSite T L).time = n.time :=
  addVectorPeriodic_time_of_ne_zero T L n ν hν

lemma signedTime_addVector_zero_of_eq_neg_one (T L : ℕ) [NeZero T]
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) :
    signedTime T (AddVector.addVector n (0 : Fin 4) : PeriodicSite T L).time = 0 := by
  rw [addVector_zero_time]; exact signedTime_succ_of_eq_neg_one T n.time hn

lemma signedTime_addVector_zero_spatial_of_eq_neg_one (T L : ℕ) [NeZero T]
    (n : PeriodicSite T L) (ν : Fin 4) (hν : ν ≠ 0) (hn : signedTime T n.time = -1) :
    signedTime T (AddVector.addVector (AddVector.addVector n (0 : Fin 4)) ν :
      PeriodicSite T L).time = 0 := by
  rw [addVector_spatial_time T L _ ν hν]
  exact signedTime_addVector_zero_of_eq_neg_one T L n hn

lemma signedTime_addVector_spatial (T L : ℕ) (n : PeriodicSite T L) (ν : Fin 4)
    (hν : ν ≠ 0) :
    signedTime T (AddVector.addVector n ν : PeriodicSite T L).time =
      signedTime T n.time := by
  rw [addVector_spatial_time T L n ν hν]

lemma mem_negativeSites_of_signedTime_eq_neg_one {T L : ℕ} [NeZero T] [NeZero L]
    {n : PeriodicSite T L} (h : signedTime T n.time = -1) : n ∈ negativeSites T L := by
  simp only [negativeSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h]; norm_num

lemma mem_interfaceSites_of_signedTime_eq_zero {T L : ℕ} [NeZero T] [NeZero L]
    {n : PeriodicSite T L} (h : signedTime T n.time = 0) : n ∈ interfaceSites T L := by
  simp only [interfaceSites, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

/-- **Crossing plaquette word evaluation** (§8.11.99 step (i)).  For a crossing plaquette
based at `n` with `signedTime n = -1` in directions `(0, ν)` (`ν ≠ 0`), the plaquette
product in the merged configuration `extendToFullConfig (reflectPosToNeg V⁺) u` is

  `(V⁺_{θn,0})⁻¹ · u_{n+e₀,ν} · (u_{n+e₀+e_ν,0})⁻¹ · (V⁺_{θ(n+e_ν),ν})⁻¹`. -/
lemma plaquetteProduct_extendToFullConfig_crossing (N T L : ℕ) [NeZero T] [NeZero L]
    (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) n 0 ν =
      (V_plus ⟨(ReflectSite.reflectSite n, 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩)⁻¹ *
      u ⟨(AddVector.addVector n 0, ν),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩ *
      (u ⟨(AddVector.addVector (AddVector.addVector n 0) ν, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_spatial_of_eq_neg_one T L n ν hν hn))⟩)⁻¹ *
      (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ := by
  have h1 : n ∈ negativeSites T L := mem_negativeSites_of_signedTime_eq_neg_one hn
  have h2 : AddVector.addVector n (0 : Fin 4) ∈ interfaceSites T L :=
    mem_interfaceSites_of_signedTime_eq_zero (signedTime_addVector_zero_of_eq_neg_one T L n hn)
  have h3 : AddVector.addVector (AddVector.addVector n (0 : Fin 4)) ν ∈ interfaceSites T L :=
    mem_interfaceSites_of_signedTime_eq_zero
      (signedTime_addVector_zero_spatial_of_eq_neg_one T L n ν hν hn)
  have h4 : AddVector.addVector n ν ∈ negativeSites T L :=
    mem_negativeSites_of_signedTime_eq_neg_one
      (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)
  unfold plaquetteProduct
  rw [extendToFullConfig_apply_neg N T L _ u n 0 h1,
    extendToFullConfig_apply_int N T L _ u _ ν h2,
    extendToFullConfig_apply_int N T L _ u _ 0 h3,
    extendToFullConfig_apply_neg N T L _ u _ ν h4,
    reflectPosToNeg_apply N T L hT V_plus h1 0,
    reflectPosToNeg_apply N T L hT V_plus h4 ν]
  simp only [if_neg hν, if_true]

#print axioms plaquetteProduct_extendToFullConfig_crossing

/-- **Per-plaquette matrix-element factorization** (B.2e.3 step (ii′), §8.11.100).
Combining the crossing plaquette word evaluation
(`plaquetteProduct_extendToFullConfig_crossing`) with the group-level factorization
(`repCharacter_crossing_word_eq_sum_matrixElement_conj`): the character of a crossing
plaquette word in the merged configuration is the matrix-element pairing

  `χ_R(word) = ∑_{k,l} (ρ (W_int u))_{kl} · conj((ρ (W_pos V⁺))_{kl})`

with `W_int(x) = x_{n+e₀,ν}·(x_{n+e₀+e_ν,0})⁻¹` (interface links) and
`W_pos(x) = x_{θn,0}·x_{θ(n+e_ν),ν}` (positive links).  0 sorries, 0 new axioms. -/
lemma repCharacter_plaquetteProduct_extendToFullConfig_crossing
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {dim : ℕ} (ρ : SU N →* Matrix (Fin dim) (Fin dim) ℂ)
    (hU : IsUnitaryRepresentation ρ)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    repCharacter ρ
        (plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)
          n 0 ν) =
      ∑ k : Fin dim, ∑ l : Fin dim,
        (ρ (u ⟨(AddVector.addVector n 0, ν),
                Finset.mem_union_right (positiveSites T L)
                  (mem_interfaceSites_of_signedTime_eq_zero
                    (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩ *
            (u ⟨(AddVector.addVector (AddVector.addVector n 0) ν, 0),
                Finset.mem_union_right (positiveSites T L)
                  (mem_interfaceSites_of_signedTime_eq_zero
                    (signedTime_addVector_zero_spatial_of_eq_neg_one T L n ν hν hn))⟩)⁻¹)) k l *
        conj ((ρ (V_plus ⟨(ReflectSite.reflectSite n, 0),
                  reflectSite_mem_positive_of_negative hT
                    (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ *
                V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), ν),
                  reflectSite_mem_positive_of_negative hT
                    (mem_negativeSites_of_signedTime_eq_neg_one
                      (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)) k l) := by
  rw [plaquetteProduct_extendToFullConfig_crossing N T L hT V_plus u n hn ν hν]
  exact repCharacter_crossing_word_eq_sum_matrixElement_conj ρ hU _ _ _ _

#print axioms repCharacter_plaquetteProduct_extendToFullConfig_crossing

/-- The interface half-word of a crossing plaquette based at `n` (signedTime `-1`),
directions `(0, ν)`: `W_int(x) = x_{n+e₀,ν}·(x_{n+e₀+e_ν,0})⁻¹`. -/
noncomputable def crossingWordInt (N T L : ℕ) [NeZero T] [NeZero L]
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) (ν : Fin 4) (hν : ν ≠ 0)
    (u : PosInterfaceConfig N T L) : SU N :=
  u ⟨(AddVector.addVector n 0, ν),
      Finset.mem_union_right (positiveSites T L)
        (mem_interfaceSites_of_signedTime_eq_zero
          (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩ *
    (u ⟨(AddVector.addVector (AddVector.addVector n 0) ν, 0),
        Finset.mem_union_right (positiveSites T L)
          (mem_interfaceSites_of_signedTime_eq_zero
            (signedTime_addVector_zero_spatial_of_eq_neg_one T L n ν hν hn))⟩)⁻¹

/-- The positive half-word of a crossing plaquette based at `n` (signedTime `-1`),
directions `(0, ν)`: `W_pos(x) = x_{θn,0}·x_{θ(n+e_ν),ν}`. -/
noncomputable def crossingWordPos (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) (ν : Fin 4) (hν : ν ≠ 0)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) : SU N :=
  V_plus ⟨(ReflectSite.reflectSite n, 0),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ *
    V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), ν),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_eq_neg_one
          (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩

/-- Restatement of `repCharacter_plaquetteProduct_extendToFullConfig_crossing` in terms of
the named half-words `crossingWordInt` / `crossingWordPos`. -/
lemma repCharacter_plaquetteProduct_crossing_eq_halfWords
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {dim : ℕ} (ρ : SU N →* Matrix (Fin dim) (Fin dim) ℂ)
    (hU : IsUnitaryRepresentation ρ)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    repCharacter ρ
        (plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)
          n 0 ν) =
      ∑ k : Fin dim, ∑ l : Fin dim,
        (ρ (crossingWordInt N T L n hn ν hν u)) k l *
        conj ((ρ (crossingWordPos N T L hT n hn ν hν V_plus)) k l) :=
  repCharacter_plaquetteProduct_extendToFullConfig_crossing N T L hT ρ hU V_plus u n hn ν hν

/-- **Reversed-crossing plaquette word evaluation** (rest-product family (a),
§8.11.102).  For a plaquette based at `n` with `signedTime n = -1` in directions
`(ν, 0)` (`ν ≠ 0` spatial — the REVERSED orientation of a crossing plaquette), the
plaquette product in the merged configuration
`extendToFullConfig (reflectPosToNeg V⁺) u` is

  `V⁺_{θn,ν} · (V⁺_{θ(n+e_ν),0})⁻¹ · (u_{n+e_ν+e₀,ν})⁻¹ · (u_{n+e₀,0})⁻¹`.

(Links: `(n,ν)` negative spatial — unchanged by reflection; `(n+e_ν,0)` negative
temporal — inverted; `(n+e_ν+e₀,ν)`, `(n+e₀,0)` interface — from `u`.) -/
lemma plaquetteProduct_extendToFullConfig_crossing_reversed (N T L : ℕ) [NeZero T]
    [NeZero L] (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) n ν 0 =
      V_plus ⟨(ReflectSite.reflectSite n, ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ *
      (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ *
      (u ⟨(AddVector.addVector (AddVector.addVector n ν) 0, ν),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L _
                (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)))⟩)⁻¹ *
      (u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹ := by
  have h1 : n ∈ negativeSites T L := mem_negativeSites_of_signedTime_eq_neg_one hn
  have h2 : AddVector.addVector n ν ∈ negativeSites T L :=
    mem_negativeSites_of_signedTime_eq_neg_one
      (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)
  have h3 : AddVector.addVector (AddVector.addVector n ν) (0 : Fin 4) ∈ interfaceSites T L :=
    mem_interfaceSites_of_signedTime_eq_zero
      (signedTime_addVector_zero_of_eq_neg_one T L _
        (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))
  have h4 : AddVector.addVector n (0 : Fin 4) ∈ interfaceSites T L :=
    mem_interfaceSites_of_signedTime_eq_zero (signedTime_addVector_zero_of_eq_neg_one T L n hn)
  unfold plaquetteProduct
  rw [extendToFullConfig_apply_neg N T L _ u n ν h1,
    extendToFullConfig_apply_neg N T L _ u _ 0 h2,
    extendToFullConfig_apply_int N T L _ u _ ν h3,
    extendToFullConfig_apply_int N T L _ u _ 0 h4,
    reflectPosToNeg_apply N T L hT V_plus h1 ν,
    reflectPosToNeg_apply N T L hT V_plus h2 0]
  simp only [if_neg hν, if_true]

#print axioms plaquetteProduct_extendToFullConfig_crossing_reversed

/-- The interface half-word of a reversed-crossing plaquette based at `n`
(signedTime `-1`), directions `(ν, 0)`:
`W_int^rev(x) = (x_{n+e_ν+e₀,ν})⁻¹ · (x_{n+e₀,0})⁻¹`. -/
noncomputable def crossingRevWordInt (N T L : ℕ) [NeZero T] [NeZero L]
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) (ν : Fin 4) (hν : ν ≠ 0)
    (u : PosInterfaceConfig N T L) : SU N :=
  (u ⟨(AddVector.addVector (AddVector.addVector n ν) 0, ν),
      Finset.mem_union_right (positiveSites T L)
        (mem_interfaceSites_of_signedTime_eq_zero
          (signedTime_addVector_zero_of_eq_neg_one T L _
            (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)))⟩)⁻¹ *
  (u ⟨(AddVector.addVector n 0, 0),
      Finset.mem_union_right (positiveSites T L)
        (mem_interfaceSites_of_signedTime_eq_zero
          (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹

/-- The positive half-word of a reversed-crossing plaquette based at `n`
(signedTime `-1`), directions `(ν, 0)`:
`W_pos^rev(x) = x_{θ(n+e_ν),0} · (x_{θn,ν})⁻¹`. -/
noncomputable def crossingRevWordPos (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) (ν : Fin 4) (hν : ν ≠ 0)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) : SU N :=
  V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), 0),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_eq_neg_one
          (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩ *
  (V_plus ⟨(ReflectSite.reflectSite n, ν),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩)⁻¹

/-- **Reversed-crossing matrix-element factorization** (rest-product family (a),
§8.11.102).  The character of the reversed-crossing word
`V₁·V₂⁻¹·u₁⁻¹·u₂⁻¹` factors as the matrix-element pairing of the half-words
`W_int^rev = u₁⁻¹·u₂⁻¹` and `W_pos^rev = V₂·V₁⁻¹`:

  `χ(word) = ∑_{k,l} (ρ (W_int^rev u))_{kl} · conj((ρ (W_pos^rev V⁺))_{kl})`.

Proof: rotate the word cyclically to `V₂⁻¹·u₁⁻¹·u₂⁻¹·V₁` (`repCharacter_cyclic`),
which is the `a⁻¹·b·c⁻¹·d⁻¹` pattern of
`repCharacter_crossing_word_eq_sum_matrixElement_conj` with `a = V₂`, `b = u₁⁻¹`,
`c = u₂`, `d = V₁⁻¹`.  0 sorries, 0 new axioms. -/
lemma repCharacter_plaquetteProduct_crossing_reversed_eq_halfWords
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {dim : ℕ} (ρ : SU N →* Matrix (Fin dim) (Fin dim) ℂ)
    (hU : IsUnitaryRepresentation ρ)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    repCharacter ρ
        (plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)
          n ν 0) =
      ∑ k : Fin dim, ∑ l : Fin dim,
        (ρ (crossingRevWordInt N T L n hn ν hν u)) k l *
        conj ((ρ (crossingRevWordPos N T L hT n hn ν hν V_plus)) k l) := by
  rw [plaquetteProduct_extendToFullConfig_crossing_reversed N T L hT V_plus u n hn ν hν]
  rw [show V_plus ⟨(ReflectSite.reflectSite n, ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ *
        (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ *
        (u ⟨(AddVector.addVector (AddVector.addVector n ν) 0, ν),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L _
                (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)))⟩)⁻¹ *
        (u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹ =
      V_plus ⟨(ReflectSite.reflectSite n, ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ *
        (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ *
        ((u ⟨(AddVector.addVector (AddVector.addVector n ν) 0, ν),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L _
                (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)))⟩)⁻¹ *
        (u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹) from by group]
  rw [repCharacter_cyclic ρ _ _ _]
  rw [show (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ *
        ((u ⟨(AddVector.addVector (AddVector.addVector n ν) 0, ν),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L _
                (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)))⟩)⁻¹ *
        (u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹) *
        V_plus ⟨(ReflectSite.reflectSite n, ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ =
      (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n ν), 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ *
        (u ⟨(AddVector.addVector (AddVector.addVector n ν) 0, ν),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L _
                (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)))⟩)⁻¹ *
        (u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹ *
        (V_plus ⟨(ReflectSite.reflectSite n, ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩)⁻¹⁻¹ from by group]
  exact repCharacter_crossing_word_eq_sum_matrixElement_conj ρ hU _ _ _ _

#print axioms repCharacter_plaquetteProduct_crossing_reversed_eq_halfWords

/-- If `t` has signed time `-1`, then `t + 2` has signed time `1` (needs `T ≥ 3`,
which follows from `Odd T` plus the impossibility of `signedTime = -1` for `T = 1`). -/
lemma signedTime_add_two_of_eq_neg_one (T : ℕ) [NeZero T] (hT : Odd T) (t : ZMod T)
    (h : signedTime T t = -1) : signedTime T (t + 2) = 1 := by
  have hval : t.val = T - 1 := by
    have hlt := ZMod.val_lt t
    by_cases hle : t.val ≤ (T - 1) / 2
    · have hpos : signedTime T t = (t.val : ℤ) := dif_pos hle
      rw [hpos] at h; omega
    · have hneg : signedTime T t = (t.val : ℤ) - (T : ℤ) := dif_neg hle
      rw [hneg] at h; omega
  have hT3 : 3 ≤ T := by
    rcases hT with ⟨k, hk⟩
    by_contra hcon
    push_neg at hcon
    have hT1 : T = 1 := by omega
    have hv0 : t.val = 0 := by
      have h2 := ZMod.val_lt t
      omega
    have hle : t.val ≤ (T - 1) / 2 := by omega
    have hst : signedTime T t = (t.val : ℤ) := dif_pos hle
    rw [hst, hv0] at h
    norm_num at h
  have ht2 : t + 2 = (1 : ZMod T) := by
    have ht : t = ((T - 1 : ℕ) : ZMod T) := by
      apply ZMod.val_injective T
      rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.sub_lt (NeZero.pos T) Nat.one_pos)]
    rw [ht]
    have hcast : ((T - 1 : ℕ) : ZMod T) = ((T : ℕ) : ZMod T) - 1 := by
      rw [Nat.cast_sub (NeZero.pos T), Nat.cast_one]
    rw [hcast, ZMod.natCast_self, zero_sub]
    ring
  rw [ht2]
  haveI : Fact (1 < T) := ⟨by omega⟩
  have h1val : (1 : ZMod T).val = 1 := ZMod.val_one T
  have hle1 : (1 : ZMod T).val ≤ (T - 1) / 2 := by rw [h1val]; omega
  have hst1 : signedTime T (1 : ZMod T) = ((1 : ZMod T).val : ℤ) := dif_pos hle1
  rw [hst1, h1val]
  norm_num

#print axioms signedTime_add_two_of_eq_neg_one

/-- The time coordinate of `n + 2e₀` has signed time `1` when `n` has signed time `-1`. -/
lemma signedTime_addVector_zero_twice_of_eq_neg_one (T L : ℕ) [NeZero T] (hT : Odd T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) :
    signedTime T (AddVector.addVector (AddVector.addVector n (0 : Fin 4)) (0 : Fin 4) :
      PeriodicSite T L).time = 1 := by
  rw [addVector_zero_time, addVector_zero_time,
    show n.time + 1 + 1 = n.time + 2 from by ring]
  exact signedTime_add_two_of_eq_neg_one T hT n.time hn

#print axioms signedTime_addVector_zero_twice_of_eq_neg_one

/-- A site with signed time `1` is a positive site. -/
lemma mem_positiveSites_of_signedTime_eq_one {T L : ℕ} [NeZero T] [NeZero L]
    {n : PeriodicSite T L} (h : signedTime T n.time = 1) : n ∈ positiveSites T L := by
  simp only [positiveSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h]; norm_num

#print axioms mem_positiveSites_of_signedTime_eq_one

/-- Pointwise evaluation of `extendToFullConfig` on a positive-site link. -/
lemma extendToFullConfig_apply_pos (N T L : ℕ) [NeZero T] [NeZero L]
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (μ : Fin 4) (hpos : n ∈ positiveSites T L) :
    (extendToFullConfig N T L U_minus u).value n μ =
      u ⟨(n, μ), Finset.mem_union_left (interfaceSites T L) hpos⟩ := by
  simp only [extendToFullConfig, extendLinkVariable, mergeConfigurations,
    dif_pos (Finset.mem_univ n), dif_pos hpos]

#print axioms extendToFullConfig_apply_pos

/-- **Degenerate temporal plaquette word evaluation** (rest-product family (b),
§8.11.102).  For a degenerate plaquette based at `n` with `signedTime n = -1` in
directions `(0, 0)`, the plaquette product in the merged configuration
`extendToFullConfig (reflectPosToNeg V⁺) u` is

  `(V⁺_{θn,0})⁻¹ · u_{n+e₀,0} · (u_{n+2e₀,0})⁻¹ · (u_{n+e₀,0})⁻¹`.

(Links: `(n,0)` negative temporal — inverted by reflection; `(n+e₀,0)` interface;
`(n+2e₀,0)` positive — from `u`'s positive part; `(n+e₀,0)` interface again.) -/
lemma plaquetteProduct_extendToFullConfig_degenerate (N T L : ℕ) [NeZero T] [NeZero L]
    (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) :
    plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) n 0 0 =
      (V_plus ⟨(ReflectSite.reflectSite n, 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩)⁻¹ *
      u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩ *
      (u ⟨(AddVector.addVector (AddVector.addVector n 0) 0, 0),
          Finset.mem_union_left (interfaceSites T L)
            (mem_positiveSites_of_signedTime_eq_one
              (signedTime_addVector_zero_twice_of_eq_neg_one T L hT n hn))⟩)⁻¹ *
      (u ⟨(AddVector.addVector n 0, 0),
          Finset.mem_union_right (positiveSites T L)
            (mem_interfaceSites_of_signedTime_eq_zero
              (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩)⁻¹ := by
  have h1 : n ∈ negativeSites T L := mem_negativeSites_of_signedTime_eq_neg_one hn
  have h2 : AddVector.addVector n (0 : Fin 4) ∈ interfaceSites T L :=
    mem_interfaceSites_of_signedTime_eq_zero (signedTime_addVector_zero_of_eq_neg_one T L n hn)
  have h3 : AddVector.addVector (AddVector.addVector n (0 : Fin 4)) (0 : Fin 4) ∈
      positiveSites T L :=
    mem_positiveSites_of_signedTime_eq_one
      (signedTime_addVector_zero_twice_of_eq_neg_one T L hT n hn)
  unfold plaquetteProduct
  rw [extendToFullConfig_apply_neg N T L _ u n 0 h1,
    extendToFullConfig_apply_int N T L _ u _ 0 h2,
    extendToFullConfig_apply_pos N T L _ u _ 0 h3,
    reflectPosToNeg_apply N T L hT V_plus h1 0]
  simp only [if_true]

#print axioms plaquetteProduct_extendToFullConfig_degenerate

/-- The bra half-word of a degenerate temporal plaquette `(n,0,0)` (signedTime `-1`):
`W_A(x) = x_{n+e₀,0} · (x_{n+2e₀,0})⁻¹` (interface link times positive-link inverse). -/
noncomputable def degenerateWordA (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (u : PosInterfaceConfig N T L) : SU N :=
  u ⟨(AddVector.addVector n 0, 0),
      Finset.mem_union_right (positiveSites T L)
        (mem_interfaceSites_of_signedTime_eq_zero
          (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩ *
  (u ⟨(AddVector.addVector (AddVector.addVector n 0) 0, 0),
      Finset.mem_union_left (interfaceSites T L)
        (mem_positiveSites_of_signedTime_eq_one
          (signedTime_addVector_zero_twice_of_eq_neg_one T L hT n hn))⟩)⁻¹

/-- The ket/bra half-word of a degenerate temporal plaquette `(n,0,0)`:
`W_B = V⁺_{θn,0} · u_{n+e₀,0}` (reflected ket link times interface link). -/
noncomputable def degenerateWordB (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) : SU N :=
  V_plus ⟨(ReflectSite.reflectSite n, 0),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_eq_neg_one hn)⟩ *
  u ⟨(AddVector.addVector n 0, 0),
      Finset.mem_union_right (positiveSites T L)
        (mem_interfaceSites_of_signedTime_eq_zero
          (signedTime_addVector_zero_of_eq_neg_one T L n hn))⟩

/-- **Degenerate plaquette matrix-element factorization** (rest-product family (b),
§8.11.102).  The character of the degenerate word `(V⁺)⁻¹·u₁·u₂⁻¹·u₁⁻¹` is already in
the `a⁻¹·b·c⁻¹·d⁻¹` pattern of `repCharacter_crossing_word_eq_sum_matrixElement_conj`
(with `a = V⁺_{θn,0}`, `b = u₁`, `c = u₂`, `d = u₁`):

  `χ(word) = ∑_{k,l} (ρ (W_A u))_{kl} · conj((ρ (W_B V⁺ u))_{kl})`.

0 sorries, 0 new axioms. -/
lemma repCharacter_plaquetteProduct_degenerate_eq_halfWords
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {dim : ℕ} (ρ : SU N →* Matrix (Fin dim) (Fin dim) ℂ)
    (hU : IsUnitaryRepresentation ρ)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) :
    repCharacter ρ
        (plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)
          n 0 0) =
      ∑ k : Fin dim, ∑ l : Fin dim,
        (ρ (degenerateWordA N T L hT n hn u)) k l *
        conj ((ρ (degenerateWordB N T L hT n hn V_plus u)) k l) := by
  rw [plaquetteProduct_extendToFullConfig_degenerate N T L hT V_plus u n hn]
  exact repCharacter_crossing_word_eq_sum_matrixElement_conj ρ hU _ _ _ _

#print axioms repCharacter_plaquetteProduct_degenerate_eq_halfWords

/-- If `t` has signed time `(T-1)/2` (the maximum positive time — the far seam of the
periodic lattice), then `t + 1` wraps around to signed time `-((T-1)/2)`.
Requires `T ≥ 3` (for `T = 1` the "seam" coincides with the `t = 0` interface). -/
lemma signedTime_succ_of_eq_max (T : ℕ) [NeZero T] (hT : Odd T) (hT3 : 3 ≤ T) (t : ZMod T)
    (h : signedTime T t = ((T - 1) / 2 : ℕ)) :
    signedTime T (t + 1) = -(((T - 1) / 2 : ℕ) : ℤ) := by
  rcases hT with ⟨k, hk⟩
  have hlt := ZMod.val_lt t
  have hval : t.val = (T - 1) / 2 := by
    by_cases hle : t.val ≤ (T - 1) / 2
    · have hpos : signedTime T t = (t.val : ℤ) := dif_pos hle
      rw [hpos] at h; omega
    · have hneg : signedTime T t = (t.val : ℤ) - (T : ℤ) := dif_neg hle
      rw [hneg] at h; omega
  have ht : t = (((T - 1) / 2 : ℕ) : ZMod T) := by
    apply ZMod.val_injective T
    rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h1 : (((T - 1) / 2 : ℕ) : ZMod T) + 1 = (((T - 1) / 2 + 1 : ℕ) : ZMod T) :=
    (Nat.cast_add_one _).symm
  rw [ht, h1]
  have hval1 : ((((T - 1) / 2 + 1 : ℕ) : ZMod T)).val = (T - 1) / 2 + 1 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hnle : ¬ ((((T - 1) / 2 + 1 : ℕ) : ZMod T)).val ≤ (T - 1) / 2 := by
    rw [hval1]; omega
  have hneg : signedTime T ((((T - 1) / 2 + 1 : ℕ) : ZMod T)) =
      (((((T - 1) / 2 + 1 : ℕ) : ZMod T)).val : ℤ) - (T : ℤ) := dif_neg hnle
  rw [hneg, hval1]
  omega

#print axioms signedTime_succ_of_eq_max

/-- The time coordinate of `n + e₀` when `n` is at the far seam `(T-1)/2`. -/
lemma signedTime_addVector_zero_of_eq_max (T L : ℕ) [NeZero T] (hT : Odd T) (hT3 : 3 ≤ T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = ((T - 1) / 2 : ℕ)) :
    signedTime T (AddVector.addVector n (0 : Fin 4) : PeriodicSite T L).time =
      -(((T - 1) / 2 : ℕ) : ℤ) := by
  rw [addVector_zero_time]
  exact signedTime_succ_of_eq_max T hT hT3 n.time hn

#print axioms signedTime_addVector_zero_of_eq_max

/-- A site at the far seam (signed time `(T-1)/2 > 0`) is a positive site. -/
lemma mem_positiveSites_of_signedTime_eq_max {T L : ℕ} [NeZero T] [NeZero L]
    {n : PeriodicSite T L} (hT3 : 3 ≤ T) (h : signedTime T n.time = ((T - 1) / 2 : ℕ)) :
    n ∈ positiveSites T L := by
  simp only [positiveSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h]; omega

#print axioms mem_positiveSites_of_signedTime_eq_max

/-- A site just past the far seam (signed time `-((T-1)/2) < 0`) is a negative site. -/
lemma mem_negativeSites_of_signedTime_neg_max {T L : ℕ} [NeZero T] [NeZero L]
    {n : PeriodicSite T L} (hT3 : 3 ≤ T)
    (h : signedTime T n.time = -(((T - 1) / 2 : ℕ) : ℤ)) :
    n ∈ negativeSites T L := by
  simp only [negativeSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h]; omega

#print axioms mem_negativeSites_of_signedTime_neg_max

/-- **Wraparound plaquette word evaluation** (rest-product family (c), §8.11.102).
For a plaquette based at `n` at the far seam `signedTime n = (T-1)/2` in directions
`(0, ν)` (`ν ≠ 0`), the plaquette product in the merged configuration
`extendToFullConfig (reflectPosToNeg V⁺) u` is

  `u_{n,0} · V⁺_{θ(n+e₀),ν} · V⁺_{θ(n+e₀+e_ν),0} · (u_{n+e_ν,ν})⁻¹`.

(Links: `(n,0)` positive temporal — from `u`; `(n+e₀,ν)` wrapped to negative spatial —
unchanged by reflection; `(n+e₀+e_ν,0)` negative temporal — inverted by reflection AND
by the plaquette orientation, hence un-inverted; `(n+e_ν,ν)` positive spatial — from
`u`.) -/
lemma plaquetteProduct_extendToFullConfig_wraparound (N T L : ℕ) [NeZero T] [NeZero L]
    (hT : Odd T) (hT3 : 3 ≤ T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = ((T - 1) / 2 : ℕ))
    (ν : Fin 4) (hν : ν ≠ 0) :
    plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) n 0 ν =
      u ⟨(n, 0),
          Finset.mem_union_left (interfaceSites T L)
            (mem_positiveSites_of_signedTime_eq_max hT3 hn)⟩ *
      V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n 0), ν),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_neg_max hT3
              (signedTime_addVector_zero_of_eq_max T L hT hT3 n hn))⟩ *
      (V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n 0) ν), 0),
          reflectSite_mem_positive_of_negative hT
            (mem_negativeSites_of_signedTime_neg_max hT3
              (by rw [signedTime_addVector_spatial T L _ ν hν]
                  exact signedTime_addVector_zero_of_eq_max T L hT hT3 n hn))⟩) *
      (u ⟨(AddVector.addVector n ν, ν),
          Finset.mem_union_left (interfaceSites T L)
            (mem_positiveSites_of_signedTime_eq_max hT3
              (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩)⁻¹ := by
  have h1 : n ∈ positiveSites T L := mem_positiveSites_of_signedTime_eq_max hT3 hn
  have h2 : AddVector.addVector n (0 : Fin 4) ∈ negativeSites T L :=
    mem_negativeSites_of_signedTime_neg_max hT3
      (signedTime_addVector_zero_of_eq_max T L hT hT3 n hn)
  have h3 : AddVector.addVector (AddVector.addVector n (0 : Fin 4)) ν ∈ negativeSites T L :=
    mem_negativeSites_of_signedTime_neg_max hT3
      (by rw [signedTime_addVector_spatial T L _ ν hν]
          exact signedTime_addVector_zero_of_eq_max T L hT hT3 n hn)
  have h4 : AddVector.addVector n ν ∈ positiveSites T L :=
    mem_positiveSites_of_signedTime_eq_max hT3
      (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn)
  unfold plaquetteProduct
  rw [extendToFullConfig_apply_pos N T L _ u n 0 h1,
    extendToFullConfig_apply_neg N T L _ u _ ν h2,
    extendToFullConfig_apply_neg N T L _ u _ 0 h3,
    extendToFullConfig_apply_pos N T L _ u _ ν h4,
    reflectPosToNeg_apply N T L hT V_plus h2 ν,
    reflectPosToNeg_apply N T L hT V_plus h3 0]
  simp only [if_neg hν, if_true, inv_inv]

#print axioms plaquetteProduct_extendToFullConfig_wraparound

/-- The `A` half-word of a wraparound plaquette `(n, 0, ν)` at the far seam:
`W_A = u_{n,0} · V⁺_{θ(n+e₀),ν} · V⁺_{θ(n+e₀+e_ν),0}` (one positive temporal link from
`u`, then the two reflected negative links from `V⁺`). -/
noncomputable def wraparoundWordA (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (hT3 : 3 ≤ T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = ((T - 1) / 2 : ℕ))
    (ν : Fin 4) (hν : ν ≠ 0)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) : SU N :=
  u ⟨(n, 0),
      Finset.mem_union_left (interfaceSites T L)
        (mem_positiveSites_of_signedTime_eq_max hT3 hn)⟩ *
  V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector n 0), ν),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_neg_max hT3
          (signedTime_addVector_zero_of_eq_max T L hT hT3 n hn))⟩ *
  V_plus ⟨(ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n 0) ν), 0),
      reflectSite_mem_positive_of_negative hT
        (mem_negativeSites_of_signedTime_neg_max hT3
          (by rw [signedTime_addVector_spatial T L _ ν hν]
              exact signedTime_addVector_zero_of_eq_max T L hT hT3 n hn))⟩

/-- The `B` half-word of a wraparound plaquette `(n, 0, ν)` at the far seam:
`W_B = u_{n+e_ν,ν}` (the positive spatial link from `u`). -/
noncomputable def wraparoundWordB (N T L : ℕ) [NeZero T] [NeZero L]
    (hT3 : 3 ≤ T)
    (n : PeriodicSite T L) (hn : signedTime T n.time = ((T - 1) / 2 : ℕ))
    (ν : Fin 4) (hν : ν ≠ 0)
    (u : PosInterfaceConfig N T L) : SU N :=
  u ⟨(AddVector.addVector n ν, ν),
      Finset.mem_union_left (interfaceSites T L)
        (mem_positiveSites_of_signedTime_eq_max hT3
          (by rw [signedTime_addVector_spatial T L n ν hν]; exact hn))⟩

/-- **Wraparound plaquette matrix-element factorization** (rest-product family (c),
§8.11.102).  The wraparound word `u₁·V₁·V₂·u₂⁻¹` is already in the `A·B⁻¹` pattern
(with `A = u₁·V₁·V₂`, `B = u₂`), so `repCharacter_mul_inv_eq_sum_matrixElement_conj`
applies directly:

  `χ(word) = ∑_{k,l} (ρ (W_A V⁺ u))_{kl} · conj((ρ (W_B u))_{kl})`.

0 sorries, 0 new axioms. -/
lemma repCharacter_plaquetteProduct_wraparound_eq_halfWords
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (hT3 : 3 ≤ T)
    {dim : ℕ} (ρ : SU N →* Matrix (Fin dim) (Fin dim) ℂ)
    (hU : IsUnitaryRepresentation ρ)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = ((T - 1) / 2 : ℕ))
    (ν : Fin 4) (hν : ν ≠ 0) :
    repCharacter ρ
        (plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)
          n 0 ν) =
      ∑ k : Fin dim, ∑ l : Fin dim,
        (ρ (wraparoundWordA N T L hT hT3 n hn ν hν V_plus u)) k l *
        conj ((ρ (wraparoundWordB N T L hT3 n hn ν hν u)) k l) := by
  rw [plaquetteProduct_extendToFullConfig_wraparound N T L hT hT3 V_plus u n hn ν hν]
  exact repCharacter_mul_inv_eq_sum_matrixElement_conj ρ hU _ _

#print axioms repCharacter_plaquetteProduct_wraparound_eq_halfWords

/-- **Crossing plaquette Boltzmann factor expansion** (B.2e.3 step (iii), §8.11.100).
The single-plaquette Boltzmann factor `exp(c · Re Tr(word))` (`c ≥ 0`) of a crossing
plaquette in the merged configuration expands as a non-negative character sum, and each
character factors into the matrix-element pairing of the interface and positive
half-words:

  `exp(c·Re Tr(word)) = ∑_s coeff_s · ∑_{k,l} (ρ_s (W_int u))_{kl}·conj((ρ_s (W_pos V⁺))_{kl})`

with `coeff_s ≥ 0`.  Combines `plaquette_boltzmann_character_expansion_single` (hcoeff
threading) with `repCharacter_plaquetteProduct_crossing_eq_halfWords`.
0 sorries, 0 new axioms. -/
lemma crossing_plaquette_boltzmann_matrixElement_expansion
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (c : ℝ) (hc : 0 ≤ c)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) (ν : Fin 4) (hν : ν ≠ 0) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s),
      ∀ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
        (u : PosInterfaceConfig N T L),
        (Real.exp (c * (Matrix.trace ((plaquetteProduct N
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) n 0 ν : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
          ∑ s : ι, (coeff s : ℂ) * ∑ k : Fin (dims s), ∑ l : Fin (dims s),
            (ρ s (crossingWordInt N T L n hn ν hν u)) k l *
            conj ((ρ s (crossingWordPos N T L hT n hn ν hν V_plus)) k l) := by
  obtain ⟨ι, hι, dims, ρ, hU, _hMeas, _hIrr, _hDims, coeff, hcoeff, hexp⟩ :=
    plaquette_boltzmann_character_expansion_single N c hc
  letI : Fintype ι := hι
  refine ⟨ι, hι, dims, ρ, hU, coeff, hcoeff, fun V_plus u => ?_⟩
  rw [hexp]
  apply Finset.sum_congr rfl; intro s _
  rw [repCharacter_plaquetteProduct_crossing_eq_halfWords N T L hT (ρ s) (hU s)
    V_plus u n hn ν hν]

#print axioms crossing_plaquette_boltzmann_matrixElement_expansion

/-- **Trace cyclicity for the crossing word** (B.2e.3 step (iv-a), helper).
For any `A b c D : SU N`, the real trace of the four-factor crossing word
`A⁻¹·b·c⁻¹·D⁻¹` equals that of `(A·D)⁻¹·(b·c⁻¹)`.  This is pure trace cyclicity:
`Tr(A⁻¹·b·c⁻¹·D⁻¹) = Tr(D⁻¹·A⁻¹·b·c⁻¹) = Tr((A·D)⁻¹·(b·c⁻¹))`, using
`Matrix.trace_mul_comm` and `(A·D)⁻¹ = D⁻¹·A⁻¹` (`mul_inv_rev`).  It is the
trace-level content that puts the crossing plaquette Boltzmann factor into the
PD-kernel-pullback form `k((W_pos)⁻¹·W_int)`.  0 sorries, 0 new axioms. -/
lemma reTrace_crossing (N : ℕ) (A b c D : SU N) :
    (Matrix.trace ((A⁻¹ * b * c⁻¹ * D⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ)).re =
    (Matrix.trace (((A * D)⁻¹ * (b * c⁻¹) : SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  have hinv : ((A * D)⁻¹ : SU N) = D⁻¹ * A⁻¹ := mul_inv_rev A D
  have htr : Matrix.trace ((A⁻¹ * b * c⁻¹ * D⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.trace (((A * D)⁻¹ * (b * c⁻¹) : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hinv]
    simp only [Submonoid.coe_mul]
    rw [Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  rw [htr]

#print axioms reTrace_crossing

/-- **Crossing plaquette Boltzmann factor in PD-kernel-pullback form** (B.2e.3 step
(iv-a), §8.11.99).  For a crossing plaquette based at `n` (signedTime `-1`), directions
`(0, ν)`, the Boltzmann factor `exp(c·Re Tr(word))` in the merged configuration equals
the PD function `k_c(g) = exp(c·Re Tr(g))` evaluated at `(W_pos V⁺)⁻¹ · W_int u` — the
PD kernel form `k((W x)⁻¹·W y)` with `x = V⁺` (ket) and `y = u` (bra).  This is the
matrix-element lift of the reflection = inversion mechanism: the reflection
`reflectPosToNeg` turns the ket word into the inverse of the positive half-word, and
trace cyclicity (`reTrace_crossing`) collects the four link factors into the two
half-words.  0 sorries, 0 new axioms. -/
lemma crossing_plaquette_boltzmann_eq_pd_kernel (N T L : ℕ) [NeZero T] [NeZero L]
    (hT : Odd T) (c : ℝ)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L)
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    Real.exp (c * Complex.re (Matrix.trace ((plaquetteProduct N
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) n 0 ν : SU N) :
        Matrix (Fin N) (Fin N) ℂ))) =
    Real.exp (c * Complex.re (Matrix.trace (
        ((crossingWordPos N T L hT n hn ν hν V_plus)⁻¹ *
          crossingWordInt N T L n hn ν hν u : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
  rw [plaquetteProduct_extendToFullConfig_crossing N T L hT V_plus u n hn ν hν]
  exact congrArg (fun x => Real.exp (c * x)) (reTrace_crossing N _ _ _ _)

#print axioms crossing_plaquette_boltzmann_eq_pd_kernel

/-- The positive-link character factor `Φ_w(U⁺) = ∏_{l ∈ L_U} χ_{w(l)}(U⁺_l)`.
The `if hpos` guards the site-membership proof needed to index `U⁺` (a positive-site
config) at a link `l`; for `l ∈ interfaceLinkPos` the guard is always true.
This is the `U⁺`-dependent factor in the character triple product separation (step 4d). -/
noncomputable def charFactorPos (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) : ℂ :=
  ∏ l ∈ interfaceLinkPos T L,
    if hpos : l.val.1 ∈ positiveSites T L then
      repCharacter (ρ (w l)) (U_plus ⟨(l.val.1, l.val.2), hpos⟩)
    else 1

#print axioms charFactorPos

/-- The interface-link character factor `Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(u⁰_l)`.
This is the `u⁰`-dependent factor in the character triple product separation (step 4d). -/
noncomputable def charFactorInt (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) : ℂ :=
  ∏ l ∈ interfaceLinkInt T L,
    if hint : l.val.1 ∈ interfaceSites T L then
      repCharacter (ρ (w l)) (U_zero ⟨(l.val.1, l.val.2), hint⟩)
    else 1

#print axioms charFactorInt

/-- **Step 5 sub-lemma 1: charFactorInt decomposes into temporal and spatial parts.**
The interface-link character factor `Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(u⁰_l)` decomposes
as `Ψ_w^{temporal}(u⁰_t) · Ψ_w^{spatial}(u⁰_s)` where the temporal product is over
`interfaceLinkTemporal` (μ = 0 links) and the spatial product is over
`interfaceLinkSpatial` (μ ≠ 0 links).  This follows from
`prod_interfaceLinkInt_eq_temporal_spatial` (the temporal/spatial partition of
`interfaceLinkInt`).  See §8.11.40 step 5. -/
lemma charFactorInt_eq_temporal_spatial (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (w : InterfaceLink T L → ι)
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    charFactorInt N T L ι dims ρ w U_zero =
      (∏ l ∈ interfaceLinkTemporal T L,
        if hint : l.val.1 ∈ interfaceSites T L then
          repCharacter (ρ (w l)) (U_zero ⟨(l.val.1, l.val.2), hint⟩)
        else 1) *
      (∏ l ∈ interfaceLinkSpatial T L,
        if hint : l.val.1 ∈ interfaceSites T L then
          repCharacter (ρ (w l)) (U_zero ⟨(l.val.1, l.val.2), hint⟩)
        else 1) := by
  unfold charFactorInt
  exact prod_interfaceLinkInt_eq_temporal_spatial T L (fun l =>
    if hint : l.val.1 ∈ interfaceSites T L then
      repCharacter (ρ (w l)) (U_zero ⟨(l.val.1, l.val.2), hint⟩)
    else 1)

#print axioms charFactorInt_eq_temporal_spatial

/-- The negative-link character factor `V_w(U⁻) = ∏_{l ∈ L_V} χ_{dual(w(l))}(U⁻_l)`.
This is the `U⁻`-dependent factor in the character triple product separation (step 4d). -/
noncomputable def charFactorNeg (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) : ℂ :=
  ∏ l ∈ interfaceLinkNeg T L,
    if hneg : l.val.1 ∈ negativeSites T L then
      repCharacter (ρ (dual (w l))) (U_minus ⟨(l.val.1, l.val.2), hneg⟩)
    else 1

#print axioms charFactorNeg

set_option maxHeartbeats 1000000 in
/-- **Step 4d: character triple product separation.** For `U = extendToFullConfig
(reflectPosToNeg V⁺) u`, the character triple product `Φ_w(U)·Ψ_w(U)·star(V_w(U))`
separates into three factors depending on disjoint variables:
`charFactorPos (restrictToPositive u)` (depends on `u`'s positive part),
`charFactorInt (restrictToInterface u)` (depends on `u`'s interface part), and
`star (charFactorNeg (reflectPosToNeg V⁺))` (depends on `V⁺` only).
Uses `Finset.prod_congr` + `dif_pos` + the specialized bridge lemmas
`interfaceLinkVar_extendToFullConfig_pos'/int'/neg'` + `interfaceLinkPos/Int/Neg_mem_iff`.
0 sorries, 0 custom axioms. -/
lemma charTripleProduct_separate
    (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (w : InterfaceLink T L → ι)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) :
    (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l))
        (interfaceLinkVar N T L (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
    (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l))
        (interfaceLinkVar N T L (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
    star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l)))
        (interfaceLinkVar N T L (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) =
    charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) *
    charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) *
    star (charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus)) := by
  set U := extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u
  -- Pos factor
  have h_pos : ∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l) =
      charFactorPos N T L ι dims ρ w (restrictToPositive N T L u) := by
    simp only [charFactorPos]
    apply Finset.prod_congr rfl
    intro l hl
    rw [dif_pos ((interfaceLinkPos_mem_iff T L l).mp hl)]
    rw [interfaceLinkVar_extendToFullConfig_pos' N T L V_plus u l
        ((interfaceLinkPos_mem_iff T L l).mp hl)]
    rfl
  -- Int factor
  have h_int : ∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l) =
      charFactorInt N T L ι dims ρ w (restrictToInterface N T L u) := by
    simp only [charFactorInt]
    apply Finset.prod_congr rfl
    intro l hl
    rw [dif_pos ((interfaceLinkInt_mem_iff T L l).mp hl)]
    rw [interfaceLinkVar_extendToFullConfig_int' N T L V_plus u l
        ((interfaceLinkInt_mem_iff T L l).mp hl)]
    rfl
  -- Neg factor
  have h_neg : ∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l) =
      charFactorNeg N T L ι dims ρ dual w (reflectPosToNeg N T L V_plus) := by
    simp only [charFactorNeg]
    apply Finset.prod_congr rfl
    intro l hl
    rw [dif_pos ((interfaceLinkNeg_mem_iff T L l).mp hl)]
    rw [interfaceLinkVar_extendToFullConfig_neg' N T L V_plus u l
        ((interfaceLinkNeg_mem_iff T L l).mp hl)]
  rw [h_pos, h_int, h_neg]

#print axioms charTripleProduct_separate

set_option maxHeartbeats 1000000 in
/-- The transfer-matrix integrand transforms correctly under the change of variables
`U⁻ ↦ V⁺ = reflectNegToPos(U⁻)`: the integrand at `U⁻` equals the transformed
integrand at `V⁺ = reflectNegToPos(U⁻)`.

This is the pointwise identity underlying `transferMatrix_change_of_variables`
(sub-step 2 of step (b)). It uses:
- `reflectToPosInterface_involution` to rewrite the ψ argument,
- `neg_action_reflection_os_periodic` + `reflect_extendToFullConfig_posInterface` +
  `wilsonActionOSPositive_dependsOnlyOnPosInterface` to rewrite S⁻ → S⁺(V⁺, σ(u⁰)),
- `reflectPosToNeg_reflectNegToPos` to show S_int is unchanged. -/
lemma transferMatrix_integrand_change_of_variables (hT : Odd T)
    (ψ : PosInterfaceConfig N T L → ℝ)
    (u : PosInterfaceConfig N T L)
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) :
    ψ (reflectToPosInterface N T L U_minus (restrictToInterface N T L u)) *
    Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
      wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) / 2 +
      wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u))) =
    ψ (mergePosInterface N T L (reflectNegToPos N T L U_minus)
        (sigmaInterface N T L (restrictToInterface N T L u))) *
    Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
      osPositiveOfPosInterface N T L β
        (mergePosInterface N T L (reflectNegToPos N T L U_minus)
          (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
      wilsonActionOSInterface N T L β
        (extendToFullConfig N T L (reflectPosToNeg N T L (reflectNegToPos N T L U_minus)) u))) := by
  -- Key substitution: reflectPosToNeg (reflectNegToPos U_minus) = U_minus
  have hinv : reflectPosToNeg N T L (reflectNegToPos N T L U_minus) = U_minus :=
    reflectPosToNeg_reflectNegToPos N T L hT U_minus
  -- Step 1: rewrite the ψ argument via reflectToPosInterface_involution
  have hψ : reflectToPosInterface N T L U_minus (restrictToInterface N T L u) =
      mergePosInterface N T L (reflectNegToPos N T L U_minus)
        (sigmaInterface N T L (restrictToInterface N T L u)) := by
    conv_lhs => rw [show U_minus = reflectPosToNeg N T L (reflectNegToPos N T L U_minus) from hinv.symm]
    exact reflectToPosInterface_involution N T L hT (reflectNegToPos N T L U_minus)
      (restrictToInterface N T L u)
  -- Step 2: rewrite S⁻ via neg_action_reflection_os_periodic
  have hSneg : wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) =
      wilsonActionOSPositive N T L β (reflectLinkVariable N (extendToFullConfig N T L U_minus u)) :=
    neg_action_reflection_os_periodic N T L β hT (extendToFullConfig N T L U_minus u)
  -- Step 3: the positive+interface restriction of the reflected config
  have hrestrict : restrictPosInterface N T L
      (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
        (reflectLinkVariable N (extendToFullConfig N T L U_minus u))) =
      mergePosInterface N T L (reflectNegToPos N T L U_minus)
        (sigmaInterface N T L (restrictToInterface N T L u)) := by
    conv_lhs => rw [show U_minus = reflectPosToNeg N T L (reflectNegToPos N T L U_minus) from hinv.symm]
    exact reflect_extendToFullConfig_posInterface N T L hT (reflectNegToPos N T L U_minus) u
  -- Step 4: S⁺ of the reflected config = osPositiveOfPosInterface(mergePosInterface ...)
  have hSpos : wilsonActionOSPositive N T L β (reflectLinkVariable N (extendToFullConfig N T L U_minus u)) =
      osPositiveOfPosInterface N T L β
        (mergePosInterface N T L (reflectNegToPos N T L U_minus)
          (sigmaInterface N T L (restrictToInterface N T L u))) := by
    unfold osPositiveOfPosInterface
    apply wilsonActionOSPositive_dependsOnlyOnPosInterface N T L β
      (reflectLinkVariable N (extendToFullConfig N T L U_minus u))
      (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
        (mergePosInterface N T L (reflectNegToPos N T L U_minus)
          (sigmaInterface N T L (restrictToInterface N T L u))))
    intro n μ hn
    have hV : (reflectLinkVariable N (extendToFullConfig N T L U_minus u)).value n μ =
        (restrictPosInterface N T L
          (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
            (reflectLinkVariable N (extendToFullConfig N T L U_minus u)))) ⟨(n, μ), hn⟩ := by
      rfl
    rw [hV, hrestrict]
    simp only [extendLinkVariable, dif_pos hn]
  -- Step 5: S_int is unchanged (reflectPosToNeg (reflectNegToPos U_minus) = U_minus)
  have hSint : wilsonActionOSInterface N T L β
      (extendToFullConfig N T L (reflectPosToNeg N T L (reflectNegToPos N T L U_minus)) u) =
      wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u) := by
    rw [hinv]
  -- Assemble
  rw [hψ, hSneg, hSpos, hSint]

#print axioms transferMatrix_integrand_change_of_variables

/-- The transfer matrix after the change of variables `U⁻ ↦ V⁺ = reflectNegToPos(U⁻)`.

After applying `reflectLinkVariable_measurePreserving_between` (with
`sourceSites = negativeSites`, `targetSites = positiveSites`) and the pointwise
identity `transferMatrix_integrand_change_of_variables`, the transfer matrix
becomes:

    (Tψ)(u) = exp(-β·S⁺(u)/2) · ∫_{V⁺} ψ(V⁺, σ(u⁰)) ·
              exp(-β·(S⁺(V⁺, σ(u⁰))/2 + S_int(U⁺, u⁰, reflect(V⁺)))) dμ⁺(V⁺)

This is the "reflected" form of the transfer matrix, where the negative-time
integral has been replaced by a positive-time integral via the measure-preserving
reflection. -/
noncomputable def transferMatrixReflected (ψ : PosInterfaceConfig N T L → ℝ)
    (u : PosInterfaceConfig N T L) : ℝ :=
  let S_plus := osPositiveOfPosInterface N T L β u
  ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
    Real.exp (-β * (S_plus / 2 +
      osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
      wilsonActionOSInterface N T L β
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))
    ∂ haarMeasurePositive N T L

set_option maxHeartbeats 1000000 in
/-- The transfer matrix equals the reflected transfer matrix, via the change of
variables `U⁻ ↦ V⁺ = reflectNegToPos(U⁻)`.

This is the integral-level change of variables (sub-step 2 of step (b)). It applies
`reflectLinkVariable_measurePreserving_between` (measure-preserving from μ⁻ to μ⁺)
together with the pointwise identity `transferMatrix_integrand_change_of_variables`. -/
lemma transferMatrix_change_of_variables (hT : Odd T)
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
    transferMatrixCorrect N T L β ψ u = transferMatrixReflected N T L β ψ u := by
  -- The measure-preserving map: U⁻ ↦ V⁺ = reflectNegToPos(U⁻)
  have hMP : MeasurePreserving (reflectNegToPos N T L)
      (haarMeasureNegative N T L) (haarMeasurePositive N T L) := by
    unfold haarMeasureNegative haarMeasurePositive reflectNegToPos
    exact reflectLinkVariable_measurePreserving_between N
      (negativeSites T L) (positiveSites T L)
      (fun n hn => reflectSite_mem_positive_of_negative hT hn)
      (fun n hn => reflectSite_mem_negative_of_positive hT hn)
  -- Define the reflected integrand
  set f_reflected := fun (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) =>
    ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
    Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
      osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
      wilsonActionOSInterface N T L β
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))
  -- Change of variables via integral_map + hMP.map_eq
  -- integral_map gives: ∫ y, f y ∂(map g μ) = ∫ x, f (g x) ∂μ
  -- So .symm gives: ∫ x, f (g x) ∂μ = ∫ y, f y ∂(map g μ)
  have h_cov : ∫ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),
      f_reflected (reflectNegToPos N T L U_minus) ∂ haarMeasureNegative N T L =
    ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      f_reflected V_plus ∂ haarMeasurePositive N T L := by
    rw [← hMP.map_eq]
    have h_int : Integrable f_reflected
        (Measure.map (reflectNegToPos N T L) (haarMeasureNegative N T L)) := by
      rw [hMP.map_eq]; exact hψ_int
    exact (integral_map hMP.measurable.aemeasurable h_int.aestronglyMeasurable).symm
  -- The original integrand equals f_reflected(reflectNegToPos U⁻) pointwise
  have h_ptwise : ∀ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),
      ψ (reflectToPosInterface N T L U_minus (restrictToInterface N T L u)) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) / 2 +
        wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u))) =
      f_reflected (reflectNegToPos N T L U_minus) :=
    transferMatrix_integrand_change_of_variables N T L β hT ψ u
  -- Assemble via calc: unfold → pointwise rewrite → change of variables → unfold
  calc transferMatrixCorrect N T L β ψ u
      = ∫ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),
          ψ (reflectToPosInterface N T L U_minus (restrictToInterface N T L u)) *
          Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
            wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) / 2 +
            wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u)))
          ∂ haarMeasureNegative N T L := by
        unfold transferMatrixCorrect; dsimp only
    _ = ∫ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),
          f_reflected (reflectNegToPos N T L U_minus) ∂ haarMeasureNegative N T L := by
        congr 1; funext U_minus; exact h_ptwise U_minus
    _ = ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
          f_reflected V_plus ∂ haarMeasurePositive N T L := h_cov
    _ = transferMatrixReflected N T L β ψ u := by
        unfold transferMatrixReflected; dsimp only

#print axioms transferMatrix_change_of_variables

/-- **Step 4b (ℝ-valued): split the transfer-matrix exp and pull out the V⁺-independent
factor.** The reflected transfer matrix
`(Tψ)(u) = ∫_{V⁺} ψ(merge(V⁺, σ(u⁰))) · exp(-β·(S⁺(u)/2 + S⁺(V⁺')/2 + S_int(U))) dμ⁺(V⁺)`
factors as `exp(-β·S⁺(u)/2) · ∫_{V⁺} ψ(merge(V⁺, σ(u⁰))) · exp(-β·(S⁺(V⁺')/2 + S_int(U))) dμ⁺(V⁺)`,
pulling the V⁺-independent `exp(-β·S⁺(u)/2)` out of the V⁺ integral via `Real.exp_add`
and `integral_const_mul`. This is the ℝ-valued core of step 4b of the Fubini reduction
(sub-step (iii) of Lemma 2). 0 sorries, 0 custom axioms. -/
lemma transferMatrixReflected_split_exp_real
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L) :
    transferMatrixReflected N T L β ψ u =
    Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) *
    ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))
      ∂ haarMeasurePositive N T L := by
  unfold transferMatrixReflected
  dsimp only
  -- Pointwise: split exp(-β*(a+b+c)) = exp(-β*a) * exp(-β*(b+c)) and rearrange
  have h_ptwise : ∀
      (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) =
      Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) *
      (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
       Real.exp (-β * (osPositiveOfPosInterface N T L β
         (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
       wilsonActionOSInterface N T L β
         (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))) := by
    intro V_plus
    have h_arg : (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) =
        (-β * osPositiveOfPosInterface N T L β u / 2) +
        (-β * (osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) := by ring
    rw [h_arg, Real.exp_add]
    ring
  rw [show (∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
        osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))
      ∂ haarMeasurePositive N T L) =
    (∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) *
      (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
       Real.exp (-β * (osPositiveOfPosInterface N T L β
         (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
       wilsonActionOSInterface N T L β
         (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      ∂ haarMeasurePositive N T L) from by
    congr 1; funext V_plus; exact h_ptwise V_plus]
  rw [integral_const_mul]

#print axioms transferMatrixReflected_split_exp_real

/-- **Step 4b (ℂ-valued): the transfer-matrix inner-product integrand, coerced to ℂ,
with the V⁺-independent exp factor pulled out.** Combining
`transferMatrixReflected_split_exp_real` (exp split + `integral_const_mul`) with
`Complex.ofReal_mul` and `integral_complex_ofReal`, the ℂ-valued integrand
`Complex.ofReal (ψ u · (Tψ)(u))` factors as
`Complex.ofReal (ψ u · exp(-β·S⁺(u)/2)) · ∫_{V⁺} Complex.ofReal (ψ(merge(V⁺, σ(u⁰))) ·
exp(-β·(S⁺(V⁺')/2 + S_int(U)))) dμ⁺(V⁺)`. This is the pointwise identity (step 4b of the
Fubini reduction, sub-step (iii) of Lemma 2) that step 4a's product-measure integral will
be rewritten with, preparing for the character-expansion substitution (step 4c).
0 sorries, 0 custom axioms. -/
lemma transferMatrixReflected_split_exp_complex
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L) :
    Complex.ofReal (ψ u * transferMatrixReflected N T L β ψ u) =
    Complex.ofReal (ψ u * Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)) *
    ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * (osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
          wilsonActionOSInterface N T L β
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
      ∂ haarMeasurePositive N T L := by
  rw [transferMatrixReflected_split_exp_real]
  -- LHS = Complex.ofReal (ψ u * (Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) * ∫ ...))
  set c_exp := Real.exp (-β * osPositiveOfPosInterface N T L β u / 2) with hc_exp
  set I_split := ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
      ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))
      ∂ haarMeasurePositive N T L with hI_split
  -- Rearrange ψ u * (c_exp * I_split) = (ψ u * c_exp) * I_split
  rw [show ψ u * (c_exp * I_split) = (ψ u * c_exp) * I_split from by ring]
  -- Split the Complex.ofReal over the product
  rw [Complex.ofReal_mul]
  -- Convert Complex.ofReal I_split to ∫ Complex.ofReal (integrand) via integral_complex_ofReal
  have h_cofR : Complex.ofReal I_split =
      ∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * (osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
            wilsonActionOSInterface N T L β
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
        ∂ haarMeasurePositive N T L := by
    rw [hI_split]
    exact (integral_complex_ofReal).symm
  rw [h_cofR]

#print axioms transferMatrixReflected_split_exp_complex

/-- **Step 4c Part A (pointwise character-expansion substitution).** For each
`V⁺`, the ℂ-valued transfer-matrix integrand
`Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·(S⁺(V⁺')/2 + S_int(U))))` factors as
`Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·S⁺(V⁺')/2)) · ((C : ℂ) · ∑_w …)`,
where `U = extendToFullConfig(reflectPosToNeg(V⁺), u)` and the second factor is the
character expansion of `exp(-β·S_int(U))` (coerced to ℂ), supplied as the
hypothesis `h_char` (obtained from `interface_boltzmann_character_expansion`).

This is a **pointwise** identity (no integrability needed): split the exp via
`Real.exp_add`, split `Complex.ofReal` via `Complex.ofReal_mul`, then substitute
the character expansion `h_char U` (the `Complex.ofReal (exp …)` vs
`(exp … : ℂ)` coercion mismatch is handled up to defeq by `rw`). 0 sorries,
0 custom axioms. -/
lemma integrand_character_expansion_pointwise
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l))) :
    ∀ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
    Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * (osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
        wilsonActionOSInterface N T L β
          (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)))) =
    Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
    ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
      (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
      star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l))) := by
  intro V_plus
  set merge := mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))
  set U := extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u
  -- Split exp(-β*(a+b)) = exp(-β*a) * exp(-β*b)
  have h_arg : (-β * (osPositiveOfPosInterface N T L β merge / 2 +
      wilsonActionOSInterface N T L β U)) =
      (-β * osPositiveOfPosInterface N T L β merge / 2) +
      (-β * wilsonActionOSInterface N T L β U) := by ring
  rw [h_arg, Real.exp_add]
  -- Rearrange ψ merge * (exp(-β*a) * exp(-β*b)) = (ψ merge * exp(-β*a)) * exp(-β*b)
  rw [show ψ merge * (Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2) *
      Real.exp (-β * wilsonActionOSInterface N T L β U)) =
      (ψ merge * Real.exp (-β * osPositiveOfPosInterface N T L β merge / 2)) *
      Real.exp (-β * wilsonActionOSInterface N T L β U) from by ring]
  -- Split Complex.ofReal over the product
  rw [Complex.ofReal_mul]
  -- Substitute the character expansion: Complex.ofReal (exp(-β*S_int U)) is defeq to
  -- (exp(-β*S_int U) : ℂ), so h_char U rewrites it to (C : ℂ) * ∑ w …
  rw [h_char U]

#print axioms integrand_character_expansion_pointwise

/-- **General Fubini + constant-pulling lemma.** For a finite index type `ι`,
a constant `C : ℂ`, scalar coefficients `F : ι → ℝ`, a V⁺-dependent prefactor
`A : α → ℂ`, and V⁺-dependent summands `X : ι → α → ℂ`, the integral
`∫ A x * (C * ∑_w (F w) * X w x) ∂μ` equals
`C * ∑_w (F w) * ∫ A x * X w x ∂μ`, provided each term
`(F w) * (A x * X w x)` is integrable.

This is the abstract core of step 4c (Fubini exchange): it rearranges the
integrand pointwise (`A * (C * ∑ …) = C * ∑ (F w) * (A * X_w)` via
`Finset.mul_sum`), pulls the constant `C` out (`integral_const_mul`, no
integrability), exchanges the finite sum with the integral
(`integral_finsetSum`, needs the integrability hypothesis), then pulls each
`(F w)` out (`integral_const_mul`). 0 sorries, 0 custom axioms. -/
lemma integral_finsetSum_pull_constants
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (C : ℂ) (F : ι → ℝ) (A : α → ℂ) (X : ι → α → ℂ)
    (h_int : ∀ w : ι, Integrable (fun x => (F w : ℂ) * (A x * X w x)) μ) :
    ∫ x, A x * (C * ∑ w : ι, (F w : ℂ) * X w x) ∂μ =
      C * ∑ w : ι, (F w : ℂ) * ∫ x, A x * X w x ∂μ := by
  -- Pointwise rearrangement: A x * (C * ∑ w (F w) * X w x) = C * ∑ w (F w) * (A x * X w x)
  rw [show (∫ x, A x * (C * ∑ w : ι, (F w : ℂ) * X w x) ∂μ) =
          (∫ x, C * ∑ w : ι, (F w : ℂ) * (A x * X w x) ∂μ) from by
    congr 1; funext x
    rw [← mul_assoc, mul_comm (A x) C, mul_assoc, Finset.mul_sum]
    refine congrArg (C * ·) (Finset.sum_congr rfl (fun w _ => by ring))]
  -- Pull the constant C out of the integral (no integrability needed)
  rw [integral_const_mul]
  -- Exchange the finite sum ∑_w with the integral (needs integrability)
  rw [integral_finsetSum Finset.univ]
  · -- Pull each (F w : ℂ) out of its integral (no integrability needed)
    simp only [integral_const_mul]
  · exact fun w _ => h_int w

#print axioms integral_finsetSum_pull_constants

set_option maxHeartbeats 1000000 in
/-- **Step 4c (Fubini exchange: finite sum ↔ V⁺ integral).** Combining
`transferMatrixReflected_split_exp_complex` (step 4b), the pointwise character-expansion
substitution `integrand_character_expansion_pointwise` (step 4c Part A), and
`integral_finsetSum_pull_constants` (Fubini + constant-pulling), the ℂ-valued transfer
matrix inner-product integrand factors as
```
Complex.ofReal (ψ u · (Tψ)(u)) =
  Complex.ofReal (ψ u · exp(-β·S⁺(u)/2)) ·
  (C · ∑_w (F w) · ∫_{V⁺} Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·S⁺(V⁺')/2)) ·
    Φ_w(U) · Ψ_w(U) · V_w(U) dμ⁺(V⁺))
```
where `U = extendToFullConfig(reflectPosToNeg(V⁺), u)`, and `Φ_w/Ψ_w/V_w` are the
character products from `interface_boltzmann_character_expansion`.

The integrability hypothesis `h_int` (each term `(F w) · (A · Φ_w · Ψ_w · V_w)` is
integrable w.r.t. `μ⁺`) is taken as a parameter — it will be discharged separately
using character boundedness (`repCharacter_norm_le_dim`) + action boundedness +
`Integrable.mono` (see design doc §8.11.10). 0 sorries, 0 custom axioms. -/
lemma transfer_matrix_fubini_character_expansion
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (ψ : PosInterfaceConfig N T L → ℝ) (u : PosInterfaceConfig N T L)
    (C : ℝ) (ι : Type) [Fintype ι] (dims : ι → ℕ)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (dual : ι → ι) (F : (InterfaceLink T L → ι) → ℝ)
    (h_char : ∀ U : LinkVariable (SU N) (PeriodicSite T L),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)))
    (h_int : ∀ w : InterfaceLink T L → ι,
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
  -- Step 1: apply the exp split (step 4b) to make the V⁺ integral explicit
  rw [transferMatrixReflected_split_exp_complex]
  -- Step 2: cancel the common prefactor (V⁺-independent factor)
  congr 1
  -- Step 3: rewrite the V⁺ integral integrand pointwise using the character expansion
  have h_pw := integrand_character_expansion_pointwise N T L β ψ u C ι dims ρ dual F h_char
  rw [show (∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L V_plus
            (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * (osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2 +
            wilsonActionOSInterface N T L β
              (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))))
        ∂ haarMeasurePositive N T L) =
      (∫ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)),
        Complex.ofReal (ψ (mergePosInterface N T L V_plus
            (sigmaInterface N T L (restrictToInterface N T L u))) *
          Real.exp (-β * osPositiveOfPosInterface N T L β
            (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
        ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)))
        ∂ haarMeasurePositive N T L) from by
    congr 1; funext V_plus; exact h_pw V_plus]
  -- Step 4: inline the Fubini exchange steps (avoids large-expression whnf timeout)
  -- 4a: rearrange integrand pointwise: A * (C * ∑ w, F w * X) = C * ∑ w, F w * (A * X)
  simp only [show ∀ V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L),
    Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
      Real.exp (-β * osPositiveOfPosInterface N T L β
        (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
    ((C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
      (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
      star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l))) =
    (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
      (Complex.ofReal (ψ (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) *
        Real.exp (-β * osPositiveOfPosInterface N T L β
          (mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u))) / 2)) *
      ((∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
       (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l)) *
       star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) l))))
    from fun V_plus => by
      rw [← mul_assoc, mul_comm _ (C : ℂ), mul_assoc, Finset.mul_sum]
      refine congrArg ((C : ℂ) * ·) (Finset.sum_congr rfl (fun w _ => by ring))]
  -- 4b: pull C out of the integral
  rw [integral_const_mul]
  -- 4c: exchange the finite sum with the integral
  rw [integral_finsetSum Finset.univ]
  · simp only [integral_const_mul]
  · exact fun w _ => h_int w

#print axioms transfer_matrix_fubini_character_expansion

/-! ### B.2e.3 step (iv-b1): crossing/non-crossing split of the interface Boltzmann factor

The interface Boltzmann factor `exp(-β·S_int(U))` for
`U = extendToFullConfig (reflectPosToNeg V⁺) u` splits as a product over the
**crossing plaquettes** (based at `signedTime = -1`, directions `(0, ν)`, `ν ≠ 0`) —
each in the PD-kernel-pullback form `exp(-β²)·k_c((W_pos V⁺)⁻¹·W_int u)` of step (iv-a) —
times a **rest** product over all remaining plaquette indices (non-crossing interface
plaquettes, which depend only on `u`, plus the reversed-orientation and degenerate
plaquettes, plus the non-interface plaquettes contributing `1`). -/

/-- A crossing plaquette index: based at a site of signed time `-1`, with first
direction temporal (`μ = 0`) and second direction spatial (`ν ≠ 0`). -/
abbrev isCrossingPlaquetteIdx (T L : ℕ) [NeZero T] [NeZero L] (p : PlaquetteIndex T L) : Prop :=
  p.2.1 = 0 ∧ signedTime T p.1.time = -1 ∧ p.2.2 ≠ 0

/-- The time coordinate of `n + e₀` (`addVectorPeriodic` form). -/
lemma addVectorPeriodic_zero_time (T L : ℕ) [NeZero T] [NeZero L] (n : PeriodicSite T L) :
    (addVectorPeriodic T L n 0).time = n.time + 1 := by
  simp [addVectorPeriodic]

/-- If `n` has signed time `-1`, then `n + e₀` has signed time `0`
(`addVectorPeriodic` form). -/
lemma signedTime_addVectorPeriodic_zero_of_eq_neg_one (T L : ℕ) [NeZero T] [NeZero L]
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) :
    signedTime T (addVectorPeriodic T L n 0).time = 0 := by
  rw [addVectorPeriodic_zero_time]; exact signedTime_succ_of_eq_neg_one T n.time hn

/-- A crossing plaquette is an interface plaquette: its corners have signed times
`{-1, 0, 0, -1}`, so they are neither all positive nor all negative. -/
lemma isInterfacePlaquette_of_crossing (T L : ℕ) [NeZero T] [NeZero L]
    (n : PeriodicSite T L) (hn : signedTime T n.time = -1) (ν : Fin 4) (hν : ν ≠ 0) :
    isInterfacePlaquette T L n 0 ν := by
  have h0 : signedTime T (addVectorPeriodic T L n 0).time = 0 :=
    signedTime_addVectorPeriodic_zero_of_eq_neg_one T L n hn
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, -⟩
    rw [hn] at h1; norm_num at h1
  · rintro ⟨-, h2, -, -⟩
    rw [h0] at h2; norm_num at h2

#print axioms isInterfacePlaquette_of_crossing

/-- Triple products over plaquette indices as a single product over `PlaquetteIndex`. -/
lemma prod_plaquetteIndex_eq_triple (T L : ℕ) [NeZero T] [NeZero L]
    (g : PeriodicSite T L → Fin 4 → Fin 4 → ℝ) :
    (∏ p : PlaquetteIndex T L, g p.1 p.2.1 p.2.2) =
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4, g n μ ν := by
  rw [← Finset.univ_product_univ, Finset.prod_product]
  apply Finset.prod_congr rfl; intro n _
  rw [← Finset.univ_product_univ, Finset.prod_product]

/-- Split a product over `PlaquetteIndex` into crossing and non-crossing parts. -/
lemma prod_plaquetteIndex_split_crossing (T L : ℕ) [NeZero T] [NeZero L]
    (F : PlaquetteIndex T L → ℝ) :
    (∏ p : PlaquetteIndex T L, F p) =
    (∏ p ∈ Finset.univ.filter (isCrossingPlaquetteIdx T L), F p) *
    (∏ p ∈ Finset.univ.filter (fun q => ¬ isCrossingPlaquetteIdx T L q), F p) := by
  classical
  exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (isCrossingPlaquetteIdx T L) F).symm

/-- **Interface Boltzmann factor: crossing/rest split** (B.2e.3 step (iv-b1)).
For `U = extendToFullConfig (reflectPosToNeg V⁺) u`, the interface Boltzmann factor
`exp(-β·S_int(U))` equals the product over crossing plaquettes of the PD-kernel-pullback
factors `exp(-β²)·k_c((W_pos V⁺)⁻¹·W_int u)` (step (iv-a),
`crossing_plaquette_boltzmann_eq_pd_kernel`), times the rest product over all
non-crossing plaquette indices.  0 sorries, 0 new axioms. -/
lemma interface_boltzmann_eq_crossing_mul_rest (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) :
    Real.exp (-β * wilsonActionOSInterface N T L β
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)) =
    (∏ p ∈ Finset.univ.filter (isCrossingPlaquetteIdx T L),
        if h : signedTime T p.1.time = -1 ∧ p.2.2 ≠ 0 then
          Real.exp (-(β * β)) * Real.exp ((β * β / N) * Complex.re (Matrix.trace (
            ((crossingWordPos N T L hT p.1 h.1 p.2.2 h.2 V_plus)⁻¹ *
              crossingWordInt N T L p.1 h.1 p.2.2 h.2 u : SU N) :
              Matrix (Fin N) (Fin N) ℂ)))
        else 1) *
    (∏ p ∈ Finset.univ.filter (fun q => ¬ isCrossingPlaquetteIdx T L q),
        if isInterfacePlaquette T L p.1 p.2.1 p.2.2 then
          Real.exp (-(β * β)) * Real.exp ((β * β / N) * Complex.re (Matrix.trace (
            (plaquetteProduct N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)
              p.1 p.2.1 p.2.2 : SU N) : Matrix (Fin N) (Fin N) ℂ)))
        else 1) := by
  classical
  rw [exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract]
  rw [← prod_plaquetteIndex_eq_triple, prod_plaquetteIndex_split_crossing]
  congr 1
  apply Finset.prod_congr rfl; intro p hp
  obtain ⟨-, hμ, hn, hν⟩ := Finset.mem_filter.mp hp
  rw [dif_pos ⟨hn, hν⟩, hμ,
    if_pos (isInterfacePlaquette_of_crossing T L p.1 hn p.2.2 hν),
    crossing_plaquette_boltzmann_eq_pd_kernel N T L hT (β * β / N) V_plus u p.1 hn p.2.2 hν]

#print axioms interface_boltzmann_eq_crossing_mul_rest

/-- Crossing plaquettes as a subtype of `PlaquetteIndex`. -/
abbrev CrossingPlaquette (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {p : PlaquetteIndex T L // isCrossingPlaquetteIdx T L p}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] :
    Fintype (CrossingPlaquette T L) := by
  classical
  exact inferInstanceAs (Fintype {p : PlaquetteIndex T L // isCrossingPlaquetteIdx T L p})

/-- **Crossing-product matrix-element expansion** (B.2e.3 step (iv-b2'), §8.11.102).
The product over all crossing plaquettes of the Boltzmann factors
`exp(c·Re Tr(word_p))` (`c ≥ 0`) in the merged configuration expands as a
non-negative-coefficient sum over assignments `w : CrossingPlaquette → ι` of products
of per-plaquette matrix-element pairings of the interface and positive half-words:

  `∏_p exp(c·Re Tr(word_p)) = ∑_w (∏_p coeff_{w p}) · ∏_p ∑_{k,l}
      (ρ_{w p} (W_int^p u))_{kl} · conj((ρ_{w p} (W_pos^p V⁺))_{kl})`

with `coeff_s ≥ 0`.  A single shared expansion datum `(ι, dims, ρ, coeff)` suffices
for all plaquettes since `plaquette_boltzmann_character_expansion_single` is
plaquette-independent.  This is the product-level input for the integrated
sum-of-squares assembly (the corrected (iv-b) path of §8.11.102).
0 sorries, 0 new axioms. -/
lemma crossing_prod_boltzmann_matrixElement_expansion
    (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s),
      ∀ (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
        (u : PosInterfaceConfig N T L),
        (∏ p : CrossingPlaquette T L,
          (Real.exp (c * Complex.re (Matrix.trace ((plaquetteProduct N
            (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) p.1.1 0 p.1.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ)) =
        ∑ w : CrossingPlaquette T L → ι,
          (∏ p : CrossingPlaquette T L, (coeff (w p) : ℂ)) *
          (∏ p : CrossingPlaquette T L, ∑ k : Fin (dims (w p)), ∑ l : Fin (dims (w p)),
            (ρ (w p) (crossingWordInt N T L p.1.1 p.2.2.1 p.1.2.2 p.2.2.2 u)) k l *
            conj ((ρ (w p) (crossingWordPos N T L hT p.1.1 p.2.2.1 p.1.2.2 p.2.2.2 V_plus)) k l)) := by
  classical
  obtain ⟨ι, hι, dims, ρ, hU, _hMeas, _hIrr, _hDims, coeff, hcoeff, hexp⟩ :=
    plaquette_boltzmann_character_expansion_single N c hc
  letI : Fintype ι := hι
  refine ⟨ι, hι, dims, ρ, hU, coeff, hcoeff, fun V_plus u => ?_⟩
  have hper : ∀ p : CrossingPlaquette T L,
      (Real.exp (c * Complex.re (Matrix.trace ((plaquetteProduct N
        (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u) p.1.1 0 p.1.2.2 : SU N) :
        Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
      ∑ s : ι, (coeff s : ℂ) * ∑ k : Fin (dims s), ∑ l : Fin (dims s),
        (ρ s (crossingWordInt N T L p.1.1 p.2.2.1 p.1.2.2 p.2.2.2 u)) k l *
        conj ((ρ s (crossingWordPos N T L hT p.1.1 p.2.2.1 p.1.2.2 p.2.2.2 V_plus)) k l) := by
    intro p
    rw [hexp]
    apply Finset.sum_congr rfl; intro s _
    rw [repCharacter_plaquetteProduct_crossing_eq_halfWords N T L hT (ρ s) (hU s)
      V_plus u p.1.1 p.2.2.1 p.1.2.2 p.2.2.2]
  rw [Finset.prod_congr rfl (fun p _ => hper p), Finset.prod_univ_sum]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.prod_mul_distrib]

#print axioms crossing_prod_boltzmann_matrixElement_expansion

