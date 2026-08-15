/-
# Transfer Matrix: Step 5 Sub-lemmas
-/

import YangMills.Proofs.TransferMatrix.Basic

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
/-! ### Step 5 sub-lemmas: temporal/spatial decomposition and u⁰_t independence

The 6-step closure plan (§8.11.40) step 5 requires showing that the temporal
interface links `u⁰_t` can be integrated out independently.  The key ingredients
are: (1) `charFactorInt` decomposes into temporal and spatial parts (using
`prod_interfaceLinkInt_eq_temporal_spatial`), (2) `fourierCoeffPos` does not
depend on `u⁰_t` (because `S⁺` only reads positive-site links and `f` satisfies
`dependsOnlyOnPosSpatialInterface`), and (3) the `u⁰_t` integral of the temporal
part of `charFactorInt` gives `δ_{w(l), trivial}` via character orthogonality.
The following lemmas formalize (1) and (2); (3) requires identifying the trivial
representation in `ι` and is deferred. -/

/-- The extended merged configurations `extendLinkVariable(mergePosInterface(V⁺, u⁰))`
and `extendLinkVariable(mergePosInterface(V⁺, u⁰'))` agree on positive-site links and
spatial interface links (μ ≠ 0) whenever `u⁰` and `u⁰'` agree on spatial interface links.
This generalizes `extendLinkVariable_merge_sigma_agree` (which is the special case
`u⁰' = σ(u⁰)`).  It is the link-by-link agreement underlying `f_temporal_invisible`:
since `dependsOnlyOnPosSpatialInterface` only constrains positive-site and
spatial-interface links, `f` gives the same value on both configurations. -/
lemma extendLinkVariable_merge_spatial_agree (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero U_zero' : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (h_spatial : ∀ (n : PeriodicSite T L) (μ : Fin 4),
      (hn : n ∈ interfaceSites T L) → μ ≠ (0 : Fin 4) →
      U_zero ⟨(n, μ), hn⟩ = U_zero' ⟨(n, μ), hn⟩)
    (n : PeriodicSite T L) (μ : Fin 4)
    (h : n ∈ positiveSites T L ∨ (n ∈ interfaceSites T L ∧ μ ≠ (0 : Fin 4))) :
    (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus U_zero)).value n μ =
    (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus U_zero')).value n μ := by
  rcases h with hpos | ⟨hint, hμ⟩
  · -- n ∈ positiveSites: both give V_plus(n,μ)
    dsimp [extendLinkVariable, mergePosInterface]
    simp [hpos, Finset.mem_union_left _ hpos]
  · -- n ∈ interfaceSites, μ ≠ 0: U_zero and U_zero' agree on spatial links
    have hdisj : Disjoint (positiveSites T L) (interfaceSites T L) := by
      unfold positiveSites interfaceSites
      rw [Finset.disjoint_filter]; intro m hm hpos hzero; linarith
    have hnpos : n ∉ positiveSites T L := Finset.disjoint_right.mp hdisj hint
    dsimp [extendLinkVariable, mergePosInterface]
    simp [hint, hnpos, Finset.mem_union_right _ hint]
    exact h_spatial n μ hint hμ

#print axioms extendLinkVariable_merge_spatial_agree

/-- If `f` depends only on positive-site and spatial-interface links
(`dependsOnlyOnPosSpatialInterface`), then `f` is invisible to changes in temporal
interface links: `f(extendLinkVariable(mergePosInterface(V⁺, u⁰))) =
f(extendLinkVariable(mergePosInterface(V⁺, u⁰')))` whenever `u⁰` and `u⁰'` agree on
spatial interface links.  This generalizes `f_sigma_invisible`. -/
lemma f_temporal_invisible (hT : Odd T)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero U_zero' : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (h_spatial : ∀ (n : PeriodicSite T L) (μ : Fin 4),
      (hn : n ∈ interfaceSites T L) → μ ≠ (0 : Fin 4) →
      U_zero ⟨(n, μ), hn⟩ = U_zero' ⟨(n, μ), hn⟩) :
    f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus U_zero)) =
    f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus U_zero')) := by
  apply hf
  intro n μ h
  exact extendLinkVariable_merge_spatial_agree N T L hT V_plus U_zero U_zero' h_spatial n μ h

#print axioms f_temporal_invisible

/-- `osPositiveOfPosInterface` is invisible to changes in temporal interface links:
`S⁺(mergePosInterface(V⁺, u⁰)) = S⁺(mergePosInterface(V⁺, u⁰'))` whenever `u⁰` and
`u⁰'` agree on spatial interface links.  This follows from `wilsonActionOSPositive_congr`
(S⁺ only reads positive-site links) and `extendLinkVariable_merge_spatial_agree` (the
two extended configs agree on positive-site links).  This generalizes
`osPositiveOfPosInterface_sigma_invariant`. -/
lemma osPositiveOfPosInterface_temporal_invariant (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero U_zero' : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (h_spatial : ∀ (n : PeriodicSite T L) (μ : Fin 4),
      (hn : n ∈ interfaceSites T L) → μ ≠ (0 : Fin 4) →
      U_zero ⟨(n, μ), hn⟩ = U_zero' ⟨(n, μ), hn⟩) :
    osPositiveOfPosInterface N T L β (mergePosInterface N T L V_plus U_zero) =
    osPositiveOfPosInterface N T L β (mergePosInterface N T L V_plus U_zero') := by
  unfold osPositiveOfPosInterface
  apply wilsonActionOSPositive_congr N T L β
  intro n μ hpos
  exact extendLinkVariable_merge_spatial_agree N T L hT V_plus U_zero U_zero' h_spatial n μ (Or.inl hpos)

#print axioms osPositiveOfPosInterface_temporal_invariant

/-- **g is invisible to changes in temporal interface links.** The function
`g(u) = f(u)·exp(-β·S⁺(u)/2)` is invisible to changes in temporal interface links:
`g(mergePosInterface(V⁺, u⁰)) = g(mergePosInterface(V⁺, u⁰'))` whenever `u⁰` and
`u⁰'` agree on spatial interface links.  This combines `f_temporal_invisible`
(f ignores temporal links) and `osPositiveOfPosInterface_temporal_invariant`
(S⁺ ignores temporal links).  This generalizes `g_posInterface_sigma_invisible`. -/
lemma g_posInterface_temporal_invisible (hT : Odd T)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero U_zero' : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (h_spatial : ∀ (n : PeriodicSite T L) (μ : Fin 4),
      (hn : n ∈ interfaceSites T L) → μ ≠ (0 : Fin 4) →
      U_zero ⟨(n, μ), hn⟩ = U_zero' ⟨(n, μ), hn⟩) :
    g_posInterface N T L hT β f (mergePosInterface N T L V_plus U_zero) =
    g_posInterface N T L hT β f (mergePosInterface N T L V_plus U_zero') := by
  unfold g_posInterface
  rw [f_temporal_invisible N T L hT f hf V_plus U_zero U_zero' h_spatial,
      osPositiveOfPosInterface_temporal_invariant N T L β hT V_plus U_zero U_zero' h_spatial]

#print axioms g_posInterface_temporal_invisible

set_option maxHeartbeats 1000000 in
/-- Reflecting the negative config `reflectPosToNeg(V⁺)` back to the positive+interface
region recovers `V⁺` on positive links and `σ(u⁰)` on interface links.

This is the key involution property for the change of variables in step (b):
`reflectToPosInterface(reflectPosToNeg(V⁺), u⁰) = mergePosInterface(V⁺, σ(u⁰))`. -/
lemma reflectToPosInterface_involution (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    reflectToPosInterface N T L (reflectPosToNeg N T L V_plus) U_zero =
    mergePosInterface N T L V_plus (sigmaInterface N T L U_zero) := by
  ext x
  rcases x with ⟨⟨n, μ⟩, hx⟩
  dsimp [reflectToPosInterface, reflectPosToNeg, sigmaInterface, mergePosInterface,
    linkVariableRestrict, reflectLinkVariable, restrictLinkVariable, extendLinkVariable,
    mergeConfigurations]
  by_cases hn_pos : n ∈ positiveSites T L
  · -- Positive case: result should be V_plus(n, μ)
    have h_reflect_neg := reflectSite_mem_negative_of_positive hT hn_pos
    have h_reflect_not_pos := reflectSite_not_mem_positive_of_positive hT hn_pos
    by_cases hμ : μ = 0
    · subst hμ
      simp [hn_pos, h_reflect_neg, h_reflect_not_pos, ReflectSite.involution, inv_inv]
    · simp [hn_pos, h_reflect_neg, h_reflect_not_pos, hμ, ReflectSite.involution]
  · -- Interface case: result should be sigmaInterface U_zero(n, μ)
    have hint : n ∈ interfaceSites T L := by
      rcases Finset.mem_union.mp hx with (h | h)
      · exact absurd h hn_pos
      · exact h
    have h_reflect_int := reflectSite_mem_interface_of_interface hT hint
    have h_reflect_not_pos := reflectSite_not_mem_positive_of_interface hT hint
    have h_reflect_not_neg := reflectSite_not_mem_negative_of_interface hT hint
    by_cases hμ : μ = 0
    · subst hμ
      simp [hn_pos, h_reflect_int, h_reflect_not_pos, h_reflect_not_neg]
    · simp [hn_pos, h_reflect_int, h_reflect_not_pos, h_reflect_not_neg, hμ]

#print axioms reflectToPosInterface_involution

/-- The reflection map from negative-time configurations to positive-time configurations.
This is the forward change-of-variables map `U⁻ ↦ V⁺ = reflect(U⁻)` used in step (b).
`reflectPosToNeg` is its inverse. -/
noncomputable def reflectNegToPos
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) :
    FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) :=
  restrictLinkVariable N (PeriodicSite T L) (positiveSites T L)
    (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (negativeSites T L) U_minus))

set_option maxHeartbeats 1000000 in
/-- `reflectPosToNeg` is the left-inverse of `reflectNegToPos`: reflecting a negative
config to positive and back recovers the original. This follows from `reflection_involution`
(θ² = id) and the fact that `extendLinkVariable`/`restrictLinkVariable` are inverses. -/
lemma reflectPosToNeg_reflectNegToPos (hT : Odd T)
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) :
    reflectPosToNeg N T L (reflectNegToPos N T L U_minus) = U_minus := by
  ext x
  rcases x with ⟨⟨n, μ⟩, hx⟩
  dsimp [reflectPosToNeg, reflectNegToPos, restrictLinkVariable, reflectLinkVariable,
    extendLinkVariable]
  have h_reflect_pos : ReflectSite.reflectSite n ∈ positiveSites T L :=
    reflectSite_mem_positive_of_negative hT hx
  have h_reflect_not_neg : ReflectSite.reflectSite n ∉ negativeSites T L :=
    reflectSite_not_mem_negative_of_negative hT hx
  by_cases hμ : μ = 0
  · subst hμ
    simp [hx, h_reflect_pos, h_reflect_not_neg, ReflectSite.involution, inv_inv]
  · simp [hx, h_reflect_pos, h_reflect_not_neg, hμ, ReflectSite.involution]

#print axioms reflectPosToNeg_reflectNegToPos

/-- Restricting `extendToFullConfig U_minus u` to negative sites recovers `U_minus`. -/
lemma restrictLinkVariable_negative_extendToFullConfig
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (u : PosInterfaceConfig N T L) :
    restrictLinkVariable N (PeriodicSite T L) (negativeSites T L)
      (extendToFullConfig N T L U_minus u) = U_minus := by
  ext ⟨⟨n, μ⟩, hn⟩
  simp only [restrictLinkVariable, extendToFullConfig, extendLinkVariable,
    dif_pos (Finset.mem_univ n), mergeConfigurations]
  by_cases hpos : n ∈ positiveSites T L
  · exfalso
    have hdisj : Disjoint (positiveSites T L) (negativeSites T L) := by
      unfold positiveSites negativeSites
      rw [Finset.disjoint_filter]; intro m hm hpos hneg; linarith
    exact Finset.disjoint_left.mp hdisj hpos hn
  · by_cases hneg : n ∈ negativeSites T L
    · simp [mergeConfigurations, hpos, hneg]
    · exfalso; exact hneg hn

/-- Restricting `extendToFullConfig U_minus u` to positive+interface sites recovers `u`. -/
lemma restrictPosInterface_extendToFullConfig
    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))
    (u : PosInterfaceConfig N T L) :
    restrictPosInterface N T L
      (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
        (extendToFullConfig N T L U_minus u)) = u := by
  ext ⟨⟨n, μ⟩, hmem⟩
  simp only [restrictPosInterface, restrictLinkVariable, extendToFullConfig,
    extendLinkVariable, dif_pos (Finset.mem_univ n), mergeConfigurations]
  rcases Finset.mem_union.mp hmem with hpos | hint
  · simp [mergeConfigurations, hpos]
  · by_cases hnpos : n ∈ positiveSites T L
    · exfalso
      have hdisj : Disjoint (positiveSites T L) (interfaceSites T L) := by
        unfold positiveSites interfaceSites
        rw [Finset.disjoint_filter]; intro m hm hpos hzero; linarith
      exact Finset.disjoint_left.mp hdisj hnpos hint
    · by_cases hneg : n ∈ negativeSites T L
      · exfalso
        have hdisj : Disjoint (negativeSites T L) (interfaceSites T L) := by
          unfold negativeSites interfaceSites
          rw [Finset.disjoint_filter]; intro m hm hneg hint; linarith
        exact Finset.disjoint_left.mp hdisj hneg hint
      · simp [mergeConfigurations, hnpos, hneg, hint]

/-- The positive+interface restriction of the reflected full config
`reflectLinkVariable(extendToFullConfig(reflectPosToNeg V⁺, u))` equals
`mergePosInterface V⁺ (σ(restrictToInterface u))`.

This combines `reflectToPosInterface_eq_restrict` (which relates
`reflectToPosInterface` to the restriction of `reflectLinkVariable`) with
`reflectToPosInterface_involution` (which evaluates `reflectToPosInterface`
on `reflectPosToNeg V⁺`). It is the key lemma for rewriting `S⁺` under the
change of variables in step (b). -/
lemma reflect_extendToFullConfig_posInterface (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (u : PosInterfaceConfig N T L) :
    restrictPosInterface N T L
      (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
        (reflectLinkVariable N (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u))) =
    mergePosInterface N T L V_plus (sigmaInterface N T L (restrictToInterface N T L u)) := by
  rw [← reflectToPosInterface_eq_restrict N T L hT
      (extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u)]
  rw [restrictLinkVariable_negative_extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u]
  rw [restrictPosInterface_extendToFullConfig N T L (reflectPosToNeg N T L V_plus) u]
  exact reflectToPosInterface_involution N T L hT V_plus (restrictToInterface N T L u)

#print axioms reflect_extendToFullConfig_posInterface

