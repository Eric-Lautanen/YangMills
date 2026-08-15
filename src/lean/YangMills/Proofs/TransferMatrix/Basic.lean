/-
# Transfer Matrix: Basic Definitions
-/

import YangMills.Proofs.ReflectionPositivity
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Prod

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
lemma measurable_reflectLinkVariable (N : ℕ) (T L : ℕ) [NeZero T] [NeZero L] :

    Measurable (reflectLinkVariable N : LinkVariable (SU N) (PeriodicSite T L) → LinkVariable (SU N) (PeriodicSite T L)) := by

  -- Use measurable_comap_iff to reduce to the value map:

  -- reflectLinkVariable N is measurable into the comap space iff its value map is measurable

  -- into the product space.

  refine (measurable_comap_iff (g := fun (U' : LinkVariable (SU N) (PeriodicSite T L)) => U'.value)).mpr ?_

  rw [measurable_pi_iff]

  intro n

  rw [measurable_pi_iff]

  intro μ

  simp [reflectLinkVariable]

  by_cases hμ : μ = 0

  · subst hμ

    -- Need to show Measurable (λ U => (U.value (ReflectSite.reflectSite n) 0)⁻¹)

    have h_val : Measurable (λ (U : LinkVariable (SU N) (PeriodicSite T L)) =>

      U.value (ReflectSite.reflectSite n) 0) := by

      -- The map U ↦ U.value is measurable from the comap definition

      have h_value_map : Measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value) :=

        comap_measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value)

      -- Compose with coordinate projections

      have h_at_n : Measurable (λ (f : PeriodicSite T L → Fin 4 → SU N) => f (ReflectSite.reflectSite n)) :=

        measurable_pi_apply (ReflectSite.reflectSite n)

      have h_at_n_0 : Measurable (λ (f : Fin 4 → SU N) => f 0) := measurable_pi_apply (0 : Fin 4)

      exact h_at_n_0.comp (h_at_n.comp h_value_map)

    -- Inversion is continuous, hence measurable

    have h_inv : Measurable (λ (g : SU N) => g⁻¹) := (Continuous.inv continuous_id).measurable

    exact h_inv.comp h_val

  · -- μ ≠ 0, so U.value (θ n) μ (no inverse)

    have h_val : Measurable (λ (U : LinkVariable (SU N) (PeriodicSite T L)) =>

      U.value (ReflectSite.reflectSite n) μ) := by

      have h_value_map : Measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value) :=

        comap_measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value)

      have h_at_n : Measurable (λ (f : PeriodicSite T L → Fin 4 → SU N) => f (ReflectSite.reflectSite n)) :=

        measurable_pi_apply (ReflectSite.reflectSite n)

      have h_at_n_μ : Measurable (λ (f : Fin 4 → SU N) => f μ) := measurable_pi_apply μ

      exact h_at_n_μ.comp (h_at_n.comp h_value_map)

    simpa [hμ] using h_val





/-- The set of links at positive-time sites. -/

noncomputable def positiveLinks : Finset (PeriodicSite T L × Fin 4) :=

  (positiveSites T L).product (Finset.univ : Finset (Fin 4))



/-- The set of links at negative-time sites. -/

noncomputable def negativeLinks : Finset (PeriodicSite T L × Fin 4) :=

  (negativeSites T L).product (Finset.univ : Finset (Fin 4))



/-- The set of links at interface sites. -/

noncomputable def interfaceLinks : Finset (PeriodicSite T L × Fin 4) :=

  (interfaceSites T L).product (Finset.univ : Finset (Fin 4))



lemma linkPartition_disjoint_union :

    positiveLinks T L ∪ negativeLinks T L ∪ interfaceLinks T L =

    (Finset.univ : Finset (PeriodicSite T L × Fin 4)) := by

  ext ⟨n, μ⟩; simp [positiveLinks, negativeLinks, interfaceLinks, positiveSites,

    negativeSites, interfaceSites]

  by_cases hpos : signedTime T n.time > 0

  · simp [hpos]

  · by_cases hneg : signedTime T n.time < 0

    · simp [hpos, hneg]

    · have hzero : signedTime T n.time = 0 := by

        have hle : signedTime T n.time ≤ 0 := by linarith

        have hge : signedTime T n.time ≥ 0 := by linarith

        linarith

      simp [hpos, hneg, hzero]



lemma linkPartition_disjoint :

    Disjoint (positiveLinks T L) (negativeLinks T L) ∧

    Disjoint (positiveLinks T L) (interfaceLinks T L) ∧

    Disjoint (negativeLinks T L) (interfaceLinks T L) := by

  have h_pos_neg_sites : Disjoint (positiveSites T L) (negativeSites T L) := by

    unfold positiveSites negativeSites

    rw [Finset.disjoint_filter]

    intro n hn hpos hneg

    linarith

  have h_pos_int_sites : Disjoint (positiveSites T L) (interfaceSites T L) := by

    unfold positiveSites interfaceSites

    rw [Finset.disjoint_filter]

    intro n hn hpos hzero

    linarith

  have h_neg_int_sites : Disjoint (negativeSites T L) (interfaceSites T L) := by

    unfold negativeSites interfaceSites

    rw [Finset.disjoint_filter]

    intro n hn hneg hzero

    linarith

  have h_pos_neg_links : Disjoint (positiveLinks T L) (negativeLinks T L) := by

    unfold positiveLinks negativeLinks

    simpa using (Finset.disjoint_product (s := positiveSites T L) (t := Finset.univ)

      (s' := negativeSites T L) (t' := Finset.univ)).mpr (Or.inl h_pos_neg_sites)

  have h_pos_int_links : Disjoint (positiveLinks T L) (interfaceLinks T L) := by

    unfold positiveLinks interfaceLinks

    simpa using (Finset.disjoint_product (s := positiveSites T L) (t := Finset.univ)

      (s' := interfaceSites T L) (t' := Finset.univ)).mpr (Or.inl h_pos_int_sites)

  have h_neg_int_links : Disjoint (negativeLinks T L) (interfaceLinks T L) := by

    unfold negativeLinks interfaceLinks

    simpa using (Finset.disjoint_product (s := negativeSites T L) (t := Finset.univ)

      (s' := interfaceSites T L) (t' := Finset.univ)).mpr (Or.inl h_neg_int_sites)

  exact ⟨h_pos_neg_links, h_pos_int_links, h_neg_int_links⟩



/-- The union of positive, negative, and interface sites covers all sites. -/

lemma sites_cover (T L : ℕ) [NeZero T] [NeZero L] :

    (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) = Finset.univ := by

  ext n; simp [positiveSites, negativeSites, interfaceSites]

  by_cases hpos : signedTime T n.time > 0

  · simp [hpos]

  · by_cases hneg : signedTime T n.time < 0

    · simp [hpos, hneg]

    · have hzero : signedTime T n.time = 0 := by

        have hle : signedTime T n.time ≤ 0 := by linarith

        have hge : signedTime T n.time ≥ 0 := by linarith

        linarith

      simp [hpos, hneg, hzero]



/-- Haar measure on the positive links. -/

noncomputable def haarMeasurePositive : Measure (FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :=

  productHaarMeasure N (PeriodicSite T L) (positiveSites T L)



/-- Haar measure on the negative links. -/

noncomputable def haarMeasureNegative : Measure (FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) :=

  productHaarMeasure N (PeriodicSite T L) (negativeSites T L)



/-- Haar measure on the interface links. -/

noncomputable def haarMeasureInterface : Measure (FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :=

  productHaarMeasure N (PeriodicSite T L) (interfaceSites T L)



/-- A helper equivalence: `FiniteLinkIndex Λ (s₁ ∪ s₂) ≃ FiniteLinkIndex Λ s₁ ⊕ FiniteLinkIndex Λ s₂`

for disjoint s₁, s₂. -/

noncomputable def finiteLinkIndexUnionSum {Λ : Type} [DecidableEq Λ] {s₁ s₂ : Finset Λ}

    (h : Disjoint s₁ s₂) : FiniteLinkIndex Λ (s₁ ∪ s₂) ≃ FiniteLinkIndex Λ s₁ ⊕ FiniteLinkIndex Λ s₂ where

  toFun := λ x =>

    if h₁ : x.1.1 ∈ s₁ then

      Sum.inl ⟨(x.1.1, x.1.2), h₁⟩

    else

      have h₂ : x.1.1 ∈ s₂ := by

        rcases Finset.mem_union.mp x.2 with (h₁' | h₂')

        · exact (h₁ h₁').elim

        · exact h₂'

      Sum.inr ⟨(x.1.1, x.1.2), h₂⟩

  invFun := λ y => match y with

    | Sum.inl ⟨(n, μ), hn⟩ => ⟨(n, μ), Finset.mem_union_left s₂ hn⟩

    | Sum.inr ⟨(n, μ), hn⟩ => ⟨(n, μ), Finset.mem_union_right s₁ hn⟩

  left_inv := by

    intro x

    apply Subtype.ext

    by_cases h₁ : x.1.1 ∈ s₁

    · simp [h₁]

    · have h₂ : x.1.1 ∈ s₂ := by

        rcases Finset.mem_union.mp x.2 with (h₁' | h₂')

        · exact (h₁ h₁').elim

        · exact h₂'

      simp [h₁, h₂]

  right_inv := by

    intro y

    rcases y with (⟨⟨n, μ⟩, hn⟩ | ⟨⟨n, μ⟩, hn⟩)

    · -- Sum.inl case: hn : (n, μ).1 ∈ s₁, i.e. n ∈ s₁

      simp [hn]

    · -- Sum.inr case: hn : (n, μ).1 ∈ s₂, i.e. n ∈ s₂, and s₁, s₂ are disjoint

      have hn' : n ∉ s₁ := by

        intro hn1

        have h_disj : s₁ ∩ s₂ = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h

        have mem_inter : n ∈ s₁ ∩ s₂ := Finset.mem_inter.mpr ⟨hn1, hn⟩

        rw [h_disj] at mem_inter

        simpa using mem_inter

      simp [hn']



/-- The product Haar measure on FiniteLinkConfig is Measure.pi on the FiniteLinkIndex type,

and we can move between FiniteLinkIndex and the product Finset via a bijection. -/

noncomputable def finiteLinkIndexEquiv (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :

    FiniteLinkIndex Λ sites ≃ (sites.product (Finset.univ : Finset (Fin 4))) where

  toFun := λ x =>

    let n := x.1.1; let μ := x.1.2; let hn : n ∈ sites := x.2

    ⟨(n, μ), by simp [hn, Finset.mem_product, Finset.mem_univ]⟩

  invFun := λ y =>

    let n := y.1.1; let μ := y.1.2

    have hn : n ∈ sites := by

      rcases Finset.mem_product.mp y.2 with ⟨hn, hμ⟩

      exact hn

    ⟨(n, μ), hn⟩

  left_inv := by

    intro x

    let n := x.1.1; let μ := x.1.2; let hn : n ∈ sites := x.2

    rfl

  right_inv := by

    intro y

    let n := y.1.1; let μ := y.1.2

    rcases Finset.mem_product.mp y.2 with ⟨hn, hμ⟩

    rfl



/-- The configuration space for positive and interface links together. -/

abbrev PosInterfaceConfig :=

  FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)



/-- Restriction of a full configuration to the positive and interface links. -/

noncomputable def restrictPosInterface (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :

    PosInterfaceConfig N T L :=

  λ idx => cfg ⟨(idx.1.1, idx.1.2), Finset.mem_univ (idx.1.1)⟩



/-- Merging a positive configuration and an interface configuration. -/

noncomputable def mergePosInterface

    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))

    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :

    PosInterfaceConfig N T L :=

  λ idx =>

    match idx with

    | ⟨(n, μ), hmem⟩ =>

      if h : n ∈ positiveSites T L then

        U_plus ⟨(n, μ), h⟩

      else

        have hint : n ∈ interfaceSites T L := by

          rcases Finset.mem_union.mp hmem with (hpos | hint)

          · exact (h hpos).elim

          · exact hint

        U_zero ⟨(n, μ), hint⟩

/-- The natural measurable equivalence that merges configurations on two disjoint site sets
into a configuration on their union, matching `productHaarMeasure`. -/
noncomputable def productHaarMeasureUnionEquiv {Λ : Type} [DecidableEq Λ]
    {s₁ s₂ : Finset Λ} (h : Disjoint s₁ s₂) :
    (FiniteLinkConfig N Λ s₁ × FiniteLinkConfig N Λ s₂) ≃ᵐ
    FiniteLinkConfig N Λ (s₁ ∪ s₂) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => SU N)).symm.trans <|
    (MeasurableEquiv.arrowCongr' (finiteLinkIndexUnionSum h) (MeasurableEquiv.refl (SU N))).symm

/-- `productHaarMeasureUnionEquiv` is measure-preserving: the product Haar measure on `s₁ ∪ s₂`
equals the product of the product Haar measures on `s₁` and `s₂`. -/
lemma measurePreserving_productHaarMeasureUnion {Λ : Type} [DecidableEq Λ]
    {s₁ s₂ : Finset Λ} (h : Disjoint s₁ s₂) :
    MeasurePreserving (productHaarMeasureUnionEquiv N h)
      ((productHaarMeasure N Λ s₁).prod (productHaarMeasure N Λ s₂))
      (productHaarMeasure N Λ (s₁ ∪ s₂)) := by
  unfold productHaarMeasure productHaarMeasureUnionEquiv
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  let haar := Measure.haarMeasure K
  have h1 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ => SU N)).symm
      ((Measure.pi (fun _ : FiniteLinkIndex Λ s₁ => haar)).prod
       (Measure.pi (fun _ : FiniteLinkIndex Λ s₂ => haar)))
      (Measure.pi (fun _ : FiniteLinkIndex Λ s₁ ⊕ FiniteLinkIndex Λ s₂ => haar)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => haar)
  have h2 : MeasurePreserving
      (MeasurableEquiv.arrowCongr' (finiteLinkIndexUnionSum h) (MeasurableEquiv.refl (SU N)))
      (Measure.pi (fun _ : FiniteLinkIndex Λ (s₁ ∪ s₂) => haar))
      (Measure.pi (fun _ : FiniteLinkIndex Λ s₁ ⊕ FiniteLinkIndex Λ s₂ => haar)) :=
    measurePreserving_arrowCongr' (fun _ => haar) (fun _ => haar)
      (finiteLinkIndexUnionSum h) (MeasurableEquiv.refl (SU N))
      (fun _ => MeasurePreserving.id haar)
  exact h1.trans h2.symm

/-- The action of `productHaarMeasureUnionEquiv`: it splits a configuration on `s₁ ∪ s₂`
into the two components according to which set the site lies in. -/
lemma productHaarMeasureUnionEquiv_apply {Λ : Type} [DecidableEq Λ] {s₁ s₂ : Finset Λ}
    (h : Disjoint s₁ s₂) (cfg₁ : FiniteLinkConfig N Λ s₁) (cfg₂ : FiniteLinkConfig N Λ s₂)
    (idx : FiniteLinkIndex Λ (s₁ ∪ s₂)) :
    productHaarMeasureUnionEquiv N h (cfg₁, cfg₂) idx =
      if h₁ : idx.1.1 ∈ s₁ then cfg₁ ⟨idx.1, h₁⟩
      else cfg₂ ⟨idx.1, by
        rcases Finset.mem_union.mp idx.2 with h | h
        · exact absurd h h₁
        · exact h⟩ := by
  unfold productHaarMeasureUnionEquiv
  simp only [MeasurableEquiv.coe_trans, Function.comp_apply]
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  rw [show (MeasurableEquiv.arrowCongr' (finiteLinkIndexUnionSum h)
        (MeasurableEquiv.refl (SU N))).symm
        ((Equiv.sumPiEquivProdPi fun _ => SU N).symm (cfg₁, cfg₂)) idx =
      (Equiv.sumPiEquivProdPi fun _ => SU N).symm (cfg₁, cfg₂) (finiteLinkIndexUnionSum h idx)
      from rfl]
  simp only [Equiv.sumPiEquivProdPi_symm_apply]
  unfold finiteLinkIndexUnionSum
  simp only [Equiv.coe_fn_mk]
  by_cases hmem : idx.1.1 ∈ s₁
  · rw [dif_pos hmem, dif_pos hmem]
  · rw [dif_neg hmem, dif_neg hmem]

lemma measure_factorization' :

    ∃ (e : (FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×

            FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×

            FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) ≃ᵐ

           FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),

    ((MeasurePreserving e

      ((haarMeasurePositive N T L).prod ((haarMeasureNegative N T L).prod (haarMeasureInterface N T L)))

      (productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) ∧

    (∀ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×

            FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×

            FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),

      restrictPosInterface N T L (e x) = mergePosInterface N T L x.1 x.2.2)) ∧

    (∀ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×

            FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×

            FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))

      (idx : FiniteLinkIndex (PeriodicSite T L) (negativeSites T L)),

      (e x) ⟨(idx.1.1, idx.1.2), Finset.mem_univ idx.1.1⟩ = x.2.1 idx)) := by

  -- Site disjointness (proved directly, since linkPartition_disjoint gives link disjointness)
  have hpn : Disjoint (positiveSites T L) (negativeSites T L) := by
    unfold positiveSites negativeSites
    rw [Finset.disjoint_filter]; intro n hn hpos hneg; linarith
  have hpi : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
  have hni : Disjoint (negativeSites T L) (interfaceSites T L) := by
    unfold negativeSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hneg hzero; linarith
  have hcover : (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) = Finset.univ :=
    sites_cover T L
  have hint_of {n : PeriodicSite T L} (hpos : n ∉ positiveSites T L) (hneg : n ∉ negativeSites T L)
      (hn : n ∈ Finset.univ) : n ∈ interfaceSites T L := by
    have h_mem : n ∈ (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) := by
      rw [hcover]; exact hn
    rcases Finset.mem_union.mp h_mem with (h | h)
    · rcases Finset.mem_union.mp h with (h' | h')
      · exact absurd h' hpos
      · exact absurd h' hneg
    · exact h
  -- The merge function (defined directly, not via mergeConfigurations which is defined later)
  let eFun (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
            (FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×
             FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))) :
      FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) :=
    fun idx =>
      if hpos : idx.1.1 ∈ positiveSites T L then x.1 ⟨idx.1, hpos⟩
      else if hneg : idx.1.1 ∈ negativeSites T L then x.2.1 ⟨idx.1, hneg⟩
      else x.2.2 ⟨idx.1, hint_of hpos hneg idx.2⟩
  -- The split function (inverse)
  let eInv (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :
      FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
      (FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×
       FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :=
    (fun i => cfg ⟨i.1, Finset.mem_univ _⟩,
     (fun i => cfg ⟨i.1, Finset.mem_univ _⟩,
      fun i => cfg ⟨i.1, Finset.mem_univ _⟩))
  -- Bijectivity
  have h_left : ∀ x, eInv (eFun x) = x := by
    intro x
    ext1
    · ext i_pos
      simp only [eInv, eFun]
      have hpos : (Subtype.val i_pos).1 ∈ positiveSites T L := i_pos.2
      rw [dif_pos hpos]
      rfl
    · ext1
      · ext i_neg
        simp only [eInv, eFun]
        have hnpos : (Subtype.val i_neg).1 ∉ positiveSites T L := by
          intro h
          exact Finset.disjoint_left.mp hpn h i_neg.2
        have hneg : (Subtype.val i_neg).1 ∈ negativeSites T L := i_neg.2
        rw [dif_neg hnpos, dif_pos hneg]
        rfl
      · ext i_int
        simp only [eInv, eFun]
        have hnpos : (Subtype.val i_int).1 ∉ positiveSites T L := by
          intro h
          exact Finset.disjoint_left.mp hpi h i_int.2
        have hnneg : (Subtype.val i_int).1 ∉ negativeSites T L := by
          intro h
          exact Finset.disjoint_left.mp hni h i_int.2
        rw [dif_neg hnpos, dif_neg hnneg]
        rfl
  have h_right : ∀ cfg, eFun (eInv cfg) = cfg := by
    intro cfg
    ext idx
    simp only [eInv, eFun]
    by_cases hpos : idx.1.1 ∈ positiveSites T L
    · rw [dif_pos hpos]; rfl
    · by_cases hneg : idx.1.1 ∈ negativeSites T L
      · rw [dif_neg hpos, dif_pos hneg]; rfl
      · rw [dif_neg hpos, dif_neg hneg]; rfl
  -- Measurability of eFun
  have h_meas_to : Measurable eFun := by
    rw [measurable_pi_iff]
    intro idx
    by_cases hpos : idx.1.1 ∈ positiveSites T L
    · have heq : (fun x => eFun x idx) = fun x => x.1 ⟨idx.1, hpos⟩ := by
        ext x; simp [eFun, hpos]
      rw [heq]
      exact (measurable_pi_apply
        (⟨idx.1, hpos⟩ : FiniteLinkIndex (PeriodicSite T L) (positiveSites T L))).comp
        measurable_fst
    · by_cases hneg : idx.1.1 ∈ negativeSites T L
      · have heq : (fun x => eFun x idx) = fun x => x.2.1 ⟨idx.1, hneg⟩ := by
          ext x; simp [eFun, hpos, hneg]
        rw [heq]
        exact (measurable_pi_apply
          (⟨idx.1, hneg⟩ : FiniteLinkIndex (PeriodicSite T L) (negativeSites T L))).comp
          (measurable_fst.comp measurable_snd)
      · have hint := hint_of hpos hneg idx.2
        have heq : (fun x => eFun x idx) = fun x => x.2.2 ⟨idx.1, hint⟩ := by
          ext x; simp [eFun, hpos, hneg, hint]
        rw [heq]
        exact (measurable_pi_apply
          (⟨idx.1, hint⟩ : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L))).comp
          (measurable_snd.comp measurable_snd)
  -- Measurability of eInv
  have h_meas_inv : Measurable eInv := by
    have h1 : Measurable (fun cfg => (eInv cfg).1) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply
        (⟨i.1, Finset.mem_univ _⟩ : FiniteLinkIndex (PeriodicSite T L) (Finset.univ))
    have h2 : Measurable (fun cfg => (eInv cfg).2.1) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply
        (⟨i.1, Finset.mem_univ _⟩ : FiniteLinkIndex (PeriodicSite T L) (Finset.univ))
    have h3 : Measurable (fun cfg => (eInv cfg).2.2) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply
        (⟨i.1, Finset.mem_univ _⟩ : FiniteLinkIndex (PeriodicSite T L) (Finset.univ))
    exact Measurable.prodMk h1 (Measurable.prodMk h2 h3)
  -- The MeasurableEquiv
  let he : (FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
            (FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×
             FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))) ≃ᵐ
           (FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :=
    MeasurableEquiv.mk
      (Equiv.mk eFun eInv h_left h_right) h_meas_to h_meas_inv
  refine ⟨he, ?_⟩
  refine And.intro (And.intro ?_ ?_) ?_
  · -- MeasurePreserving condition
    have hpos_negint : Disjoint (positiveSites T L)
        (negativeSites T L ∪ interfaceSites T L) := by
      rw [Finset.disjoint_left]
      intro n hn hmem
      rcases Finset.mem_union.mp hmem with (hneg | hint)
      · exact (Finset.disjoint_left.mp hpn hn) hneg
      · exact (Finset.disjoint_left.mp hpi hn) hint
    have h_cover : positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L) =
        (Finset.univ : Finset (PeriodicSite T L)) := by
      rw [← Finset.union_assoc, hcover]
    let castIdx : FiniteLinkIndex (PeriodicSite T L)
        (positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L)) ≃
        FiniteLinkIndex (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) :=
      Equiv.subtypeEquivRight (fun p => by rw [h_cover])
    let castEquiv : FiniteLinkConfig N (PeriodicSite T L)
        (positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L)) ≃ᵐ
        FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) :=
      MeasurableEquiv.arrowCongr' castIdx (MeasurableEquiv.refl (SU N))
    let eFull := (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (productHaarMeasureUnionEquiv N hni)).trans
        (productHaarMeasureUnionEquiv N hpos_negint)
    let eFullUniv := eFull.trans castEquiv
    haveI hfinPos : IsFiniteMeasure
        (productHaarMeasure N (PeriodicSite T L) (positiveSites T L)) :=
      productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (positiveSites T L)
    haveI hfinNeg : IsFiniteMeasure
        (productHaarMeasure N (PeriodicSite T L) (negativeSites T L)) :=
      productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (negativeSites T L)
    haveI hfinInt : IsFiniteMeasure
        (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L)) :=
      productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (interfaceSites T L)
    have h_mp_negint : MeasurePreserving (productHaarMeasureUnionEquiv N hni)
        ((productHaarMeasure N (PeriodicSite T L) (negativeSites T L)).prod
         (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L)))
        (productHaarMeasure N (PeriodicSite T L)
          (negativeSites T L ∪ interfaceSites T L)) :=
      measurePreserving_productHaarMeasureUnion N hni
    have h_mp_posnegint : MeasurePreserving (productHaarMeasureUnionEquiv N hpos_negint)
        ((productHaarMeasure N (PeriodicSite T L) (positiveSites T L)).prod
         (productHaarMeasure N (PeriodicSite T L)
           (negativeSites T L ∪ interfaceSites T L)))
        (productHaarMeasure N (PeriodicSite T L)
          (positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L))) :=
      measurePreserving_productHaarMeasureUnion N hpos_negint
    have h_mp_prod : MeasurePreserving
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
          (productHaarMeasureUnionEquiv N hni))
        ((productHaarMeasure N (PeriodicSite T L) (positiveSites T L)).prod
         ((productHaarMeasure N (PeriodicSite T L) (negativeSites T L)).prod
          (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L))))
        ((productHaarMeasure N (PeriodicSite T L) (positiveSites T L)).prod
         (productHaarMeasure N (PeriodicSite T L)
           (negativeSites T L ∪ interfaceSites T L))) :=
      MeasurePreserving.prod (MeasurePreserving.id _) h_mp_negint
    have h_mp_full : MeasurePreserving eFull
        ((productHaarMeasure N (PeriodicSite T L) (positiveSites T L)).prod
         ((productHaarMeasure N (PeriodicSite T L) (negativeSites T L)).prod
          (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L))))
        (productHaarMeasure N (PeriodicSite T L)
          (positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L))) :=
      h_mp_prod.trans h_mp_posnegint
    have h_mp_cast : MeasurePreserving castEquiv
        (productHaarMeasure N (PeriodicSite T L)
          (positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L)))
        (productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) := by
      unfold productHaarMeasure
      let K : TopologicalSpace.PositiveCompacts (SU N) :=
        ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
      let haar := Measure.haarMeasure K
      exact measurePreserving_arrowCongr' (fun _ => haar) (fun _ => haar)
        castIdx (MeasurableEquiv.refl (SU N)) (fun _ => MeasurePreserving.id haar)
    have h_mp_full_univ : MeasurePreserving eFullUniv
        ((productHaarMeasure N (PeriodicSite T L) (positiveSites T L)).prod
         ((productHaarMeasure N (PeriodicSite T L) (negativeSites T L)).prod
          (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L))))
        (productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :=
      h_mp_full.trans h_mp_cast
    have h_eq : (he : _ → _) = (eFullUniv : _ → _) := by
      ext x idx
      simp only [he, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, eFun]
      rw [show (eFullUniv x idx) = (eFull x) (castIdx.symm idx) from rfl]
      rw [show (eFull x (castIdx.symm idx)) =
          productHaarMeasureUnionEquiv N hpos_negint
            (x.1, productHaarMeasureUnionEquiv N hni (x.2.1, x.2.2)) (castIdx.symm idx) from rfl]
      have h_mem : idx.1.1 ∈ positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L) :=
        ((fun (p : PeriodicSite T L × Fin 4) =>
            (by rw [h_cover] :
              p.1 ∈ positiveSites T L ∪ (negativeSites T L ∪ interfaceSites T L) ↔ p.1 ∈ Finset.univ))
            idx.1).mpr idx.2
      have h_cast : castIdx.symm idx = ⟨idx.1, h_mem⟩ := rfl
      rw [h_cast]
      rw [productHaarMeasureUnionEquiv_apply N hpos_negint x.1
            ((productHaarMeasureUnionEquiv N hni) (x.2.1, x.2.2)) ⟨idx.1, h_mem⟩]
      by_cases hpos : idx.1.1 ∈ positiveSites T L
      · rw [dif_pos hpos, dif_pos hpos]
      · rw [dif_neg hpos, dif_neg hpos]
        have h_neg_or_int : idx.1.1 ∈ negativeSites T L ∪ interfaceSites T L := by
          rcases Finset.mem_union.mp h_mem with h | h
          · exact absurd h hpos
          · exact h
        have h_apply : productHaarMeasureUnionEquiv N hni (x.2.1, x.2.2) ⟨idx.1, h_neg_or_int⟩ =
            if h₁ : idx.1.1 ∈ negativeSites T L then x.2.1 ⟨idx.1, h₁⟩
            else x.2.2 ⟨idx.1, by
              rcases Finset.mem_union.mp h_neg_or_int with h | h
              · exact absurd h h₁
              · exact h⟩ :=
          productHaarMeasureUnionEquiv_apply N hni x.2.1 x.2.2 ⟨idx.1, h_neg_or_int⟩
        simp only [h_apply]
    rw [h_eq]
    exact h_mp_full_univ
  · -- restrictPosInterface condition
    intro x
    ext idx
    rcases idx with ⟨⟨n, μ⟩, hmem⟩
    by_cases hpos : n ∈ positiveSites T L
    · -- positive case: both sides give x.1 ⟨(n, μ), hpos⟩
      simp [restrictPosInterface, he, eFun, mergePosInterface, hpos]
    · -- non-positive case: both sides give x.2.2 ⟨(n, μ), hint⟩
      have hnpos : n ∉ negativeSites T L := by
        intro h
        rcases Finset.mem_union.mp hmem with (hpos' | hint)
        · exact absurd hpos' hpos
        · exact Finset.disjoint_left.mp hni h hint
      have hint : n ∈ interfaceSites T L := by
        rcases Finset.mem_union.mp hmem with (hpos' | hint')
        · exact absurd hpos' hpos
        · exact hint'
      simp [restrictPosInterface, he, eFun, mergePosInterface, hpos, hnpos, hint]
  · -- negative projection condition
    intro x idx
    have hnpos : idx.1.1 ∉ positiveSites T L :=
      fun h => Finset.disjoint_left.mp hpn h idx.2
    simp only [he, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, eFun]
    rw [dif_neg hnpos, dif_pos idx.2]
    rfl

/-- The product Haar measure on the positive+interface configuration space. -/

noncomputable def haarMeasurePosInterface : Measure (PosInterfaceConfig N T L) :=

  Measure.map (Function.uncurry (mergePosInterface N T L))

    ((haarMeasurePositive N T L).prod (haarMeasureInterface N T L))



lemma haarMeasurePosInterface_eq :

    haarMeasurePosInterface N T L =

    Measure.map (Function.uncurry (mergePosInterface N T L))

      ((haarMeasurePositive N T L).prod (haarMeasureInterface N T L)) := rfl



/-- Merge a negative and a positive+interface configuration into a full config. -/

noncomputable def mergeConfigurations

    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))

    (U_plus_zero : PosInterfaceConfig N T L) :

    FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) :=

  λ idx =>

    match idx with

    | ⟨(n, μ), hn⟩ =>

      if hpos : n ∈ positiveSites T L then

        U_plus_zero ⟨(n, μ), Finset.mem_union_left (interfaceSites T L) hpos⟩

      else if hneg : n ∈ negativeSites T L then

        U_minus ⟨(n, μ), hneg⟩

      else

        have hint : n ∈ interfaceSites T L := by

          have h_cover : (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) = Finset.univ := by

            ext n'; simp [positiveSites, negativeSites, interfaceSites]

            by_cases hpos' : signedTime T n'.time > 0

            · simp [hpos']

            · by_cases hneg' : signedTime T n'.time < 0

              · simp [hpos', hneg']

              · have hzero' : signedTime T n'.time = 0 := by

                  have hle' : signedTime T n'.time ≤ 0 := by linarith

                  have hge' : signedTime T n'.time ≥ 0 := by linarith

                  linarith

                simp [hpos', hneg', hzero']

          have hn_univ : n ∈ Finset.univ := hn

          have h_mem : n ∈ (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) := by

            rw [h_cover]; exact hn_univ

          rcases Finset.mem_union.mp h_mem with (h | h)

          · rcases Finset.mem_union.mp h with (h' | h')

            · exfalso; exact hpos h'

            · exfalso; exact hneg h'

          · exact h

        U_plus_zero ⟨(n, μ), Finset.mem_union_right (positiveSites T L) hint⟩



/-- Extend a configuration to a full link variable. -/

noncomputable def extendToFullConfig

    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))

    (U_plus_zero : PosInterfaceConfig N T L) :

    LinkVariable (SU N) (PeriodicSite T L) :=

  extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))

    (mergeConfigurations N T L U_minus U_plus_zero)



/--

  Restrict a full `LinkVariable` to a `FiniteLinkConfig` on a subset of sites.

-/

noncomputable def linkVariableRestrict (Λ : Type) [DecidableEq Λ] (sites : Finset Λ)

    (U : LinkVariable (SU N) Λ) : FiniteLinkConfig N Λ sites :=

  λ ⟨(n, μ), hn⟩ => U.value n μ



/--

  The identity configuration on the positive+interface region (all links = 1).

-/

noncomputable def onePosInterface : PosInterfaceConfig N T L := λ _ => 1



/--

  The reflection map θ⁻⁰ from negative+interface configurations to

  positive+interface configurations.



  Given (U⁻, U⁰), we construct a full configuration where positive links are

  set to 1, U⁻ on negative links, and U⁰ on interface links.  Then we apply

  the full geometric reflection θ and restrict the result to the

  positive+interface region.  Since θ maps negative links to positive links

  and interface links to themselves, the result depends only on U⁻ and U⁰.

-/

noncomputable def reflectToPosInterface

    (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L))

    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :

    PosInterfaceConfig N T L :=

  -- Combine identity on positive links with U_zero on interface links

  let U_plus_zero_zeroed : PosInterfaceConfig N T L :=

    λ idx =>

      match idx with

      | ⟨(n, μ), hmem⟩ =>

        if hpos : n ∈ positiveSites T L then 1

        else

          have hint : n ∈ interfaceSites T L := by

            rcases Finset.mem_union.mp hmem with (hpos' | hint')

            · exact (hpos hpos').elim

            · exact hint'

          U_zero ⟨(n, μ), hint⟩

  -- Merge with U_minus to get a full config, then reflect and restrict

  let full_cfg := mergeConfigurations N T L U_minus U_plus_zero_zeroed

  let full_link := extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) full_cfg

  let reflected_link := reflectLinkVariable N full_link

  linkVariableRestrict N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) reflected_link



/--

  Restrict a PosInterfaceConfig to the interface links only.

-/

noncomputable def restrictToInterface (u : PosInterfaceConfig N T L) :

    FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L) :=

  λ ⟨(n, μ), hn⟩ => u ⟨(n, μ), Finset.mem_union_right (positiveSites T L) hn⟩



/--

  Restrict a PosInterfaceConfig to the positive links only.

-/

noncomputable def restrictToPositive (u : PosInterfaceConfig N T L) :

    FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) :=

  λ ⟨(n, μ), hn⟩ => u ⟨(n, μ), Finset.mem_union_left (interfaceSites T L) hn⟩



/-- A `PosInterfaceConfig` decomposes as the merge of its positive and interface
restrictions: `u = mergePosInterface (restrictToPositive u) (restrictToInterface u)`.
This is the key decomposition needed to apply the bridge lemmas
`interfaceLinkVar_extendToFullConfig_pos/int/neg` in step 4d (measure factorization).
0 sorries, 0 custom axioms. -/
lemma mergePosInterface_restrictToPositive_restrictToInterface
    (u : PosInterfaceConfig N T L) :
    mergePosInterface N T L (restrictToPositive N T L u) (restrictToInterface N T L u) = u := by
  funext ⟨(n, μ), hmem⟩
  simp only [mergePosInterface, restrictToPositive, restrictToInterface]
  split_ifs <;> rfl

#print axioms mergePosInterface_restrictToPositive_restrictToInterface

/-- Restricting a merged config `mergePosInterface U⁺ u⁰` to the positive links recovers `U⁺`.
This is the "restrict-after-merge" identity for the positive part, needed in step 4d to identify
the `Φ_w` factor (which depends only on `U⁺`) after the measure factorization splits
`u = mergePosInterface U⁺ u⁰`. 0 sorries, 0 custom axioms. -/
lemma restrictToPositive_mergePosInterface (N T L : ℕ) [NeZero T] [NeZero L]
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    restrictToPositive N T L (mergePosInterface N T L U_plus U_zero) = U_plus := by
  funext ⟨(n, μ), hpos⟩
  simp only [restrictToPositive, mergePosInterface]
  split_ifs with h
  · rfl
  · exact absurd hpos h

#print axioms restrictToPositive_mergePosInterface

/-- Restricting a merged config `mergePosInterface U⁺ u⁰` to the interface links recovers `u⁰`.
This is the "restrict-after-merge" identity for the interface part, needed in step 4d to identify
the `Ψ_w` factor (which depends only on `u⁰`). 0 sorries, 0 custom axioms. -/
lemma restrictToInterface_mergePosInterface (N T L : ℕ) [NeZero T] [NeZero L]
    (U_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    restrictToInterface N T L (mergePosInterface N T L U_plus U_zero) = U_zero := by
  funext ⟨(n, μ), hint⟩
  have hdisj : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
  simp only [restrictToInterface, mergePosInterface]
  split_ifs with h
  · exact (Finset.disjoint_left.mp hdisj h hint).elim
  · rfl

#print axioms restrictToInterface_mergePosInterface



/--

  Compute S_OS⁺(U⁺,U⁰) from a positive+interface configuration.

  Since S_OS⁺ only involves positive-time plaquettes (all four corners > 0),

  it depends only on the positive+interface part of the configuration.

  The value does not depend on how negative links are set.

-/

noncomputable def osPositiveOfPosInterface (u : PosInterfaceConfig N T L) : ℝ :=

  let full_link := extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u

  wilsonActionOSPositive N T L β full_link



/--

  The correct transfer matrix T acting on functions ψ : PosInterfaceConfig → ℝ.



  (T ψ)(u) = ∫ ψ(θ⁻⁰(U⁻, u⁰))

              · exp(-β·(S_OS⁺(u)/2 + S_OS⁻(U⁻)/2 + S_OS_int(u, U⁻)))

              dμ⁻(U⁻)



  where u = (U⁺, U⁰) and the integral kernel is chosen so that the key identity holds:



    g(u)·(T g)(u) = ∫ G(U)·G(θU) dμ⁻(U⁻)



  with g(u) = f(u)·exp(-β·S_OS⁺(u)/2).

-/

noncomputable def transferMatrixCorrect (ψ : PosInterfaceConfig N T L → ℝ)

    (u : PosInterfaceConfig N T L) : ℝ :=

  let S_plus := osPositiveOfPosInterface N T L β u

  ∫ (U_minus : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),

    ψ (reflectToPosInterface N T L U_minus (restrictToInterface N T L u)) *

    Real.exp (-β * (S_plus / 2 +

                    wilsonActionOSNegative N T L β (extendToFullConfig N T L U_minus u) / 2 +

                    wilsonActionOSInterface N T L β (extendToFullConfig N T L U_minus u)))

    ∂ haarMeasureNegative N T L

/-- The function G(U) = f(U)·exp(-β·S_OS⁺(U))·exp(-β·S_OS_int(U)/2)



  This is the key building block for the Osterwalder-Seiler reflection positivity proof.

  For a function f depending only on positive+interface links, G(U)·G(θU) factors through

  the transfer matrix. -/

noncomputable def G (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)

    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=

  f U * Real.exp (-β * wilsonActionOSPositive N T L β U) *

    Real.exp (-β * wilsonActionOSInterface N T L β U / 2)



/-- The function g(u) = f(u)·exp(-β·S_OS⁺(u)/2) for u ∈ PosInterfaceConfig.



  This is the positive+interface reduction of G.  The extra factor of 1/2 in the

  exponential (compared to G) ensures that G(U)·G(θU) factorizes as

  g(U⁺,U⁰)·g(θ⁻⁰(U⁻,U⁰))·exp(-β·(S_OS⁻(U⁻)+S_OS_int(U))/2). -/

noncomputable def g_posInterface (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)

    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)

    (u : PosInterfaceConfig N T L) : ℝ :=

  f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u) *

    Real.exp (-β * osPositiveOfPosInterface N T L β u / 2)



/-- For a full config cfg, merging its restrictions to negative and pos+interface recovers cfg. -/

lemma mergeConfigurations_restore (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :

    mergeConfigurations N T L

      (λ ⟨(n, μ), hn⟩ => cfg ⟨(n, μ), Finset.mem_univ n⟩)

      (restrictPosInterface N T L cfg) = cfg := by

  ext x

  rcases x with ⟨⟨n, μ⟩, hn⟩

  dsimp [mergeConfigurations, restrictPosInterface]

  by_cases hpos : n ∈ positiveSites T L

  · simp [hpos]

  · by_cases hneg : n ∈ negativeSites T L

    · simp [hpos, hneg]

    · have hint : n ∈ interfaceSites T L := by

        have h_cover : (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) = Finset.univ := by

          ext n'; simp [positiveSites, negativeSites, interfaceSites]

          by_cases hpos' : signedTime T n'.time > 0

          · simp [hpos']

          · by_cases hneg' : signedTime T n'.time < 0

            · simp [hpos', hneg']

            · have hzero' : signedTime T n'.time = 0 := by

                have hle' : signedTime T n'.time ≤ 0 := by linarith

                have hge' : signedTime T n'.time ≥ 0 := by linarith

                linarith

              simp [hpos', hneg', hzero']

        have hn_univ : n ∈ Finset.univ := hn

        have h_mem : n ∈ (positiveSites T L) ∪ (negativeSites T L) ∪ (interfaceSites T L) := by

          rw [h_cover]; exact hn_univ

        rcases Finset.mem_union.mp h_mem with (h | h)

        · rcases Finset.mem_union.mp h with (h' | h')

          · exfalso; exact hpos h'

          · exfalso; exact hneg h'

        · exact h

      simp [hpos, hneg, hint]



/-- For a full config cfg, the extended link variable equals extendToFullConfig of its pieces. -/

lemma extend_eq_extendToFullConfig (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) :

    extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg =

    extendToFullConfig N T L

      (λ ⟨(n, μ), hn⟩ => cfg ⟨(n, μ), Finset.mem_univ n⟩)

      (restrictPosInterface N T L cfg) := by

  dsimp [extendToFullConfig]

  rw [mergeConfigurations_restore N T L cfg]



/-- If V and W agree on all pos+interface link variables, then S_OS⁺(V) = S_OS⁺(W). -/

lemma wilsonActionOSPositive_dependsOnlyOnPosInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]

    (V W : LinkVariable (SU N) (PeriodicSite T L))

    (h : ∀ (n : PeriodicSite T L) (μ : Fin 4), n ∈ (positiveSites T L ∪ interfaceSites T L) → V.value n μ = W.value n μ) :

    wilsonActionOSPositive N T L β V = wilsonActionOSPositive N T L β W := by

  unfold wilsonActionOSPositive

  refine Finset.sum_congr rfl (λ n hn => ?_)

  refine Finset.sum_congr rfl (λ μ hμ => ?_)

  refine Finset.sum_congr rfl (λ ν hν => ?_)

  by_cases hpos : signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧

    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧

    signedTime T (addVectorPeriodic T L n ν).time > 0

  · -- All four corners have positive time, so they are in positiveSites ∪ interfaceSites

    have hpos_n : signedTime T n.time > 0 := hpos.1

    have hpos_nμ : signedTime T (addVectorPeriodic T L n μ).time > 0 := hpos.2.1

    have hpos_nμν : signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 := hpos.2.2.1

    have hpos_nν : signedTime T (addVectorPeriodic T L n ν).time > 0 := hpos.2.2.2

    have mem_union (x : PeriodicSite T L) (hx : signedTime T x.time > 0) : x ∈ positiveSites T L ∪ interfaceSites T L := by

      have hx_pos : x ∈ positiveSites T L := by

        dsimp [positiveSites]

        simp [hx]

      exact Finset.mem_union_left _ hx_pos

    have hVW1 : V.value n μ = W.value n μ := h n μ (mem_union n hpos_n)

    have hVW2 : V.value (addVectorPeriodic T L n μ) ν = W.value (addVectorPeriodic T L n μ) ν :=

      h (addVectorPeriodic T L n μ) ν (mem_union (addVectorPeriodic T L n μ) hpos_nμ)

    have hVW3 : V.value (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν) μ = W.value (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν) μ :=

      h (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν) μ (mem_union (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν) hpos_nμν)

    have hVW4 : V.value (addVectorPeriodic T L n ν) ν = W.value (addVectorPeriodic T L n ν) ν :=

      h (addVectorPeriodic T L n ν) ν (mem_union (addVectorPeriodic T L n ν) hpos_nν)

    have h_pp_eq : plaquetteProduct N V n μ ν = plaquetteProduct N W n μ ν := by

      dsimp [plaquetteProduct, AddVector.addVector]

      simp [hVW1, hVW2, hVW3, hVW4]

    simp [hpos_n, hpos_nμ, hpos_nμν, hpos_nν, h_pp_eq, plaquetteContribution]

  · simp [hpos]



/-- Restriction to pos+interface, then extension back, gives a link variable that agrees with

  the original on pos+interface links. -/

lemma extend_of_restrictPosInterface_agrees (U : LinkVariable (SU N) (PeriodicSite T L)) :

    ∀ (n : PeriodicSite T L) (μ : Fin 4),

      n ∈ (positiveSites T L ∪ interfaceSites T L) →

      (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)

        (restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U))

      ).value n μ = U.value n μ := by

  intro n μ hn

  dsimp [extendLinkVariable, restrictPosInterface, restrictLinkVariable]

  simp [hn]

lemma G_thetaG_factorization_clean (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)

    (U : LinkVariable (SU N) (PeriodicSite T L)) :

    G N T L hT β f U * G N T L hT β f (reflectLinkVariable N U) =

    (f U * Real.exp (-β * wilsonActionOSPositive N T L β U / 2)) *

    (f (reflectLinkVariable N U) * Real.exp (-β * wilsonActionOSNegative N T L β U / 2)) *

    Real.exp (-β * (wilsonActionOSPositive N T L β U / 2 + wilsonActionOSNegative N T L β U / 2 +

                    wilsonActionOSInterface N T L β U)) := by

  unfold G

  have h_pos_reflect : wilsonActionOSPositive N T L β (reflectLinkVariable N U) = wilsonActionOSNegative N T L β U :=

    (neg_action_reflection_os_periodic N T L β hT U).symm

  have h_int_reflect : wilsonActionOSInterface N T L β (reflectLinkVariable N U) = wilsonActionOSInterface N T L β U :=

    interface_action_reflection_symmetric_os_periodic N T L β hT U

  calc

    (f U * Real.exp (-β * wilsonActionOSPositive N T L β U) * Real.exp (-β * wilsonActionOSInterface N T L β U / 2)) *

    (f (reflectLinkVariable N U) * Real.exp (-β * wilsonActionOSPositive N T L β (reflectLinkVariable N U)) *

      Real.exp (-β * wilsonActionOSInterface N T L β (reflectLinkVariable N U) / 2))

        = (f U * f (reflectLinkVariable N U)) *

          (Real.exp (-β * wilsonActionOSPositive N T L β U) * Real.exp (-β * wilsonActionOSPositive N T L β (reflectLinkVariable N U))) *

          (Real.exp (-β * wilsonActionOSInterface N T L β U / 2) * Real.exp (-β * wilsonActionOSInterface N T L β (reflectLinkVariable N U) / 2)) := by

      simp [mul_assoc, mul_comm, mul_left_comm]

    _ = (f U * f (reflectLinkVariable N U)) *

        (Real.exp (-β * wilsonActionOSPositive N T L β U) * Real.exp (-β * wilsonActionOSNegative N T L β U)) *

        (Real.exp (-β * wilsonActionOSInterface N T L β U / 2) * Real.exp (-β * wilsonActionOSInterface N T L β U / 2)) := by

      rw [h_pos_reflect, h_int_reflect]

    _ = (f U * f (reflectLinkVariable N U)) *

        Real.exp (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U + wilsonActionOSInterface N T L β U)) := by

      have h_exp_add : Real.exp (-β * wilsonActionOSPositive N T L β U) * Real.exp (-β * wilsonActionOSNegative N T L β U) =

          Real.exp (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U)) := by

        rw [← Real.exp_add]

        ring

      have h_exp_double : Real.exp (-β * wilsonActionOSInterface N T L β U / 2) * Real.exp (-β * wilsonActionOSInterface N T L β U / 2) =

          Real.exp (-β * wilsonActionOSInterface N T L β U) := by

        calc

          Real.exp (-β * wilsonActionOSInterface N T L β U / 2) * Real.exp (-β * wilsonActionOSInterface N T L β U / 2)

              = Real.exp ((-β * wilsonActionOSInterface N T L β U / 2) + (-β * wilsonActionOSInterface N T L β U / 2)) := by

            rw [← Real.exp_add]

          _ = Real.exp (-β * wilsonActionOSInterface N T L β U) := by ring

      rw [h_exp_add, h_exp_double]

      calc

        (f U * f (reflectLinkVariable N U)) * Real.exp (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U)) *

            Real.exp (-β * wilsonActionOSInterface N T L β U)

            = (f U * f (reflectLinkVariable N U)) * (Real.exp (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U)) *

                Real.exp (-β * wilsonActionOSInterface N T L β U)) := by ring

        _ = (f U * f (reflectLinkVariable N U)) * Real.exp (-β * (wilsonActionOSPositive N T L β U + wilsonActionOSNegative N T L β U +

            wilsonActionOSInterface N T L β U)) := by

          rw [← Real.exp_add]

          ring

    _ = (f U * f (reflectLinkVariable N U)) *

        Real.exp (-β * (wilsonActionOSPositive N T L β U / 2 + wilsonActionOSNegative N T L β U / 2 +

                        wilsonActionOSPositive N T L β U / 2 + wilsonActionOSNegative N T L β U / 2 +

                        wilsonActionOSInterface N T L β U)) := by ring

    _ = (f U * f (reflectLinkVariable N U)) *

        (Real.exp (-β * wilsonActionOSPositive N T L β U / 2) * Real.exp (-β * wilsonActionOSNegative N T L β U / 2) *

         Real.exp (-β * (wilsonActionOSPositive N T L β U / 2 + wilsonActionOSNegative N T L β U / 2 +

                         wilsonActionOSInterface N T L β U))) := by

      rw [← Real.exp_add, ← Real.exp_add]

      ring

    _ = (f U * Real.exp (-β * wilsonActionOSPositive N T L β U / 2)) *

        (f (reflectLinkVariable N U) * Real.exp (-β * wilsonActionOSNegative N T L β U / 2)) *

        Real.exp (-β * (wilsonActionOSPositive N T L β U / 2 + wilsonActionOSNegative N T L β U / 2 +

                        wilsonActionOSInterface N T L β U)) := by

      ring



/-- Key lemma: osPositiveOfPosInterface of the restriction equals S_OS⁺(U). -/

lemma osPositiveOfPosInterface_restrict_eq (U : LinkVariable (SU N) (PeriodicSite T L)) :

    osPositiveOfPosInterface N T L β (restrictPosInterface N T L

      (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)) =

    wilsonActionOSPositive N T L β U := by

  let u := restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U)

  dsimp [osPositiveOfPosInterface, u]

  apply wilsonActionOSPositive_dependsOnlyOnPosInterface N T L β _ _

  intro n μ hn

  rcases Finset.mem_union.mp hn with (hn_pos | hn_int)

  · simp [hn_pos, extendLinkVariable, restrictPosInterface, restrictLinkVariable]

  · simp [hn_int, extendLinkVariable, restrictPosInterface, restrictLinkVariable]



/-- reflectToPosInterface(U⁻, U⁰) = restrictPosInterface(restrictLinkVariable(univ, θU)).

  This is proved by extensionality. -/

lemma reflectToPosInterface_eq_restrict (hT : Odd T) (U : LinkVariable (SU N) (PeriodicSite T L)) :

    reflectToPosInterface N T L

      (restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U)

      (restrictToInterface N T L (restrictPosInterface N T L

        (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U))) =

    restrictPosInterface N T L (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))

      (reflectLinkVariable N U)) := by

  ext x

  rcases x with ⟨⟨n, μ⟩, hx⟩

  dsimp [reflectToPosInterface, linkVariableRestrict, reflectLinkVariable, restrictLinkVariable,

    restrictPosInterface, restrictToInterface, extendLinkVariable, mergeConfigurations]

  by_cases hn_pos : n ∈ positiveSites T L

  · have h_reflect_neg : ReflectSite.reflectSite n ∈ negativeSites T L := by

      have h_signed : signedTime T n.time > 0 := by

        simpa [positiveSites, Finset.mem_filter] using hn_pos

      have h_neg_signed : signedTime T (ReflectSite.reflectSite n).time < 0 := by

        calc

          signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time := by

            simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T n.time hT]

          _ < 0 := by linarith

      simpa [negativeSites, Finset.mem_filter] using h_neg_signed

    have h_pos_neg_disjoint : Disjoint (positiveSites T L) (negativeSites T L) := by

      unfold positiveSites negativeSites

      rw [Finset.disjoint_filter]

      intro m hm hpos hneg; linarith

    have h_reflect_not_pos : ReflectSite.reflectSite n ∉ positiveSites T L :=

      Finset.disjoint_right.mp h_pos_neg_disjoint h_reflect_neg

    by_cases hμ : μ = 0

    · subst hμ; simp [hn_pos, h_reflect_neg, h_reflect_not_pos]

    · simp [hn_pos, h_reflect_neg, h_reflect_not_pos, hμ]

  · have hint : n ∈ interfaceSites T L := by

      rcases Finset.mem_union.mp hx with (h | h)

      · exact absurd h hn_pos

      · exact h

    have h_pos_int_disjoint : Disjoint (positiveSites T L) (interfaceSites T L) := by

      unfold positiveSites interfaceSites

      rw [Finset.disjoint_filter]

      intro m hm hpos hint; linarith

    have h_neg_int_disjoint : Disjoint (negativeSites T L) (interfaceSites T L) := by

      unfold negativeSites interfaceSites

      rw [Finset.disjoint_filter]

      intro m hm hneg hint; linarith

    have h_reflect_int : ReflectSite.reflectSite n ∈ interfaceSites T L := by

      have h_signed : signedTime T n.time = 0 := by

        simpa [interfaceSites, Finset.mem_filter] using hint

      have h_int_signed : signedTime T (ReflectSite.reflectSite n).time = 0 := by

        calc

          signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time := by

            simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T n.time hT]

          _ = -0 := by rw [h_signed]

          _ = 0 := by simp

      simpa [interfaceSites, Finset.mem_filter] using h_int_signed

    have h_reflect_not_pos : ReflectSite.reflectSite n ∉ positiveSites T L :=

      Finset.disjoint_right.mp h_pos_int_disjoint h_reflect_int

    have h_reflect_not_neg : ReflectSite.reflectSite n ∉ negativeSites T L :=

      Finset.disjoint_right.mp h_neg_int_disjoint h_reflect_int

    by_cases hμ : μ = 0

    · subst hμ; simp [hint, h_reflect_int, h_reflect_not_pos, h_reflect_not_neg]

    · simp [hint, h_reflect_int, h_reflect_not_pos, h_reflect_not_neg, hμ]


/-- The reflection map from positive-time configurations to negative-time configurations.
This is the inverse of the change-of-variables map `U⁻ ↦ V⁺ = reflect(U⁻)` used in
step (b) of the `transferMatrixPositivity_axiom` closure plan: given `V⁺` on positive
sites, `reflectPosToNeg V⁺` is the negative config obtained by reflecting `V⁺`. -/
noncomputable def reflectPosToNeg
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L)) :
    FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) :=
  restrictLinkVariable N (PeriodicSite T L) (negativeSites T L)
    (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (positiveSites T L) V_plus))

/-- **Link action of `reflectPosToNeg`.** For a negative-site link index `(n, μ)` with
`n ∈ negativeSites`, the reflected negative config `reflectPosToNeg V⁺` evaluates to:
- `μ = 0` (time-like): `(V⁺_{(θn, 0)})⁻¹` — the positive-site link variable, inverted
  (reflection reverses the orientation of time-like links);
- `μ ≠ 0` (spatial): `V⁺_{(θn, μ)}` — the positive-site link variable, unchanged
  (spatial directions commute with reflection).

Here `θn = reflectSite n` is the reflected (positive) site.  This is the key
ingredient for the pointwise character identity in the σ-inversion lemma (Lemma 3):
the time-like inversion produces a `χ(g⁻¹) = conj(χ(g))` factor (via `repCharacter_inv`),
while the spatial case keeps the link variable unchanged. -/
lemma reflectPosToNeg_apply (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    {n : PeriodicSite T L} (hneg : n ∈ negativeSites T L) (μ : Fin 4) :
    reflectPosToNeg N T L V_plus ⟨(n, μ), hneg⟩ =
      if μ = 0 then
        (V_plus ⟨(ReflectSite.reflectSite n, μ),
          reflectSite_mem_positive_of_negative hT hneg⟩)⁻¹
      else
        V_plus ⟨(ReflectSite.reflectSite n, μ),
          reflectSite_mem_positive_of_negative hT hneg⟩ := by
  have hpos : ReflectSite.reflectSite n ∈ positiveSites T L :=
    reflectSite_mem_positive_of_negative hT hneg
  simp only [reflectPosToNeg, restrictLinkVariable, reflectLinkVariable, extendLinkVariable]
  simp only [dif_pos hpos]

#print axioms reflectPosToNeg_apply

/-- The σ reflection on interface configurations: inverts time-like links, keeps spatial.
This is the restriction of `reflectLinkVariable` to interface sites (which are fixed by
`reflectSite` since their time coordinate is 0). -/
noncomputable def sigmaInterface
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L) :=
  restrictLinkVariable N (PeriodicSite T L) (interfaceSites T L)
    (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (interfaceSites T L) U_zero))

/-- **σ-action on individual interface links.** For a link `(n, μ)` at an interface
site `n` (signedTime=0), `sigmaInterface` gives:
- **Temporal** (μ=0): the link value at the reflected site, **inverted**.
- **Spatial** (μ≠0): the link value at the reflected site, **unchanged**.

This is the key property underlying §8.11.32: the σ reflection inverts temporal
interface links (w → w⁻¹, giving ρ(w⁻¹) = ρ(w)† for the Peter-Weyl conjugation)
while keeping spatial interface links fixed. -/
lemma sigmaInterface_apply (hT : Odd T)
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (n : PeriodicSite T L) (hn : n ∈ interfaceSites T L) (μ : Fin 4) :
    sigmaInterface N T L U_zero ⟨(n, μ), hn⟩ =
      if hμ : μ = 0 then
        (U_zero ⟨(ReflectSite.reflectSite n, μ),
          reflectSite_mem_interface_of_interface hT hn⟩)⁻¹
      else
        U_zero ⟨(ReflectSite.reflectSite n, μ),
          reflectSite_mem_interface_of_interface hT hn⟩ := by
  have h_reflect_int : ReflectSite.reflectSite n ∈ interfaceSites T L :=
    reflectSite_mem_interface_of_interface hT hn
  unfold sigmaInterface restrictLinkVariable reflectLinkVariable extendLinkVariable
  by_cases hμ : μ = 0
  · subst hμ; simp [h_reflect_int]
  · simp [h_reflect_int, hμ]

#print axioms sigmaInterface_apply

/-- For spatial interface links (μ ≠ 0), σ leaves the link value unchanged.
This follows from `sigmaInterface_apply` (which reads the link at the reflected site)
and `reflectSite_interface_self` (which fixes interface sites: θ n = n).
Temporal interface links (μ = 0) are inverted by σ; spatial ones are not.
This is the first sub-lemma for the σ-disappears-from-g argument (§8.11.37). -/
lemma sigmaInterface_spatial_fixed (hT : Odd T)
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (n : PeriodicSite T L) (hn : n ∈ interfaceSites T L) (μ : Fin 4) (hμ : μ ≠ 0) :
    sigmaInterface N T L U_zero ⟨(n, μ), hn⟩ = U_zero ⟨(n, μ), hn⟩ := by
  rw [sigmaInterface_apply N T L hT U_zero n hn μ, dif_neg hμ]
  simp only [reflectSite_interface_self hT hn]

#print axioms sigmaInterface_spatial_fixed

/-- The extended merged configurations `extendLinkVariable(mergePosInterface(V⁺, σ(u⁰)))`
and `extendLinkVariable(mergePosInterface(V⁺, u⁰))` agree on positive-site links and
spatial interface links (μ ≠ 0). They differ only on temporal interface links (μ = 0),
where σ inverts. This is the link-by-link agreement underlying `f_sigma_invisible` (§8.11.37):
since `dependsOnlyOnPosSpatialInterface` only constrains positive-site and spatial-interface
links, `f` gives the same value on both configurations. -/
lemma extendLinkVariable_merge_sigma_agree (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))
    (n : PeriodicSite T L) (μ : Fin 4)
    (h : n ∈ positiveSites T L ∨ (n ∈ interfaceSites T L ∧ μ ≠ (0 : Fin 4))) :
    (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus (sigmaInterface N T L U_zero))).value n μ =
    (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus U_zero)).value n μ := by
  rcases h with hpos | ⟨hint, hμ⟩
  · -- n ∈ positiveSites: both give V_plus(n,μ)
    dsimp [extendLinkVariable, mergePosInterface]
    simp [hpos, Finset.mem_union_left _ hpos]
  · -- n ∈ interfaceSites, μ ≠ 0: σ fixes spatial links
    have hdisj : Disjoint (positiveSites T L) (interfaceSites T L) := by
      unfold positiveSites interfaceSites
      rw [Finset.disjoint_filter]; intro m hm hpos hzero; linarith
    have hnpos : n ∉ positiveSites T L := Finset.disjoint_right.mp hdisj hint
    dsimp [extendLinkVariable, mergePosInterface]
    simp [hint, hnpos, Finset.mem_union_right _ hint]
    rw [sigmaInterface_spatial_fixed N T L hT U_zero n hint μ hμ]

#print axioms extendLinkVariable_merge_sigma_agree

/-- If `f` depends only on positive-site and spatial-interface links
(`dependsOnlyOnPosSpatialInterface`), then `f` is invisible to the σ twist on temporal
interface links: `f(extendLinkVariable(mergePosInterface(V⁺, σ(u⁰)))) = f(extendLinkVariable(mergePosInterface(V⁺, u⁰)))`.
This follows directly from `extendLinkVariable_merge_sigma_agree` applied to the
hypothesis `hf`. See §8.11.37. -/
lemma f_sigma_invisible (hT : Odd T)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus (sigmaInterface N T L U_zero))) =
    f (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L)
       (mergePosInterface N T L V_plus U_zero)) := by
  apply hf
  intro n μ h
  exact extendLinkVariable_merge_sigma_agree N T L hT V_plus U_zero n μ h

#print axioms f_sigma_invisible

/-- If two link variables agree on all positive-site links, then `wilsonActionOSPositive`
gives the same value: the positive-time action only sums plaquettes whose four corners
all have positive signed time, and `plaquetteProduct` only reads links at those four
positive corners. -/
lemma wilsonActionOSPositive_congr (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ)
    (U V : LinkVariable (SU N) (PeriodicSite T L))
    (h : ∀ n μ, n ∈ positiveSites T L → U.value n μ = V.value n μ) :
    wilsonActionOSPositive N T L β U = wilsonActionOSPositive N T L β V := by
  unfold wilsonActionOSPositive
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  by_cases hcond : signedTime T n.time > 0 ∧
                   signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                   signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                   signedTime T (addVectorPeriodic T L n ν).time > 0
  · rw [if_pos hcond, if_pos hcond]
    unfold plaquetteContribution plaquetteProduct
    have hAV (m : PeriodicSite T L) (dir : Fin 4) :
        AddVector.addVector m dir = addVectorPeriodic T L m dir := by rfl
    simp only [hAV]
    rw [
      h n μ (by simpa [positiveSites, Finset.mem_filter] using hcond.1),
      h (addVectorPeriodic T L n μ) ν
        (by simpa [positiveSites, Finset.mem_filter] using hcond.2.1),
      h (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν) μ
        (by simpa [positiveSites, Finset.mem_filter] using hcond.2.2.1),
      h (addVectorPeriodic T L n ν) ν
        (by simpa [positiveSites, Finset.mem_filter] using hcond.2.2.2)
    ]
  · rw [if_neg hcond, if_neg hcond]

#print axioms wilsonActionOSPositive_congr

/-- `osPositiveOfPosInterface` is invariant under the σ twist on temporal interface links:
`S⁺(mergePosInterface(V⁺, σ(u⁰))) = S⁺(mergePosInterface(V⁺, u⁰))`.
This follows from `wilsonActionOSPositive_congr` (S⁺ only reads positive-site links)
and `extendLinkVariable_merge_sigma_agree` (the two extended configs agree on positive-site
links). See §8.11.37. -/
lemma osPositiveOfPosInterface_sigma_invariant (hT : Odd T)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    osPositiveOfPosInterface N T L β (mergePosInterface N T L V_plus (sigmaInterface N T L U_zero)) =
    osPositiveOfPosInterface N T L β (mergePosInterface N T L V_plus U_zero) := by
  unfold osPositiveOfPosInterface
  apply wilsonActionOSPositive_congr N T L β
  intro n μ hpos
  exact extendLinkVariable_merge_sigma_agree N T L hT V_plus U_zero n μ (Or.inl hpos)

#print axioms osPositiveOfPosInterface_sigma_invariant

/-- **σ-disappears-from-g (main lemma).** The function `g(u) = f(u)·exp(-β·S⁺(u)/2)` is
invisible to the σ twist on temporal interface links:
`g(mergePosInterface(V⁺, σ(u⁰))) = g(mergePosInterface(V⁺, u⁰))`.
This combines `f_sigma_invisible` (f ignores σ) and `osPositiveOfPosInterface_sigma_invariant`
(S⁺ ignores σ). See §8.11.37. -/
lemma g_posInterface_sigma_invisible (hT : Odd T)
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf : dependsOnlyOnPosSpatialInterface N T L f)
    (V_plus : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L))
    (U_zero : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) :
    g_posInterface N T L hT β f (mergePosInterface N T L V_plus (sigmaInterface N T L U_zero)) =
    g_posInterface N T L hT β f (mergePosInterface N T L V_plus U_zero) := by
  unfold g_posInterface
  rw [f_sigma_invisible N T L hT f hf V_plus U_zero,
      osPositiveOfPosInterface_sigma_invariant N T L β hT V_plus U_zero]

#print axioms g_posInterface_sigma_invisible

