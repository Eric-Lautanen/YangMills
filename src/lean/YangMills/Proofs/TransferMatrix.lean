/-

# Transfer Matrix: Corrected Approach



This file provides definitions and lemmas toward a transfer matrix proof

of the Osterwalder-Seiler reflection positivity for the periodic lattice.



## Mathematical Setup



Let μ₀ = μ⁺ ⊗ μ⁻ ⊗ μ⁰ be the factorization of the product Haar measure on

the finite periodic lattice into positive-time, negative-time, and interface

links (via `measure_factorization'`).



For an observable f depending only on links in the positive-time and interface

regions (`dependsOnlyOnPosInterface N T L f`), define:



    G(U) = f(U)·exp(-β·S_OS⁺(U))·exp(-β·S_OS_int(U)/2)

    g(u) = f(u)·exp(-β·S_OS⁺(u)/2)   for u ∈ PosInterfaceConfig



The reflection positivity lemma `gibbsExpectationPeriodic_reflection_positive`

reduces to proving:



    ∫ G(U)·G(θU) dμ₀(U) ≥ 0



## The Correct Transfer Matrix



Define the transfer matrix T acting on functions ψ : PosInterfaceConfig → ℝ by:



    (T ψ)(U⁺,U⁰) = ∫ ψ(θ⁻⁰(U⁻,U⁰))

                     · exp(-β·(S_OS⁻(U⁻)+S_OS_int(U⁺,U⁻,U⁰))/2)

                     dμ⁻(U⁻)



where θ⁻⁰(U⁻,U⁰) is the restriction of θ(merge(U⁻,U⁰)) to positive+interface

sites (i.e., reflecting the negative links to the positive side).



## Key Identity



    ∫ G(U)·G(θU) dμ₀(U) = ∫_{PosInt} g(u)·(T g)(u) dμ⁺⁰(u)



This holds because:

1. G(U)·G(θU) = g(U⁺,U⁰)·g(θ⁻⁰(U⁻,U⁰))

                · exp(-β·(S_OS⁻(U⁻)+S_OS_int(U⁺,U⁻,U⁰))/2)

2. The factorization μ₀ ≅ μ⁺ × μ⁻ × μ⁰ turns the LHS into an integral

   over U⁺,U⁻,U⁰ of this expression.

3. Integrating out U⁻ gives (T g)(U⁺,U⁰) by definition.



## Positivity



The operator T is POSITIVE because its integral kernel is a positive-definite

function on (SU(N)ⁿ × SU(N)ⁿ). This follows from the Peter-Weyl theorem on

SU(N) (Osterwalder-Seiler 1979, Theorem 3.1). Therefore ⟨g, T·g⟩ ≥ 0.



## Previous (Incorrect) Approach



A previous version of this file defined a different transfer matrix that acted

trivially (as a multiplication operator) because it did not apply the reflection

θ⁻⁰ in the kernel.  This made the identity `transferMatrix_identity` false for

general f.  The current approach corrects this by applying the reflection.



## References



- K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"

  (Ann. Phys. 110, 1978, pp 440–471), §3.

- J. Glimm, A. Jaffe, "Quantum Physics" (2nd ed.), §6.1.

- M. Lüscher, "Some analytic results concerning the mass spectrum

  of Yang-Mills gauge theories on a torus" (1983)

- M. Salmhofer, "Construction of a Higgs field" (thesis, 1990).

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

/-- The key identity for the Osterwalder-Seiler reflection positivity proof:



  ∫ G(U)·G(θU) dμ₀(U) = ∫_{PosInt} g(u)·(T g)(u) dμ⁺⁰(u)



  where G(U) = f(U)·exp(-β·S_OS⁺(U))·exp(-β·S_OS_int(U)/2) and

  g(u) = f(u)·exp(-β·S_OS⁺(u)/2).



  Hypothesis: `hf_supported` ensures f (hence g) depends only on positive+interface links.

  Hypothesis: `hf` ensures f is measurable (so the integrals are well-defined).

-/

lemma integral_G_thetaG_eq_inner_g_Tg (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)

    (hf : Measurable f) (hf_supported : dependsOnlyOnPosInterface N T L f)

    (hf_int : Integrable

      (fun (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>

        G N T L hT β f (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg) *

        G N T L hT β f (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg)))

      (productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)))) :

    (∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),

      G N T L hT β f (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg) *

      G N T L hT β f (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg))

      ∂ productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =

    (∫ (u : PosInterfaceConfig N T L),

      g_posInterface N T L hT β f u * (transferMatrixCorrect N T L β (g_posInterface N T L hT β f) u)

      ∂ haarMeasurePosInterface N T L) := by
  -- Step 1: the measure-preserving equiv
  obtain ⟨e, ⟨hMP, hRestrict⟩, hNeg⟩ := measure_factorization' N T L
  -- Measure abbreviations (after obtain so they also rewrite inside hMP)
  set muP := haarMeasurePositive N T L
  set muN := haarMeasureNegative N T L
  set muI := haarMeasureInterface N T L
  set mu0 := productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
  set H := fun (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
    G N T L hT β f (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg) *
    G N T L hT β f (reflectLinkVariable N (extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) cfg))
  -- Finiteness instances for the product Haar measures (needed for prod operations)
  haveI hfinP : IsFiniteMeasure muP :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (positiveSites T L)
  haveI hfinN : IsFiniteMeasure muN :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (negativeSites T L)
  haveI hfinI : IsFiniteMeasure muI :=
    productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (interfaceSites T L)
  -- Disjointness of positive and interface sites
  have hpi : Disjoint (positiveSites T L) (interfaceSites T L) := by
    unfold positiveSites interfaceSites
    rw [Finset.disjoint_filter]; intro n hn hpos hzero; linarith
  -- Reassociation equiv rho : (Pos × (Neg × Int)) ≃ᵐ ((Pos × Int) × Neg)
  let rho : (FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
           (FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L) ×
            FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L))) ≃ᵐ
          ((FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
            FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)) ×
           FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm
  have hMPrho : MeasurePreserving rho (muP.prod (muN.prod muI)) ((muP.prod muI).prod muN) := by
    -- rho = (prodCongr id prodComm).trans prodAssoc.symm
    -- (a) prodCongr id swap : Pos × (Neg × Int) → Pos × (Int × Neg), measure-preserving
    have h1 : MeasurePreserving (Prod.map id Prod.swap)
        (muP.prod (muN.prod muI)) (muP.prod (muI.prod muN)) :=
      MeasurePreserving.prod (MeasurePreserving.id muP) (Measure.measurePreserving_swap (μ := muN) (ν := muI))
    -- (b) prodAssoc.symm : Pos × (Int × Neg) → (Pos × Int) × Neg, measure-preserving
    have h2 : MeasurePreserving MeasurableEquiv.prodAssoc.symm
        (muP.prod (muI.prod muN)) ((muP.prod muI).prod muN) :=
      (measurePreserving_prodAssoc muP muI muN).symm
    exact h2.comp h1
  have hrho_symm_apply : ∀ y, rho.symm y = ⟨y.1.1, ⟨y.2, y.1.2⟩⟩ := by
    intro y; rfl
  -- Step 2: change of variables
  rw [← hMP.integral_comp' H]
  -- Step 4: reassociate via rho.symm
  rw [← hMPrho.symm.integral_comp' (fun x => H (e x))]
  -- Step 6: integrability (push hf_int through CoV then reassociation)
  have hHe_int : Integrable (fun x => H (e x)) (muP.prod (muN.prod muI)) :=
    hMP.integrable_comp_emb e.measurableEmbedding |>.mpr hf_int
  have hInt : Integrable (fun y => H (e (rho.symm y))) ((muP.prod muI).prod muN) :=
    hMPrho.symm.integrable_comp_emb rho.symm.measurableEmbedding |>.mpr hHe_int
  rw [integral_prod _ hInt]
  -- Step 5+7: inner identity
  have hInner : ∀ (x : FiniteLinkConfig N (PeriodicSite T L) (positiveSites T L) ×
      FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
      ∫ (Uneg : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),
        H (e (rho.symm (x, Uneg))) ∂muN =
      g_posInterface N T L hT β f (mergePosInterface N T L x.1 x.2) *
      transferMatrixCorrect N T L β (g_posInterface N T L hT β f) (mergePosInterface N T L x.1 x.2) := by
    intro x
    set m := mergePosInterface N T L x.1 x.2
    -- Pointwise identity: for each Uneg, H (e (rho.symm (x, Uneg))) factors as g(m) * bracket
    have hpt : ∀ (Uneg : FiniteLinkConfig N (PeriodicSite T L) (negativeSites T L)),
        H (e (rho.symm (x, Uneg))) =
        g_posInterface N T L hT β f m *
          (g_posInterface N T L hT β f (reflectToPosInterface N T L Uneg (restrictToInterface N T L m)) *
            Real.exp (-β * (osPositiveOfPosInterface N T L β m / 2 +
              wilsonActionOSNegative N T L β (extendToFullConfig N T L Uneg m) / 2 +
              wilsonActionOSInterface N T L β (extendToFullConfig N T L Uneg m)))) := by
      intro Uneg
      set U := extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
        (e (rho.symm (x, Uneg)))
      -- restrict univ U = e (rho.symm (x, Uneg))  (extend then restrict = identity)
      have h_ru : restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U =
          e (rho.symm (x, Uneg)) := by
        funext idx
        obtain ⟨⟨n, μ⟩, hn⟩ := idx
        simp only [restrictLinkVariable, extendLinkVariable, U, dif_pos (Finset.mem_univ n)]
      -- restrictPosInterface (restrict univ U) = m  (via hRestrict and rho.symm structure)
      have h_rpi : restrictPosInterface N T L
          (restrictLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) U) = m := by
        rw [h_ru, hRestrict (rho.symm (x, Uneg))]; rfl
      -- restrict neg U = Uneg  (via hNeg and rho.symm structure)
      have h_rn : restrictLinkVariable N (PeriodicSite T L) (negativeSites T L) U = Uneg := by
        funext idx
        obtain ⟨⟨n, μ⟩, hn⟩ := idx
        simp only [restrictLinkVariable, extendLinkVariable, U, dif_pos (Finset.mem_univ n)]
        rw [hNeg (rho.symm (x, Uneg)) ⟨(n, μ), hn⟩]
        rfl
      -- Unfold H to G U * G(θU), then apply the factorization and substitute
      rw [show H (e (rho.symm (x, Uneg))) =
          G N T L hT β f U * G N T L hT β f (reflectLinkVariable N U) from rfl]
      rw [G_thetaG_factorization N T L hT β f hf_supported U]
      rw [h_rpi, h_rn]
      ring
    simp only [hpt]
    rw [integral_const_mul]
    rfl
  simp only [hInner]
  -- Step 9: transform RHS via integral_map
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
  rw [haarMeasurePosInterface_eq]
  have hRHS : (∫ u, g_posInterface N T L hT β f u * transferMatrixCorrect N T L β (g_posInterface N T L hT β f) u
      ∂ Measure.map (Function.uncurry (mergePosInterface N T L)) (muP.prod muI)) =
    (∫ x, g_posInterface N T L hT β f (Function.uncurry (mergePosInterface N T L) x) *
      transferMatrixCorrect N T L β (g_posInterface N T L hT β f) (Function.uncurry (mergePosInterface N T L) x)
      ∂ (muP.prod muI)) :=
    hME.integral_map (fun u => g_posInterface N T L hT β f u * transferMatrixCorrect N T L β (g_posInterface N T L hT β f) u)
  rw [hRHS]
  rfl


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
