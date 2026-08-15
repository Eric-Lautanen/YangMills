/-
# Transfer Matrix: Key Identity
-/

import YangMills.Proofs.TransferMatrix.Fubini

open Set
open Matrix
open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
namespace Lattice

section TransferMatrix

variable (N T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (β : ℝ)
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


