module Ontology.Hecke.CertifiedSaturatedForcedStableCollapse where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( certifiedBalancedComposed
    ; certifiedBalancedCycle
    ; certifiedDenseComposed
    ; certifiedExplicitWidth3
    )
open import Ontology.Hecke.CertifiedRepresentativePersistence as CRP
  using
    ( CertifiedRepresentativeClass
    ; anchoredRep
    ; immediateRep
    ; stayRep
    )
open import Ontology.Hecke.ImmediateExitRepresentativeComputations as IERC
  using
    ( exitAnchoredTrajectory
    ; exitExplicitWidth2
    ; exitFullSupportCascade
    )
open import Ontology.Hecke.CertifiedRepresentativeOrbitSummaryPersistence as CROSP
  using
    ( orbitSummaryForcedStableCountAt
    )

------------------------------------------------------------------------
-- Current negative boundary on the saturated side.
--
-- The full Hecke-side `DefectOrbitSummary` is already present on the current
-- certified representative set, but the only theorem-bearing separating field
-- so far is `forcedStableCount`. That field does split off `explicitWidth1`,
-- but it completely collapses the present saturated side to the single value
-- `15`.

data CertifiedSaturatedRepresentative : Set where
  stayExplicitWidth3 : CertifiedSaturatedRepresentative
  stayDenseComposed : CertifiedSaturatedRepresentative
  anchoredBalancedCycle : CertifiedSaturatedRepresentative
  anchoredBalancedComposed : CertifiedSaturatedRepresentative
  immediateExplicitWidth2 : CertifiedSaturatedRepresentative
  immediateAnchoredTrajectory : CertifiedSaturatedRepresentative
  immediateFullSupportCascade : CertifiedSaturatedRepresentative

saturatedRepresentativeClass :
  CertifiedSaturatedRepresentative → CertifiedRepresentativeClass
saturatedRepresentativeClass stayExplicitWidth3 =
  stayRep GT.certifiedExplicitWidth3
saturatedRepresentativeClass stayDenseComposed =
  stayRep GT.certifiedDenseComposed
saturatedRepresentativeClass anchoredBalancedCycle =
  anchoredRep GT.certifiedBalancedCycle
saturatedRepresentativeClass anchoredBalancedComposed =
  anchoredRep GT.certifiedBalancedComposed
saturatedRepresentativeClass immediateExplicitWidth2 =
  immediateRep IERC.exitExplicitWidth2
saturatedRepresentativeClass immediateAnchoredTrajectory =
  immediateRep IERC.exitAnchoredTrajectory
saturatedRepresentativeClass immediateFullSupportCascade =
  immediateRep IERC.exitFullSupportCascade

saturatedForcedStableCountAt :
  CertifiedSaturatedRepresentative → Nat
saturatedForcedStableCountAt c =
  orbitSummaryForcedStableCountAt (saturatedRepresentativeClass c)

saturatedForcedStableCount≡15 :
  ∀ c →
  saturatedForcedStableCountAt c ≡ 15
saturatedForcedStableCount≡15 stayExplicitWidth3 = refl
saturatedForcedStableCount≡15 stayDenseComposed = refl
saturatedForcedStableCount≡15 anchoredBalancedCycle = refl
saturatedForcedStableCount≡15 anchoredBalancedComposed = refl
saturatedForcedStableCount≡15 immediateExplicitWidth2 = refl
saturatedForcedStableCount≡15 immediateAnchoredTrajectory = refl
saturatedForcedStableCount≡15 immediateFullSupportCascade = refl
