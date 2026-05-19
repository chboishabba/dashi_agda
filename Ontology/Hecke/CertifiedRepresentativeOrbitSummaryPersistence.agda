module Ontology.Hecke.CertifiedRepresentativeOrbitSummaryPersistence where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( certifiedBalancedComposed
    ; certifiedBalancedCycle
    ; certifiedDenseComposed
    ; certifiedExplicitWidth1
    ; certifiedExplicitWidth3
    )
open import Ontology.Hecke.CertifiedRepresentativePersistence as CRP
  using
    ( CertifiedRepresentativeClass
    ; P2PersistenceTier
    ; anchoredRep
    ; immediateRep
    ; p2PersistenceTierAt
    ; reducedPersistence
    ; saturatedPersistence
    ; stayRep
    )
open import Ontology.Hecke.ExitToAnchoredRepresentativeComputations as ETRC
  using
    ( exitToAnchoredForcedStableOrbitP2-balancedComposed
    ; exitToAnchoredForcedStableOrbitP2-balancedCycle
    ; exitToAnchoredRepresentativeOrbitSummaryP2
    )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using (DefectOrbitSummary)
open import Ontology.Hecke.ImmediateExitRepresentativeComputations as IERC
  using
    ( exitAnchoredTrajectory
    ; exitExplicitWidth2
    ; exitFullSupportCascade
    ; immediateExitForcedStableOrbitP2-anchoredTrajectory
    ; immediateExitForcedStableOrbitP2-explicitWidth2
    ; immediateExitForcedStableOrbitP2-fullSupportCascade
    ; immediateExitRepresentativeOrbitSummaryP2
    )
open import Ontology.Hecke.StaysOneMoreStepRepresentativeComputations as SSRC
  using
    ( stayForcedStableOrbitP2-denseComposed
    ; stayForcedStableOrbitP2-explicitWidth1
    ; stayForcedStableOrbitP2-explicitWidth3
    ; stayRepresentativeOrbitSummaryP2
    )

------------------------------------------------------------------------
-- Certified persistence factorization through the full Hecke
-- `DefectOrbitSummary`, not only through the extracted count band.

orbitSummaryP2At : CertifiedRepresentativeClass → DefectOrbitSummary
orbitSummaryP2At (stayRep c) = stayRepresentativeOrbitSummaryP2 c
orbitSummaryP2At (anchoredRep c) = exitToAnchoredRepresentativeOrbitSummaryP2 c
orbitSummaryP2At (immediateRep c) = immediateExitRepresentativeOrbitSummaryP2 c

orbitSummaryForcedStableCountAt :
  CertifiedRepresentativeClass → Nat
orbitSummaryForcedStableCountAt c =
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryP2At c)

orbitSummaryForcedStableCount-explicitWidth1 :
  orbitSummaryForcedStableCountAt (stayRep certifiedExplicitWidth1) ≡ 2
orbitSummaryForcedStableCount-explicitWidth1 =
  stayForcedStableOrbitP2-explicitWidth1

orbitSummaryForcedStableCount-explicitWidth3 :
  orbitSummaryForcedStableCountAt (stayRep certifiedExplicitWidth3) ≡ 15
orbitSummaryForcedStableCount-explicitWidth3 =
  stayForcedStableOrbitP2-explicitWidth3

orbitSummaryForcedStableCount-denseComposed :
  orbitSummaryForcedStableCountAt (stayRep certifiedDenseComposed) ≡ 15
orbitSummaryForcedStableCount-denseComposed =
  stayForcedStableOrbitP2-denseComposed

orbitSummaryForcedStableCount-balancedCycle :
  orbitSummaryForcedStableCountAt (anchoredRep certifiedBalancedCycle) ≡ 15
orbitSummaryForcedStableCount-balancedCycle =
  exitToAnchoredForcedStableOrbitP2-balancedCycle

orbitSummaryForcedStableCount-balancedComposed :
  orbitSummaryForcedStableCountAt (anchoredRep certifiedBalancedComposed) ≡ 15
orbitSummaryForcedStableCount-balancedComposed =
  exitToAnchoredForcedStableOrbitP2-balancedComposed

orbitSummaryForcedStableCount-explicitWidth2 :
  orbitSummaryForcedStableCountAt (immediateRep exitExplicitWidth2) ≡ 15
orbitSummaryForcedStableCount-explicitWidth2 =
  immediateExitForcedStableOrbitP2-explicitWidth2

orbitSummaryForcedStableCount-anchoredTrajectory :
  orbitSummaryForcedStableCountAt (immediateRep exitAnchoredTrajectory) ≡ 15
orbitSummaryForcedStableCount-anchoredTrajectory =
  immediateExitForcedStableOrbitP2-anchoredTrajectory

orbitSummaryForcedStableCount-fullSupportCascade :
  orbitSummaryForcedStableCountAt (immediateRep exitFullSupportCascade) ≡ 15
orbitSummaryForcedStableCount-fullSupportCascade =
  immediateExitForcedStableOrbitP2-fullSupportCascade

data CertifiedOrbitSummaryBand : DefectOrbitSummary → Set where
  reducedSummary :
    ∀ {s} →
    FOS.DefectOrbitSummary.forcedStableCount s ≡ 2 →
    CertifiedOrbitSummaryBand s
  saturatedSummary :
    ∀ {s} →
    FOS.DefectOrbitSummary.forcedStableCount s ≡ 15 →
    CertifiedOrbitSummaryBand s

tierFromCertifiedOrbitSummaryBand :
  ∀ {s} →
  CertifiedOrbitSummaryBand s → P2PersistenceTier
tierFromCertifiedOrbitSummaryBand (reducedSummary _) = reducedPersistence
tierFromCertifiedOrbitSummaryBand (saturatedSummary _) = saturatedPersistence

orbitSummaryBandAt :
  (c : CertifiedRepresentativeClass) →
  CertifiedOrbitSummaryBand (orbitSummaryP2At c)
orbitSummaryBandAt (stayRep certifiedExplicitWidth1) =
  reducedSummary orbitSummaryForcedStableCount-explicitWidth1
orbitSummaryBandAt (stayRep certifiedExplicitWidth3) =
  saturatedSummary orbitSummaryForcedStableCount-explicitWidth3
orbitSummaryBandAt (stayRep certifiedDenseComposed) =
  saturatedSummary orbitSummaryForcedStableCount-denseComposed
orbitSummaryBandAt (anchoredRep certifiedBalancedCycle) =
  saturatedSummary orbitSummaryForcedStableCount-balancedCycle
orbitSummaryBandAt (anchoredRep certifiedBalancedComposed) =
  saturatedSummary orbitSummaryForcedStableCount-balancedComposed
orbitSummaryBandAt (immediateRep exitExplicitWidth2) =
  saturatedSummary orbitSummaryForcedStableCount-explicitWidth2
orbitSummaryBandAt (immediateRep exitAnchoredTrajectory) =
  saturatedSummary orbitSummaryForcedStableCount-anchoredTrajectory
orbitSummaryBandAt (immediateRep exitFullSupportCascade) =
  saturatedSummary orbitSummaryForcedStableCount-fullSupportCascade

persistenceTier-factors-through-orbitSummary :
  ∀ c →
  p2PersistenceTierAt c
    ≡
  tierFromCertifiedOrbitSummaryBand (orbitSummaryBandAt c)
persistenceTier-factors-through-orbitSummary (stayRep certifiedExplicitWidth1) =
  refl
persistenceTier-factors-through-orbitSummary (stayRep certifiedExplicitWidth3) =
  refl
persistenceTier-factors-through-orbitSummary (stayRep certifiedDenseComposed) =
  refl
persistenceTier-factors-through-orbitSummary (anchoredRep certifiedBalancedCycle) =
  refl
persistenceTier-factors-through-orbitSummary (anchoredRep certifiedBalancedComposed) =
  refl
persistenceTier-factors-through-orbitSummary (immediateRep exitExplicitWidth2) =
  refl
persistenceTier-factors-through-orbitSummary (immediateRep exitAnchoredTrajectory) =
  refl
persistenceTier-factors-through-orbitSummary (immediateRep exitFullSupportCascade) =
  refl

record CertifiedRepresentativeOrbitSummaryFactorization : Set₁ where
  field
    summary : CertifiedRepresentativeClass → DefectOrbitSummary
    persistenceTier : CertifiedRepresentativeClass → P2PersistenceTier
    factor :
      ∀ c →
      persistenceTier c
        ≡
      tierFromCertifiedOrbitSummaryBand (orbitSummaryBandAt c)

canonicalCertifiedRepresentativeOrbitSummaryFactorization :
  CertifiedRepresentativeOrbitSummaryFactorization
canonicalCertifiedRepresentativeOrbitSummaryFactorization =
  record
    { summary = orbitSummaryP2At
    ; persistenceTier = p2PersistenceTierAt
    ; factor = persistenceTier-factors-through-orbitSummary
    }
