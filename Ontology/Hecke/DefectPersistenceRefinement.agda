module Ontology.Hecke.DefectPersistenceRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( CollapseTime
    ; exitToAnchored
    ; immediateExit
    ; staysOneMoreStep
    ; unknownCollapse
    )
open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( certifiedDenseComposed
    ; certifiedExplicitWidth1
    ; certifiedExplicitWidth3
    )
open import Ontology.Hecke.CertifiedRepresentativeOrbitSummaryPersistence as CROSP
  using
    ( orbitSummaryBandAt
    ; persistenceTier-factors-through-orbitSummary
    ; tierFromCertifiedOrbitSummaryBand
    )
open import Ontology.Hecke.CertifiedRepresentativePersistence as CRP
  using
    ( CertifiedRepresentativeClass
    ; anchoredRep
    ; certifiedRepresentativeCollapseTime
    ; explicitWidth1-reducedPersistence
    ; explicitWidth2-saturatedPersistence
    ; explicitWidth3-saturatedPersistence
    ; fullSupportCascade-saturatedPersistence
    ; immediateRep
    ; p2PersistenceTierAt
    ; reducedPersistence
    ; saturatedPersistence
    ; stayRep
    ; anchoredTrajectory-saturatedPersistence
    ; balancedComposed-saturatedPersistence
    ; balancedCycle-saturatedPersistence
    ; denseComposed-saturatedPersistence
    )
open import Ontology.Hecke.ImmediateExitRepresentativeComputations as IERC
  using
    ( exitAnchoredTrajectory
    ; exitExplicitWidth2
    ; exitFullSupportCascade
    )

------------------------------------------------------------------------
-- Minimal Hecke-side refinement above collapse time on the current
-- certified representative set.
--
-- Current exact `p2` data shows that collapse time alone does not determine
-- the Hecke-side pressure count: `explicitWidth1` and the other current
-- stay-class representatives all have `staysOneMoreStep`, but only
-- `explicitWidth1` lands in the reduced `forcedStableCountOrbitP2 = 2`
-- branch.  The smallest honest refinement is therefore one extra bit inside
-- the stay class.

data StayRefinement : Set where
  lowStay : StayRefinement
  highStay : StayRefinement
  nonStay : StayRefinement

stayRefinementFrom :
  CollapseTime → CRP.P2PersistenceTier → StayRefinement
stayRefinementFrom staysOneMoreStep reducedPersistence = lowStay
stayRefinementFrom staysOneMoreStep saturatedPersistence = highStay
stayRefinementFrom immediateExit _ = nonStay
stayRefinementFrom exitToAnchored _ = nonStay
stayRefinementFrom unknownCollapse _ = nonStay

stayRefinementAt : CertifiedRepresentativeClass → StayRefinement
stayRefinementAt c =
  stayRefinementFrom
    (certifiedRepresentativeCollapseTime c)
    (p2PersistenceTierAt c)

data RefinedPressureLevel : Set where
  reducedPressure : RefinedPressureLevel
  saturatedPressure : RefinedPressureLevel

refinedPressureLevel : StayRefinement → RefinedPressureLevel
refinedPressureLevel lowStay = reducedPressure
refinedPressureLevel highStay = saturatedPressure
refinedPressureLevel nonStay = saturatedPressure

exactOrbitPressureAt : StayRefinement → Nat
exactOrbitPressureAt lowStay = 2
exactOrbitPressureAt highStay = 15
exactOrbitPressureAt nonStay = 15

stayRefinementFromOrbitSummary : CertifiedRepresentativeClass → StayRefinement
stayRefinementFromOrbitSummary c =
  stayRefinementFrom
    (certifiedRepresentativeCollapseTime c)
    (tierFromCertifiedOrbitSummaryBand (orbitSummaryBandAt c))

stayRefinement-factors-through-orbitSummary :
  ∀ c →
  stayRefinementAt c ≡ stayRefinementFromOrbitSummary c
stayRefinement-factors-through-orbitSummary c
  rewrite persistenceTier-factors-through-orbitSummary c = refl

------------------------------------------------------------------------
-- Current exact certified identities.

explicitWidth1-lowStay :
  stayRefinementAt (stayRep certifiedExplicitWidth1) ≡ lowStay
explicitWidth1-lowStay = refl

explicitWidth3-highStay :
  stayRefinementAt (stayRep certifiedExplicitWidth3) ≡ highStay
explicitWidth3-highStay = refl

denseComposed-highStay :
  stayRefinementAt (stayRep certifiedDenseComposed) ≡ highStay
denseComposed-highStay = refl

balancedCycle-nonStay :
  stayRefinementAt (anchoredRep GT.certifiedBalancedCycle) ≡ nonStay
balancedCycle-nonStay = refl

balancedComposed-nonStay :
  stayRefinementAt (anchoredRep GT.certifiedBalancedComposed) ≡ nonStay
balancedComposed-nonStay = refl

explicitWidth2-nonStay :
  stayRefinementAt (immediateRep exitExplicitWidth2) ≡ nonStay
explicitWidth2-nonStay = refl

anchoredTrajectory-nonStay :
  stayRefinementAt (immediateRep exitAnchoredTrajectory) ≡ nonStay
anchoredTrajectory-nonStay = refl

fullSupportCascade-nonStay :
  stayRefinementAt (immediateRep exitFullSupportCascade) ≡ nonStay
fullSupportCascade-nonStay = refl

------------------------------------------------------------------------
-- Exact current orbit-pressure law on the certified representative set.

refinedPressure-explicitWidth1 :
  exactOrbitPressureAt (stayRefinementAt (stayRep certifiedExplicitWidth1)) ≡ 2
refinedPressure-explicitWidth1
  rewrite explicitWidth1-lowStay = refl

refinedPressure-explicitWidth3 :
  exactOrbitPressureAt (stayRefinementAt (stayRep certifiedExplicitWidth3)) ≡ 15
refinedPressure-explicitWidth3
  rewrite explicitWidth3-highStay = refl

refinedPressure-denseComposed :
  exactOrbitPressureAt (stayRefinementAt (stayRep certifiedDenseComposed)) ≡ 15
refinedPressure-denseComposed
  rewrite denseComposed-highStay = refl

refinedPressure-balancedCycle :
  exactOrbitPressureAt (stayRefinementAt (anchoredRep GT.certifiedBalancedCycle)) ≡ 15
refinedPressure-balancedCycle
  rewrite balancedCycle-nonStay = refl

refinedPressure-balancedComposed :
  exactOrbitPressureAt (stayRefinementAt (anchoredRep GT.certifiedBalancedComposed)) ≡ 15
refinedPressure-balancedComposed
  rewrite balancedComposed-nonStay = refl

refinedPressure-explicitWidth2 :
  exactOrbitPressureAt (stayRefinementAt (immediateRep exitExplicitWidth2)) ≡ 15
refinedPressure-explicitWidth2
  rewrite explicitWidth2-nonStay = refl

refinedPressure-anchoredTrajectory :
  exactOrbitPressureAt (stayRefinementAt (immediateRep exitAnchoredTrajectory)) ≡ 15
refinedPressure-anchoredTrajectory
  rewrite anchoredTrajectory-nonStay = refl

refinedPressure-fullSupportCascade :
  exactOrbitPressureAt (stayRefinementAt (immediateRep exitFullSupportCascade)) ≡ 15
refinedPressure-fullSupportCascade
  rewrite fullSupportCascade-nonStay = refl

record CertifiedRepresentativePersistenceRefinementFactorization : Set₁ where
  field
    refinement : CertifiedRepresentativeClass → StayRefinement
    refinementFromOrbitSummary : CertifiedRepresentativeClass → StayRefinement
    factor :
      ∀ c →
      refinement c ≡ refinementFromOrbitSummary c

canonicalCertifiedRepresentativePersistenceRefinementFactorization :
  CertifiedRepresentativePersistenceRefinementFactorization
canonicalCertifiedRepresentativePersistenceRefinementFactorization =
  record
    { refinement = stayRefinementAt
    ; refinementFromOrbitSummary = stayRefinementFromOrbitSummary
    ; factor = stayRefinement-factors-through-orbitSummary
    }
