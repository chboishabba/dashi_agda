module Ontology.Hecke.ImmediateExitRepresentativeComputations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Pressure using (Pressure; high)
open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( GeneratorCollapseClass
    ; collapseTime
    ; collapseTime-anchoredTrajectory
    ; collapseTime-explicitWidth2
    ; collapseTime-fullSupportCascade
    ; immediateExit
    ; mixedScaleClass
    ; prefixClass
    )
open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( CertifiedExitClass
    ; certifiedAnchoredTrajectory
    ; certifiedExplicitWidth2
    ; exitClassToGeneratorClass
    )
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily
  using
    ( MixedScaleGeneratorClass
    ; fullSupportCascade
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance
  using (ShiftContractState)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.DefectOrbitCollapseBridge as DOCB
  using
    ( forcedStableCountOrbitP2
    ; illegalCountP2
    ; orbitSummaryP2
    ; primeImage
    ; representativeState
    )
open import Ontology.Hecke.DefectOrbitCollapsePressure as DOCP
  using
    ( PressureClass
    ; defectPressureSummaryAt
    ; highPressure
    ; pressureClass
    ; pressureClass-explicit-immediateExit
    )
open import Ontology.Hecke.PressureAdapter using
  ( embedPressureClass
  ; embedPressureClass-high
  )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries
  using (DefectOrbitSummary)

------------------------------------------------------------------------
-- Concrete evaluator surface for the current `immediateExit` classes.

data CertifiedImmediateExitClass : Set where
  exitExplicitWidth2 : CertifiedImmediateExitClass
  exitAnchoredTrajectory : CertifiedImmediateExitClass
  exitFullSupportCascade : CertifiedImmediateExitClass

immediateExitCollapseClass :
  CertifiedImmediateExitClass → GeneratorCollapseClass
immediateExitCollapseClass exitExplicitWidth2 =
  prefixClass (GT.exitClassToGeneratorClass certifiedExplicitWidth2)
immediateExitCollapseClass exitAnchoredTrajectory =
  prefixClass (GT.exitClassToGeneratorClass certifiedAnchoredTrajectory)
immediateExitCollapseClass exitFullSupportCascade =
  mixedScaleClass fullSupportCascade

immediateExitCollapseTime :
  (c : CertifiedImmediateExitClass) →
  collapseTime (immediateExitCollapseClass c) ≡ immediateExit
immediateExitCollapseTime exitExplicitWidth2 = collapseTime-explicitWidth2
immediateExitCollapseTime exitAnchoredTrajectory =
  collapseTime-anchoredTrajectory
immediateExitCollapseTime exitFullSupportCascade =
  collapseTime-fullSupportCascade

immediateExitRepresentativeState :
  CertifiedImmediateExitClass → ShiftContractState
immediateExitRepresentativeState c =
  representativeState (immediateExitCollapseClass c)

immediateExitRepresentativePrimeImage :
  CertifiedImmediateExitClass → FactorVec
immediateExitRepresentativePrimeImage c =
  primeImage (immediateExitCollapseClass c)

immediateExitRepresentativeOrbitSummaryP2 :
  CertifiedImmediateExitClass → DefectOrbitSummary
immediateExitRepresentativeOrbitSummaryP2 c =
  orbitSummaryP2 (immediateExitCollapseClass c)

immediateExitRepresentativeIllegalCountP2 :
  CertifiedImmediateExitClass → Nat
immediateExitRepresentativeIllegalCountP2 c =
  illegalCountP2 (immediateExitCollapseClass c)

immediateExitRepresentativeForcedStableCountOrbitP2 :
  CertifiedImmediateExitClass → Nat
immediateExitRepresentativeForcedStableCountOrbitP2 c =
  forcedStableCountOrbitP2 (immediateExitCollapseClass c)

immediateExitRepresentativePressureClass :
  CertifiedImmediateExitClass → PressureClass
immediateExitRepresentativePressureClass c =
  pressureClass (immediateExitCollapseClass c)

immediateExitRepresentativePressure :
  CertifiedImmediateExitClass → Pressure
immediateExitRepresentativePressure c =
  embedPressureClass (immediateExitRepresentativePressureClass c)

immediateExitRepresentativeHighPressure :
  ∀ c →
  immediateExitRepresentativePressureClass c ≡ highPressure
immediateExitRepresentativeHighPressure c =
  pressureClass-explicit-immediateExit
    (immediateExitCollapseClass c)
    (immediateExitCollapseTime c)

immediateExitRepresentativePressureIsHigh :
  ∀ c →
  immediateExitRepresentativePressure c ≡ high
immediateExitRepresentativePressureIsHigh c
  rewrite immediateExitRepresentativeHighPressure c
  = embedPressureClass-high

record ImmediateExitRepresentativeComputation : Set₁ where
  field
    exitClass : CertifiedImmediateExitClass
    exitProof :
      collapseTime (immediateExitCollapseClass exitClass) ≡ immediateExit
    representative : ShiftContractState
    representativePrime : FactorVec
    summaryP2 : DefectOrbitSummary
    illegalAtP2 : Nat
    forcedStableOrbitAtP2 : Nat
    pressureTier : PressureClass
    genericPressureTier : Pressure
    pressureIsHigh : pressureTier ≡ highPressure
    genericPressureIsHigh : genericPressureTier ≡ high

immediateExitComputationAt :
  CertifiedImmediateExitClass → ImmediateExitRepresentativeComputation
immediateExitComputationAt c =
  record
    { exitClass = c
    ; exitProof = immediateExitCollapseTime c
    ; representative = immediateExitRepresentativeState c
    ; representativePrime = immediateExitRepresentativePrimeImage c
    ; summaryP2 = immediateExitRepresentativeOrbitSummaryP2 c
    ; illegalAtP2 = immediateExitRepresentativeIllegalCountP2 c
    ; forcedStableOrbitAtP2 =
        immediateExitRepresentativeForcedStableCountOrbitP2 c
    ; pressureTier = immediateExitRepresentativePressureClass c
    ; genericPressureTier = immediateExitRepresentativePressure c
    ; pressureIsHigh = immediateExitRepresentativeHighPressure c
    ; genericPressureIsHigh = immediateExitRepresentativePressureIsHigh c
    }

immediateExitRepresentativePressureSummary :
  CertifiedImmediateExitClass → DOCP.DefectPressureSummary
immediateExitRepresentativePressureSummary c =
  defectPressureSummaryAt (immediateExitCollapseClass c)

------------------------------------------------------------------------
-- Current exact `p2` computations.

immediateExitIllegalCountP2-explicitWidth2 :
  immediateExitRepresentativeIllegalCountP2 exitExplicitWidth2 ≡ 15
immediateExitIllegalCountP2-explicitWidth2 = refl

immediateExitIllegalCountP2-anchoredTrajectory :
  immediateExitRepresentativeIllegalCountP2 exitAnchoredTrajectory ≡ 15
immediateExitIllegalCountP2-anchoredTrajectory = refl

immediateExitIllegalCountP2-fullSupportCascade :
  immediateExitRepresentativeIllegalCountP2 exitFullSupportCascade ≡ 15
immediateExitIllegalCountP2-fullSupportCascade = refl

immediateExitForcedStableOrbitP2-explicitWidth2 :
  immediateExitRepresentativeForcedStableCountOrbitP2 exitExplicitWidth2 ≡ 15
immediateExitForcedStableOrbitP2-explicitWidth2 = refl

immediateExitForcedStableOrbitP2-anchoredTrajectory :
  immediateExitRepresentativeForcedStableCountOrbitP2 exitAnchoredTrajectory ≡ 15
immediateExitForcedStableOrbitP2-anchoredTrajectory = refl

immediateExitForcedStableOrbitP2-fullSupportCascade :
  immediateExitRepresentativeForcedStableCountOrbitP2 exitFullSupportCascade ≡ 15
immediateExitForcedStableOrbitP2-fullSupportCascade = refl
