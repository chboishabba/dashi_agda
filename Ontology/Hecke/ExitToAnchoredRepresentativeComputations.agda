module Ontology.Hecke.ExitToAnchoredRepresentativeComputations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Pressure using (Pressure; medium)
open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( GeneratorCollapseClass
    ; collapseTime
    ; collapseTime-balancedComposed
    ; collapseTime-balancedCycle
    ; exitToAnchored
    ; prefixClass
    )
open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( CertifiedExitToAnchoredClass
    ; certifiedBalancedComposed
    ; certifiedBalancedCycle
    ; exitToAnchoredClassToGeneratorClass
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
    ; mediumPressure
    ; pressureClass
    ; pressureClass-explicit-exitToAnchored
    )
open import Ontology.Hecke.PressureAdapter using
  ( embedPressureClass
  ; embedPressureClass-medium
  )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries
  using (DefectOrbitSummary)

------------------------------------------------------------------------
-- Concrete evaluator surface for the current `exitToAnchored` classes.

exitToAnchoredCollapseClass :
  CertifiedExitToAnchoredClass → GeneratorCollapseClass
exitToAnchoredCollapseClass c =
  prefixClass (exitToAnchoredClassToGeneratorClass c)

exitToAnchoredCollapseTime :
  (c : CertifiedExitToAnchoredClass) →
  collapseTime (exitToAnchoredCollapseClass c) ≡ exitToAnchored
exitToAnchoredCollapseTime certifiedBalancedCycle =
  collapseTime-balancedCycle
exitToAnchoredCollapseTime certifiedBalancedComposed =
  collapseTime-balancedComposed

exitToAnchoredRepresentativeState :
  CertifiedExitToAnchoredClass → ShiftContractState
exitToAnchoredRepresentativeState c =
  representativeState (exitToAnchoredCollapseClass c)

exitToAnchoredRepresentativePrimeImage :
  CertifiedExitToAnchoredClass → FactorVec
exitToAnchoredRepresentativePrimeImage c =
  primeImage (exitToAnchoredCollapseClass c)

exitToAnchoredRepresentativeOrbitSummaryP2 :
  CertifiedExitToAnchoredClass → DefectOrbitSummary
exitToAnchoredRepresentativeOrbitSummaryP2 c =
  orbitSummaryP2 (exitToAnchoredCollapseClass c)

exitToAnchoredRepresentativeIllegalCountP2 :
  CertifiedExitToAnchoredClass → Nat
exitToAnchoredRepresentativeIllegalCountP2 c =
  illegalCountP2 (exitToAnchoredCollapseClass c)

exitToAnchoredRepresentativeForcedStableCountOrbitP2 :
  CertifiedExitToAnchoredClass → Nat
exitToAnchoredRepresentativeForcedStableCountOrbitP2 c =
  forcedStableCountOrbitP2 (exitToAnchoredCollapseClass c)

exitToAnchoredRepresentativePressureClass :
  CertifiedExitToAnchoredClass → PressureClass
exitToAnchoredRepresentativePressureClass c =
  pressureClass (exitToAnchoredCollapseClass c)

exitToAnchoredRepresentativePressure :
  CertifiedExitToAnchoredClass → Pressure
exitToAnchoredRepresentativePressure c =
  embedPressureClass (exitToAnchoredRepresentativePressureClass c)

exitToAnchoredRepresentativeMediumPressure :
  ∀ c →
  exitToAnchoredRepresentativePressureClass c ≡ mediumPressure
exitToAnchoredRepresentativeMediumPressure c =
  pressureClass-explicit-exitToAnchored
    (exitToAnchoredCollapseClass c)
    (exitToAnchoredCollapseTime c)

exitToAnchoredRepresentativePressureIsMedium :
  ∀ c →
  exitToAnchoredRepresentativePressure c ≡ medium
exitToAnchoredRepresentativePressureIsMedium c
  rewrite exitToAnchoredRepresentativeMediumPressure c
  = embedPressureClass-medium

record ExitToAnchoredRepresentativeComputation : Set₁ where
  field
    exitClass : CertifiedExitToAnchoredClass
    exitProof :
      collapseTime (exitToAnchoredCollapseClass exitClass) ≡ exitToAnchored
    representative : ShiftContractState
    representativePrime : FactorVec
    summaryP2 : DefectOrbitSummary
    illegalAtP2 : Nat
    forcedStableOrbitAtP2 : Nat
    pressureTier : PressureClass
    genericPressureTier : Pressure
    pressureIsMedium : pressureTier ≡ mediumPressure
    genericPressureIsMedium : genericPressureTier ≡ medium

exitToAnchoredComputationAt :
  CertifiedExitToAnchoredClass → ExitToAnchoredRepresentativeComputation
exitToAnchoredComputationAt c =
  record
    { exitClass = c
    ; exitProof = exitToAnchoredCollapseTime c
    ; representative = exitToAnchoredRepresentativeState c
    ; representativePrime = exitToAnchoredRepresentativePrimeImage c
    ; summaryP2 = exitToAnchoredRepresentativeOrbitSummaryP2 c
    ; illegalAtP2 = exitToAnchoredRepresentativeIllegalCountP2 c
    ; forcedStableOrbitAtP2 =
        exitToAnchoredRepresentativeForcedStableCountOrbitP2 c
    ; pressureTier = exitToAnchoredRepresentativePressureClass c
    ; genericPressureTier = exitToAnchoredRepresentativePressure c
    ; pressureIsMedium = exitToAnchoredRepresentativeMediumPressure c
    ; genericPressureIsMedium = exitToAnchoredRepresentativePressureIsMedium c
    }

exitToAnchoredRepresentativePressureSummary :
  CertifiedExitToAnchoredClass → DOCP.DefectPressureSummary
exitToAnchoredRepresentativePressureSummary c =
  defectPressureSummaryAt (exitToAnchoredCollapseClass c)

------------------------------------------------------------------------
-- Current exact `p2` computations.

exitToAnchoredIllegalCountP2-balancedCycle :
  exitToAnchoredRepresentativeIllegalCountP2 certifiedBalancedCycle ≡ 15
exitToAnchoredIllegalCountP2-balancedCycle = refl

exitToAnchoredIllegalCountP2-balancedComposed :
  exitToAnchoredRepresentativeIllegalCountP2 certifiedBalancedComposed ≡ 15
exitToAnchoredIllegalCountP2-balancedComposed = refl

exitToAnchoredForcedStableOrbitP2-balancedCycle :
  exitToAnchoredRepresentativeForcedStableCountOrbitP2 certifiedBalancedCycle ≡ 15
exitToAnchoredForcedStableOrbitP2-balancedCycle = refl

exitToAnchoredForcedStableOrbitP2-balancedComposed :
  exitToAnchoredRepresentativeForcedStableCountOrbitP2 certifiedBalancedComposed ≡ 15
exitToAnchoredForcedStableOrbitP2-balancedComposed = refl
