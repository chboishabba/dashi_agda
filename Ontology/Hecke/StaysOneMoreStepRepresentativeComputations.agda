module Ontology.Hecke.StaysOneMoreStepRepresentativeComputations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; z≤n; s≤s)

open import DASHI.Pressure using (Pressure; low)
open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( GeneratorCollapseClass
    ; collapseTime
    ; collapseTime-denseComposed
    ; collapseTime-explicitWidth1
    ; collapseTime-explicitWidth3
    ; prefixClass
    ; staysOneMoreStep
    )
open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( CertifiedStayClass
    ; certifiedDenseComposed
    ; certifiedExplicitWidth1
    ; certifiedExplicitWidth3
    ; stayClassToGeneratorClass
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance
  using (ShiftContractState)
open import MonsterOntos using (p2)
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
    ; lowPressure
    ; pressureClass
    ; pressureClass-explicit-staysOneMoreStep
    )
open import Ontology.Hecke.PressureAdapter using
  ( embedPressureClass
  ; embedPressureClass-low
  )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries
  using (DefectOrbitSummary)

------------------------------------------------------------------------
-- Concrete evaluator surface for the current `staysOneMoreStep` classes.
--
-- This packages the strongest currently honest computations:
-- - the certified stay-classes on the closure side;
-- - the chosen live representative state on the Hecke bridge;
-- - the transported prime image and `p2` orbit summary; and
-- - the coarse pressure tier inherited from the collapse-time surface.

stayCollapseClass : CertifiedStayClass → GeneratorCollapseClass
stayCollapseClass c = prefixClass (stayClassToGeneratorClass c)

stayCollapseTime :
  (c : CertifiedStayClass) →
  collapseTime (stayCollapseClass c) ≡ staysOneMoreStep
stayCollapseTime certifiedExplicitWidth1 = collapseTime-explicitWidth1
stayCollapseTime certifiedExplicitWidth3 = collapseTime-explicitWidth3
stayCollapseTime certifiedDenseComposed = collapseTime-denseComposed

stayRepresentativeState : CertifiedStayClass → ShiftContractState
stayRepresentativeState c = representativeState (stayCollapseClass c)

stayRepresentativePrimeImage : CertifiedStayClass → FactorVec
stayRepresentativePrimeImage c = primeImage (stayCollapseClass c)

stayRepresentativeOrbitSummaryP2 :
  CertifiedStayClass → DefectOrbitSummary
stayRepresentativeOrbitSummaryP2 c =
  orbitSummaryP2 (stayCollapseClass c)

stayRepresentativeIllegalCountP2 : CertifiedStayClass → Nat
stayRepresentativeIllegalCountP2 c =
  illegalCountP2 (stayCollapseClass c)

stayRepresentativeForcedStableCountOrbitP2 :
  CertifiedStayClass → Nat
stayRepresentativeForcedStableCountOrbitP2 c =
  forcedStableCountOrbitP2 (stayCollapseClass c)

stayRepresentativePressureClass :
  CertifiedStayClass → PressureClass
stayRepresentativePressureClass c =
  pressureClass (stayCollapseClass c)

stayRepresentativePressure :
  CertifiedStayClass → Pressure
stayRepresentativePressure c =
  embedPressureClass (stayRepresentativePressureClass c)

stayRepresentativeLowPressure :
  ∀ c →
  stayRepresentativePressureClass c ≡ lowPressure
stayRepresentativeLowPressure c =
  pressureClass-explicit-staysOneMoreStep
    (stayCollapseClass c)
    (stayCollapseTime c)

stayRepresentativePressureIsLow :
  ∀ c →
  stayRepresentativePressure c ≡ low
stayRepresentativePressureIsLow c
  rewrite stayRepresentativeLowPressure c
  = embedPressureClass-low

record StaysOneMoreStepRepresentativeComputation : Set₁ where
  field
    stayClass : CertifiedStayClass
    stayProof :
      collapseTime (stayCollapseClass stayClass) ≡ staysOneMoreStep
    representative : ShiftContractState
    representativePrime : FactorVec
    summaryP2 : DefectOrbitSummary
    illegalAtP2 : Nat
    forcedStableOrbitAtP2 : Nat
    pressureTier : PressureClass
    genericPressureTier : Pressure
    pressureIsLow : pressureTier ≡ lowPressure
    genericPressureIsLow : genericPressureTier ≡ low

computationAt :
  CertifiedStayClass → StaysOneMoreStepRepresentativeComputation
computationAt c =
  record
    { stayClass = c
    ; stayProof = stayCollapseTime c
    ; representative = stayRepresentativeState c
    ; representativePrime = stayRepresentativePrimeImage c
    ; summaryP2 = stayRepresentativeOrbitSummaryP2 c
    ; illegalAtP2 = stayRepresentativeIllegalCountP2 c
    ; forcedStableOrbitAtP2 =
        stayRepresentativeForcedStableCountOrbitP2 c
    ; pressureTier = stayRepresentativePressureClass c
    ; genericPressureTier = stayRepresentativePressure c
    ; pressureIsLow = stayRepresentativeLowPressure c
    ; genericPressureIsLow = stayRepresentativePressureIsLow c
    }

stayRepresentativePressureSummary :
  CertifiedStayClass → DOCP.DefectPressureSummary
stayRepresentativePressureSummary c =
  defectPressureSummaryAt (stayCollapseClass c)

------------------------------------------------------------------------
-- Current exact `p2` computations.

stayForcedStableOrbitP2-explicitWidth1 :
  stayRepresentativeForcedStableCountOrbitP2 certifiedExplicitWidth1 ≡ 2
stayForcedStableOrbitP2-explicitWidth1 = refl

stayForcedStableOrbitP2-explicitWidth3 :
  stayRepresentativeForcedStableCountOrbitP2 certifiedExplicitWidth3 ≡ 15
stayForcedStableOrbitP2-explicitWidth3 = refl

stayForcedStableOrbitP2-denseComposed :
  stayRepresentativeForcedStableCountOrbitP2 certifiedDenseComposed ≡ 15
stayForcedStableOrbitP2-denseComposed = refl

------------------------------------------------------------------------
-- Honest strictness on the certified stay slice.
--
-- `explicitWidth1` is the only current stay representative whose forced
-- stable count sits strictly below the saturated `15` plateau.

stayForcedStableOrbitP2-explicitWidth1<explicitWidth3 :
  stayRepresentativeForcedStableCountOrbitP2 certifiedExplicitWidth1 <
  stayRepresentativeForcedStableCountOrbitP2 certifiedExplicitWidth3
stayForcedStableOrbitP2-explicitWidth1<explicitWidth3
  rewrite stayForcedStableOrbitP2-explicitWidth1
        | stayForcedStableOrbitP2-explicitWidth3
  = s≤s (s≤s (s≤s z≤n))
