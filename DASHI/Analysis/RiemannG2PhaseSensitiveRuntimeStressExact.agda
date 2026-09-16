module DASHI.Analysis.RiemannG2PhaseSensitiveRuntimeStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2PhaseSensitiveRuntimeDiagnosticExact as Initial

------------------------------------------------------------------------
-- BROADER PHASE-SENSITIVE RUNTIME STRESS
--
-- Extend the initial 18-cell diagnostic across three target zeros, three
-- Gaussian widths, two horizontal-displacement parameters and four neighbouring
-- target-relative gaps.  The purpose remains mechanism stress only.
--
-- No Gaussian member is identified with the final universal pole-quotient
-- taper.  Critical-line zeta ordinates are phase-gap inputs only and do not
-- instantiate an off-line contradiction case.
------------------------------------------------------------------------

initialBoundary : Initial.PhaseSensitiveRuntimeDiagnosticBoundary
initialBoundary = Initial.canonicalPhaseSensitiveRuntimeDiagnosticBoundary

record PhaseSensitiveRuntimeStressReceipt : Set where
  constructor phase-sensitive-runtime-stress-receipt
  field
    csvPath : String
    jsonPath : String
    jsonSHA256 : String
    targetCount : Nat
    gaussianWidthCount : Nat
    horizontalDisplacementCount : Nat
    neighbourOffsetsPerTarget : Nat
    testedCells : Nat
    allOneSidedBoundsHeld : Bool
    minimumPhaseOverCoarsePermille : Nat
    medianPhaseOverCoarsePermille : Nat
    maximumPhaseOverCoarsePermille : Nat
    multipleTargetZerosChecked : Bool
    multipleDiagnosticTaperWidthsChecked : Bool
    multipleHorizontalDisplacementsChecked : Bool
    sameObjectUniversalPoleQuotientTaperUsed : Bool
    authenticatedOffLineZeroCarrierUsed : Bool
    exactLocalRuntimeExecuted : Bool
open PhaseSensitiveRuntimeStressReceipt public

currentPhaseSensitiveRuntimeStressReceipt : PhaseSensitiveRuntimeStressReceipt
currentPhaseSensitiveRuntimeStressReceipt =
  phase-sensitive-runtime-stress-receipt
    "/mnt/data/RH_phase_sensitive_stress_72.csv"
    "/mnt/data/riemann_g2_phase_sensitive_stress_72.json"
    "d9b497f4d37e7a156be4f8e5d5f262bce5cde0435f001c2b3efe72a8e48783aa"
    3 3 2 4 72
    true
    318 373 905
    true true true
    false false true

record PhaseSensitiveRuntimeStressBoundary : Set where
  constructor phase-sensitive-runtime-stress-boundary
  field
    initialPhaseSensitiveMechanismInherited : Bool
    broaderTargetStressExecuted : Bool
    broaderTaperWidthStressExecuted : Bool
    broaderHorizontalDisplacementStressExecuted : Bool
    allSeventyTwoOneSidedBoundsHeld : Bool
    phaseSensitiveUpperBelowCoarseEnvelopeThroughoutStress : Bool
    stressInstantiatesFinalUniversalPoleQuotientTaper : Bool
    stressInstantiatesAuthenticatedOffLineCarrier : Bool
    stressPaysSameObjectWeld : Bool
    stressPaysStrictNearFarMargin : Bool
    stressProvesRH : Bool
open PhaseSensitiveRuntimeStressBoundary public

canonicalPhaseSensitiveRuntimeStressBoundary : PhaseSensitiveRuntimeStressBoundary
canonicalPhaseSensitiveRuntimeStressBoundary =
  phase-sensitive-runtime-stress-boundary
    true true true true true true
    false false false false false

data PhaseSensitiveRuntimeStressResidual : Set where
  obtainConcreteFinalUniversalPoleQuotientTaperEvaluation : PhaseSensitiveRuntimeStressResidual
  replaceDiagnosticTaperBySameObjectFinalTaper : PhaseSensitiveRuntimeStressResidual
  provePointwisePhaseSensitiveMajorantOnFinalCarrier : PhaseSensitiveRuntimeStressResidual
  certifyCellIntegralUppers : PhaseSensitiveRuntimeStressResidual
  aggregateExactFiniteNearUpper : PhaseSensitiveRuntimeStressResidual
  compareAgainstOwnedComplementBudget : PhaseSensitiveRuntimeStressResidual

firstPhaseSensitiveRuntimeStressResidual : PhaseSensitiveRuntimeStressResidual
firstPhaseSensitiveRuntimeStressResidual = obtainConcreteFinalUniversalPoleQuotientTaperEvaluation
