module DASHI.Reasoning.LogicalConsequenceHistoryResidueExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path

------------------------------------------------------------------------
-- FINITE RECONVERGENCE FIXTURE
--
-- Two epistemic histories reach the same visible final assertion.  The
-- empirical route has passed through an empirical-promotion/design-discharge
-- gate and deposits a persistent authority residue; the purely logical route
-- does not.  Final syntax therefore cannot reconstruct later admissibility.
------------------------------------------------------------------------

data DerivationState : Set where
  sourceState
  logicalIntermediate
  empiricalIntermediate
  reconvergedLogical
  reconvergedEmpirical
  : DerivationState

data DerivationTransition : DerivationState → DerivationState → Set where
  sourceToLogical : DerivationTransition sourceState logicalIntermediate
  logicalToReconverged : DerivationTransition logicalIntermediate reconvergedLogical
  sourceToEmpirical : DerivationTransition sourceState empiricalIntermediate
  empiricalToReconverged : DerivationTransition empiricalIntermediate reconvergedEmpirical

residue : DerivationState → Trajectory.ResidueFlag
residue sourceState = Trajectory.residueAbsent
residue logicalIntermediate = Trajectory.residueAbsent
residue empiricalIntermediate = Trajectory.residuePresent
residue reconvergedLogical = Trajectory.residueAbsent
residue reconvergedEmpirical = Trajectory.residuePresent

noEmpiricalResidueErasure : Trajectory.NoResidueErasure DerivationTransition residue
noEmpiricalResidueErasure sourceToLogical ()
noEmpiricalResidueErasure logicalToReconverged ()
noEmpiricalResidueErasure sourceToEmpirical ()
noEmpiricalResidueErasure empiricalToReconverged present = present

logicalHistory :
  Trajectory.Trace DerivationTransition sourceState reconvergedLogical
logicalHistory =
  Trajectory.traceStep sourceToLogical
    (Trajectory.traceStep logicalToReconverged Trajectory.traceRefl)

empiricalHistory :
  Trajectory.Trace DerivationTransition sourceState reconvergedEmpirical
empiricalHistory =
  Trajectory.traceStep sourceToEmpirical
    (Trajectory.traceStep empiricalToReconverged Trajectory.traceRefl)

empiricalRouteDepositsResidue :
  Trajectory.ResidueDeposition DerivationTransition residue
empiricalRouteDepositsResidue = Trajectory.residueDeposition
  sourceState
  reconvergedEmpirical
  empiricalHistory
  refl
  refl

empiricalResiduePersists :
  residue reconvergedEmpirical ≡ Trajectory.residuePresent
empiricalResiduePersists =
  Trajectory.tracePreservesPresentResidue
    noEmpiricalResidueErasure
    (Trajectory.traceStep empiricalToReconverged Trajectory.traceRefl)
    refl

------------------------------------------------------------------------
-- Coarse final assertion observation.
------------------------------------------------------------------------

data VisibleAssertion : Set where
  sameFinalAssertion : VisibleAssertion

observeFinal : DerivationState → VisibleAssertion
observeFinal _ = sameFinalAssertion

data DerivationPattern : Set where
  logicOnlyPattern empiricalQualifiedPattern : DerivationPattern

patternOf : DerivationState → DerivationPattern
patternOf sourceState = logicOnlyPattern
patternOf logicalIntermediate = logicOnlyPattern
patternOf empiricalIntermediate = empiricalQualifiedPattern
patternOf reconvergedLogical = logicOnlyPattern
patternOf reconvergedEmpirical = empiricalQualifiedPattern

data LaterAdmission : Set where
  requiresFreshEvidence
  empiricalContinuationAdmissible
  : LaterAdmission

laterAdmission : DerivationState → LaterAdmission
laterAdmission sourceState = requiresFreshEvidence
laterAdmission logicalIntermediate = requiresFreshEvidence
laterAdmission empiricalIntermediate = empiricalContinuationAdmissible
laterAdmission reconvergedLogical = requiresFreshEvidence
laterAdmission reconvergedEmpirical = empiricalContinuationAdmissible

choiceSurface : History.HistoryConditionedChoiceSurface
choiceSurface = record
  { History = DerivationState
  ; Observation = VisibleAssertion
  ; Pattern = DerivationPattern
  ; Choice = LaterAdmission
  ; observe = observeFinal
  ; patternOf = patternOf
  ; choose = laterAdmission
  ; historyReading =
      "Identical final assertion syntax may retain different empirical authority histories and therefore different later admission."
  }

sameAssertionDifferentAdmission :
  History.DistinctHistoriesSameObservationDifferentChoice choiceSurface
sameAssertionDifferentAdmission = record
  { leftHistory = reconvergedLogical
  ; rightHistory = reconvergedEmpirical
  ; historiesDistinct = λ ()
  ; samePresentObservation = refl
  ; choicesDiffer = λ ()
  }

laterAdmissionCannotDescendThroughFinalAssertion :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    (History.observe choiceSurface)
    (History.choose choiceSurface) →
  ⊥
laterAdmissionCannotDescendThroughFinalAssertion =
  History.historySensitiveChoiceCannotDescendThroughPresentObservation
    sameAssertionDifferentAdmission

------------------------------------------------------------------------
-- Future cone form: same final assertion, different permitted continuation.
------------------------------------------------------------------------

data FutureConeCode : Set where
  logicOnlyCone empiricalQualifiedCone : FutureConeCode

futureCone : DerivationState → FutureConeCode
futureCone sourceState = logicOnlyCone
futureCone logicalIntermediate = logicOnlyCone
futureCone empiricalIntermediate = empiricalQualifiedCone
futureCone reconvergedLogical = logicOnlyCone
futureCone reconvergedEmpirical = empiricalQualifiedCone

futureSurface : History.HistoryConditionedFutureConeSurface
futureSurface = record
  { FutureHistory = DerivationState
  ; FutureObservation = VisibleAssertion
  ; FutureConeCode = FutureConeCode
  ; observeFutureHistory = observeFinal
  ; futureCone = futureCone
  ; futureReading =
      "The same final assertion can expose different continuation cones because empirical authority was deposited along only one derivation path."
  }

sameAssertionDifferentFutureCone :
  History.SameObservationDifferentFutureCone futureSurface
sameAssertionDifferentFutureCone = record
  { futureLeftHistory = reconvergedLogical
  ; futureRightHistory = reconvergedEmpirical
  ; futureSameObservation = refl
  ; futureConesDiffer = λ ()
  }

record LogicalConsequenceHistoryBoundary : Set where
  constructor logicalConsequenceHistoryBoundary
  field
    sameFinalAssertionImpliesSameDerivationHistory : Bool
    sameFinalAssertionImpliesSameDerivationHistoryIsFalse :
      sameFinalAssertionImpliesSameDerivationHistory ≡ false
    empiricalPromotionMayDepositPersistentResidue : Bool
    empiricalPromotionMayDepositPersistentResidueIsTrue :
      empiricalPromotionMayDepositPersistentResidue ≡ true
    sameFinalAssertionImpliesSameLaterAdmission : Bool
    sameFinalAssertionImpliesSameLaterAdmissionIsFalse :
      sameFinalAssertionImpliesSameLaterAdmission ≡ false
    sameFinalAssertionImpliesSameFutureCone : Bool
    sameFinalAssertionImpliesSameFutureConeIsFalse :
      sameFinalAssertionImpliesSameFutureCone ≡ false

canonicalLogicalConsequenceHistoryBoundary :
  LogicalConsequenceHistoryBoundary
canonicalLogicalConsequenceHistoryBoundary =
  logicalConsequenceHistoryBoundary false refl true refl false refl false refl
