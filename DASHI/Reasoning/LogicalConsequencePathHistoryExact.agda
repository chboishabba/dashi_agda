module DASHI.Reasoning.LogicalConsequencePathHistoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- PATH-INDEXED EPISTEMIC CONSEQUENCE HISTORY
--
-- A final formula is not a sufficient description of how that formula became
-- available. Parser/semantic resolution, logical deduction, empirical
-- promotion, residual refinement and design discharge are distinct edge kinds.
-- Two paths may reconverge at the same final assertion while retaining
-- different authority and different admissible continuation cones.
------------------------------------------------------------------------

data ConsequenceStage : Set where
  sourceStage
  semanticCandidateStage
  reviewedPNFStage
  logicalClosureStage
  empiricalDemandStage
  designDischargeStage
  logicalArrivalStage
  evidenceQualifiedArrivalStage
  : ConsequenceStage

data ConsequenceEdgeKind : Set where
  parserCandidateEdge
  semanticResolutionEdge
  logicalEntailmentEdge
  empiricalPromotionEdge
  residualRefinementEdge
  designDischargeEdge
  : ConsequenceEdgeKind

data ConsequenceStep : ConsequenceStage → ConsequenceStage → Set where
  parserToCandidate : ConsequenceStep sourceStage semanticCandidateStage
  candidateToReviewed : ConsequenceStep semanticCandidateStage reviewedPNFStage
  reviewedToLogical : ConsequenceStep reviewedPNFStage logicalClosureStage
  logicalToArrival : ConsequenceStep logicalClosureStage logicalArrivalStage
  logicalToEmpiricalDemand : ConsequenceStep logicalClosureStage empiricalDemandStage
  demandToDesignDischarge : ConsequenceStep empiricalDemandStage designDischargeStage
  designToEvidenceArrival : ConsequenceStep designDischargeStage evidenceQualifiedArrivalStage

stepKind : ∀ {x y} → ConsequenceStep x y → ConsequenceEdgeKind
stepKind parserToCandidate = parserCandidateEdge
stepKind candidateToReviewed = semanticResolutionEdge
stepKind reviewedToLogical = logicalEntailmentEdge
stepKind logicalToArrival = logicalEntailmentEdge
stepKind logicalToEmpiricalDemand = empiricalPromotionEdge
stepKind demandToDesignDischarge = residualRefinementEdge
stepKind designToEvidenceArrival = designDischargeEdge

logicalArrivalPath :
  Trajectory.Trace ConsequenceStep sourceStage logicalArrivalStage
logicalArrivalPath =
  Trajectory.traceStep parserToCandidate
    (Trajectory.traceStep candidateToReviewed
      (Trajectory.traceStep reviewedToLogical
        (Trajectory.traceStep logicalToArrival Trajectory.traceRefl)))

evidenceQualifiedArrivalPath :
  Trajectory.Trace ConsequenceStep sourceStage evidenceQualifiedArrivalStage
evidenceQualifiedArrivalPath =
  Trajectory.traceStep parserToCandidate
    (Trajectory.traceStep candidateToReviewed
      (Trajectory.traceStep reviewedToLogical
        (Trajectory.traceStep logicalToEmpiricalDemand
          (Trajectory.traceStep demandToDesignDischarge
            (Trajectory.traceStep designToEvidenceArrival Trajectory.traceRefl)))))

------------------------------------------------------------------------
-- Same final assertion, different fine arrival state.
------------------------------------------------------------------------

data FinalAssertionObservation : Set where
  sameFinalFormula : FinalAssertionObservation
  notFinalYet : FinalAssertionObservation

observeStage : ConsequenceStage → FinalAssertionObservation
observeStage logicalArrivalStage = sameFinalFormula
observeStage evidenceQualifiedArrivalStage = sameFinalFormula
observeStage _ = notFinalYet

sameFinalAssertionObservation :
  observeStage logicalArrivalStage ≡ observeStage evidenceQualifiedArrivalStage
sameFinalAssertionObservation = refl

------------------------------------------------------------------------
-- Empirical qualification is path-deposited residue.
------------------------------------------------------------------------

empiricalQualificationResidue : ConsequenceStage → Trajectory.ResidueFlag
empiricalQualificationResidue evidenceQualifiedArrivalStage = Trajectory.residuePresent
empiricalQualificationResidue designDischargeStage = Trajectory.residuePresent
empiricalQualificationResidue _ = Trajectory.residueAbsent

noEmpiricalQualificationErasure :
  Trajectory.NoResidueErasure ConsequenceStep empiricalQualificationResidue
noEmpiricalQualificationErasure designToEvidenceArrival refl = refl

qualificationDeposition :
  Trajectory.ResidueDeposition ConsequenceStep empiricalQualificationResidue
qualificationDeposition =
  Trajectory.residueDeposition
    empiricalDemandStage
    evidenceQualifiedArrivalStage
    (Trajectory.traceStep demandToDesignDischarge
      (Trajectory.traceStep designToEvidenceArrival Trajectory.traceRefl))
    refl
    refl

qualificationPersistsAlongTrace :
  ∀ {x y} →
  Trajectory.Trace ConsequenceStep x y →
  empiricalQualificationResidue x ≡ Trajectory.residuePresent →
  empiricalQualificationResidue y ≡ Trajectory.residuePresent
qualificationPersistsAlongTrace =
  Trajectory.tracePreservesPresentResidue noEmpiricalQualificationErasure

------------------------------------------------------------------------
-- Coarse final-formula observation cannot reconstruct qualification residue.
------------------------------------------------------------------------

finalFormulaNeedsResidueRefinement :
  Observer.StrictRefinement
    observeStage
    (Trajectory.residueRefinedObserver observeStage empiricalQualificationResidue)
finalFormulaNeedsResidueRefinement =
  Trajectory.coarseCollisionAcrossResidueGivesStrictRefinement
    observeStage
    empiricalQualificationResidue
    logicalArrivalStage
    evidenceQualifiedArrivalStage
    refl refl refl

finalFormulaCannotRecoverQualificationResidue :
  Trajectory.ResidueDescendsThrough observeStage empiricalQualificationResidue → ⊥
finalFormulaCannotRecoverQualificationResidue =
  Trajectory.coarseCollisionAcrossResidueBlocksDescent refl refl refl

------------------------------------------------------------------------
-- History-conditioned use and continuation.
------------------------------------------------------------------------

data DerivationHistory : Set where
  logicalOnlyHistory
  evidenceQualifiedHistory
  : DerivationHistory

data DerivationPattern : Set where
  pureLogicPattern
  empiricalQualificationPattern
  : DerivationPattern

data ConsequenceUse : Set where
  useAsLogicalConsequence
  useAsEvidenceQualifiedClaim
  : ConsequenceUse

data ConsequenceFutureCone : Set where
  logicOnlyCone
  evidenceQualifiedCone
  : ConsequenceFutureCone

data DerivationAuthority : Set where
  logicalAuthority
  empiricallyQualifiedAuthority
  : DerivationAuthority

historyObservation : DerivationHistory → FinalAssertionObservation
historyObservation _ = sameFinalFormula

historyPattern : DerivationHistory → DerivationPattern
historyPattern logicalOnlyHistory = pureLogicPattern
historyPattern evidenceQualifiedHistory = empiricalQualificationPattern

historyUse : DerivationHistory → ConsequenceUse
historyUse logicalOnlyHistory = useAsLogicalConsequence
historyUse evidenceQualifiedHistory = useAsEvidenceQualifiedClaim

historyAuthority : DerivationHistory → DerivationAuthority
historyAuthority logicalOnlyHistory = logicalAuthority
historyAuthority evidenceQualifiedHistory = empiricallyQualifiedAuthority

consequenceChoiceSurface : History.HistoryConditionedChoiceSurface
consequenceChoiceSurface =
  record
    { History = DerivationHistory
    ; Observation = FinalAssertionObservation
    ; Pattern = DerivationPattern
    ; Choice = ConsequenceUse
    ; observe = historyObservation
    ; patternOf = historyPattern
    ; choose = historyUse
    ; historyReading =
        "The same final formula can have a pure-logical arrival history or an empirically qualified arrival history; downstream use remains history-sensitive."
    }

sameFormulaDifferentUseWitness :
  History.DistinctHistoriesSameObservationDifferentChoice consequenceChoiceSurface
sameFormulaDifferentUseWitness =
  record
    { leftHistory = logicalOnlyHistory
    ; rightHistory = evidenceQualifiedHistory
    ; historiesDistinct = λ ()
    ; samePresentObservation = refl
    ; choicesDiffer = λ ()
    }

finalFormulaDoesNotDeterminePermittedUse :
  NonFactor.FactorsThrough
    (History.observe consequenceChoiceSurface)
    (History.choose consequenceChoiceSurface) →
  ⊥
finalFormulaDoesNotDeterminePermittedUse =
  History.historySensitiveChoiceCannotDescendThroughPresentObservation
    sameFormulaDifferentUseWitness

historyFutureCone : DerivationHistory → ConsequenceFutureCone
historyFutureCone logicalOnlyHistory = logicOnlyCone
historyFutureCone evidenceQualifiedHistory = evidenceQualifiedCone

consequenceFutureConeSurface : History.HistoryConditionedFutureConeSurface
consequenceFutureConeSurface =
  record
    { FutureHistory = DerivationHistory
    ; FutureObservation = FinalAssertionObservation
    ; FutureConeCode = ConsequenceFutureCone
    ; observeFutureHistory = historyObservation
    ; futureCone = historyFutureCone
    ; futureReading =
        "Identical final formula observations can expose different downstream claim-use cones because empirical qualification is path-dependent."
    }

sameFormulaDifferentFutureConeWitness :
  History.SameObservationDifferentFutureCone consequenceFutureConeSurface
sameFormulaDifferentFutureConeWitness =
  record
    { futureLeftHistory = logicalOnlyHistory
    ; futureRightHistory = evidenceQualifiedHistory
    ; futureSameObservation = refl
    ; futureConesDiffer = λ ()
    }

finalFormulaDoesNotDetermineFutureCone :
  NonFactor.FactorsThrough
    (History.observeFutureHistory consequenceFutureConeSurface)
    (History.futureCone consequenceFutureConeSurface) →
  ⊥
finalFormulaDoesNotDetermineFutureCone =
  History.futureConeCannotDescendThroughPresentObservation
    sameFormulaDifferentFutureConeWitness

sameFormulaDifferentAuthority :
  historyAuthority logicalOnlyHistory
  ≡ historyAuthority evidenceQualifiedHistory → ⊥
sameFormulaDifferentAuthority ()

record LogicalConsequencePathHistoryBoundary : Set where
  constructor logicalConsequencePathHistoryBoundary
  field
    finalFormulaDeterminesDerivationPath : Bool
    finalFormulaDeterminesDerivationPathIsFalse :
      finalFormulaDeterminesDerivationPath ≡ false
    sameFormulaImpliesSameAuthority : Bool
    sameFormulaImpliesSameAuthorityIsFalse :
      sameFormulaImpliesSameAuthority ≡ false
    empiricalQualificationCanBePathResidue : Bool
    empiricalQualificationCanBePathResidueIsTrue :
      empiricalQualificationCanBePathResidue ≡ true
    sameFormulaImpliesSameFutureCone : Bool
    sameFormulaImpliesSameFutureConeIsFalse :
      sameFormulaImpliesSameFutureCone ≡ false
    edgeKindsRemainFirstClass : Bool
    edgeKindsRemainFirstClassIsTrue :
      edgeKindsRemainFirstClass ≡ true

canonicalLogicalConsequencePathHistoryBoundary : LogicalConsequencePathHistoryBoundary
canonicalLogicalConsequencePathHistoryBoundary =
  logicalConsequencePathHistoryBoundary
    false refl
    false refl
    true refl
    false refl
    true refl
