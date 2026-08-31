module DASHI.Governance.SexedHistoricalBinaryTernaryDialecticExact where

------------------------------------------------------------------------
-- BINARY / TERNARY DIALECTIC BRIDGE FOR HISTORICAL CO-CONSTITUTION
--
-- Binary logical contradiction, dialectical counterposition, and the ternary
-- epistemic disposition {-1,0,+1} remain separately typed.
--
-- In particular:
--   unresolved != refuted
--   counterposition != logical negation
--   binary forcing loses information
--   same coarse two-pole coding != same fine historical state
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Ontology.EpistemicTrit as Trit
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Dialectic
import DASHI.Governance.SexedHistoricalDialecticalOrderHolonomyAnalogueExact as Order
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats

------------------------------------------------------------------------
-- Three distinct semantic roles.
------------------------------------------------------------------------

data HistoricalEvaluationMode : Set where
  binaryLogicalEvaluation
  ternaryEpistemicEvaluation
  dialecticalConstructionEvaluation
  : HistoricalEvaluationMode

binaryModeNotTernaryMode :
  binaryLogicalEvaluation ≡ ternaryEpistemicEvaluation → ⊥
binaryModeNotTernaryMode ()

binaryModeNotDialecticalMode :
  binaryLogicalEvaluation ≡ dialecticalConstructionEvaluation → ⊥
binaryModeNotDialecticalMode ()

ternaryModeNotDialecticalMode :
  ternaryEpistemicEvaluation ≡ dialecticalConstructionEvaluation → ⊥
ternaryModeNotDialecticalMode ()

------------------------------------------------------------------------
-- Canonical ternary rule is inherited, not rebuilt.
------------------------------------------------------------------------

neutralHistoricalEvidenceRefines :
  Suspension.disposition Suspension.neutralEvidence
  ≡ Suspension.suspendAndRefine
neutralHistoricalEvidenceRefines = Suspension.neutralMeansSuspendAndRefine

neutralHistoricalEvidenceIsNotReject :
  Suspension.disposition Suspension.neutralEvidence
  ≡ Suspension.disposition Suspension.negativeEvidence → ⊥
neutralHistoricalEvidenceIsNotReject eq =
  Suspension.negativeIsNotNeutral (sym eq)

neutralHistoricalEvidenceIsNotAccept :
  Suspension.disposition Suspension.neutralEvidence
  ≡ Suspension.disposition Suspension.positiveEvidence → ⊥
neutralHistoricalEvidenceIsNotAccept eq =
  Suspension.positiveIsNotNeutral (sym eq)

------------------------------------------------------------------------
-- Binary forcing is explicitly information-losing.
------------------------------------------------------------------------

rejectForcingCollidesUnresolvedWithContradicted :
  Trit.forceUnresolvedToReject Trit.unresolved
  ≡ Trit.forceUnresolvedToReject Trit.contradicted
rejectForcingCollidesUnresolvedWithContradicted = Trit.rejectPolicyCollision

acceptForcingCollidesUnresolvedWithSupported :
  Trit.forceUnresolvedToAccept Trit.unresolved
  ≡ Trit.forceUnresolvedToAccept Trit.supported
acceptForcingCollidesUnresolvedWithSupported = Trit.acceptPolicyCollision

------------------------------------------------------------------------
-- Dialectical opposition remains distinct from logical negation.
------------------------------------------------------------------------

constructedCounterpositionIsNotLogicalNegation :
  Dialectic.constructedCounterposition ≡ Dialectic.logicalNegation → ⊥
constructedCounterpositionIsNotLogicalNegation = Dialectic.counterposition≢negation

historicalContextDifferenceDoesNotManufactureContradiction :
  ¬ (Dialectic.HereThereReports → Dialectic.Contradiction ⊤)
historicalContextDifferenceDoesNotManufactureContradiction =
  Dialectic.noGenericContradictionFromContextReports

------------------------------------------------------------------------
-- Historical two-pole compression can hide a third unresolved/refining state.
------------------------------------------------------------------------

data HistoricalTritState : Set where
  inheritedPole
  unresolvedTransition
  reconstitutedPole
  : HistoricalTritState

data BinaryHistoricalPole : Set where
  oldPole newPole : BinaryHistoricalPole

data FineHistoricalStatus : Set where
  inheritedFine
  unresolvedFine
  reconstitutedFine
  : FineHistoricalStatus

collapseUnresolvedBackward : HistoricalTritState → BinaryHistoricalPole
collapseUnresolvedBackward inheritedPole = oldPole
collapseUnresolvedBackward unresolvedTransition = oldPole
collapseUnresolvedBackward reconstitutedPole = newPole

fineHistoricalStatus : HistoricalTritState → FineHistoricalStatus
fineHistoricalStatus inheritedPole = inheritedFine
fineHistoricalStatus unresolvedTransition = unresolvedFine
fineHistoricalStatus reconstitutedPole = reconstitutedFine

binaryBackwardCollapseCannotRecoverFineStatus :
  INF.FactorsThrough collapseUnresolvedBackward fineHistoricalStatus → ⊥
binaryBackwardCollapseCannotRecoverFineStatus =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      inheritedPole
      unresolvedTransition
      refl
      (λ ()))

collapseUnresolvedForward : HistoricalTritState → BinaryHistoricalPole
collapseUnresolvedForward inheritedPole = oldPole
collapseUnresolvedForward unresolvedTransition = newPole
collapseUnresolvedForward reconstitutedPole = newPole

binaryForwardCollapseCannotRecoverFineStatus :
  INF.FactorsThrough collapseUnresolvedForward fineHistoricalStatus → ⊥
binaryForwardCollapseCannotRecoverFineStatus =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      unresolvedTransition
      reconstitutedPole
      refl
      (λ ()))

------------------------------------------------------------------------
-- Two-pole sex/gender coding is also not the 2x2 construction tensor.
------------------------------------------------------------------------

binarySexCodingStillCannotRecoverConstructionDirection :
  INF.FactorsThrough Stats.recordedSexSurface Stats.relationalCell → ⊥
binarySexCodingStillCannotRecoverConstructionDirection =
  Stats.recordedSexCannotRecoverConstructionDirection

------------------------------------------------------------------------
-- Path order and ternary epistemic status are independent dimensions.
------------------------------------------------------------------------

data PathAssessment : Set where
  pathRejected
  pathUnresolved
  pathSupported
  : PathAssessment

assessPath : Order.PathOrder → PathAssessment
assessPath Order.institutionThenReinterpret = pathUnresolved
assessPath Order.reinterpretThenInstitution = pathUnresolved

sameAssessmentDoesNotRecoverOrder :
  INF.FactorsThrough assessPath (λ x → x) → ⊥
sameAssessmentDoesNotRecoverOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Order.institutionThenReinterpret
      Order.reinterpretThenInstitution
      refl
      (λ ()))

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

data TernaryNeutralMeansDialecticalSynthesis : Set where

data BinaryOppositionExhaustsHistoricalPossibility : Set where

data CounterpositionMeansLogicalContradiction : Set where

data UnresolvedMeansFalse : Set where

data TwoPolesExhaustSexedSubjectFormation : Set where

ternaryNeutralDoesNotMeanDialecticalSynthesis :
  TernaryNeutralMeansDialecticalSynthesis → ⊥
ternaryNeutralDoesNotMeanDialecticalSynthesis ()

binaryOppositionDoesNotExhaustHistoricalPossibility :
  BinaryOppositionExhaustsHistoricalPossibility → ⊥
binaryOppositionDoesNotExhaustHistoricalPossibility ()

counterpositionDoesNotMeanLogicalContradiction :
  CounterpositionMeansLogicalContradiction → ⊥
counterpositionDoesNotMeanLogicalContradiction ()

unresolvedDoesNotMeanFalse : UnresolvedMeansFalse → ⊥
unresolvedDoesNotMeanFalse ()

twoPolesDoNotExhaustSexedSubjectFormation :
  TwoPolesExhaustSexedSubjectFormation → ⊥
twoPolesDoNotExhaustSexedSubjectFormation ()

record SexedHistoricalBinaryTernaryDialecticBoundary : Set where
  constructor sexed-historical-binary-ternary-dialectic-boundary
  field
    binaryEqualsTernary : Bool
    dialecticalCounterpositionEqualsNegation : Bool
    neutralEqualsReject : Bool
    neutralEqualsAccept : Bool
    neutralEqualsSynthesis : Bool
    binarySexCodingRecoversConstructionTensor : Bool
    pathAssessmentRecoversPathOrder : Bool
    genuineSameFrameContradictionStillExplodes : Bool

canonicalSexedHistoricalBinaryTernaryDialecticBoundary :
  SexedHistoricalBinaryTernaryDialecticBoundary
canonicalSexedHistoricalBinaryTernaryDialecticBoundary =
  sexed-historical-binary-ternary-dialectic-boundary
    false false false false false false false true
