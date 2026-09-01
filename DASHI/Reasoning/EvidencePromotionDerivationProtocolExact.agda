module DASHI.Reasoning.EvidencePromotionDerivationProtocolExact where

open import DASHI.Core.Prelude

import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path

------------------------------------------------------------------------
-- ORDERED AUTHORITY PROTOCOL
--
-- Typed edge labels alone do not make every permutation admissible.  This
-- protocol gives the canonical authority order for the experimental-claim
-- lane and leaves residual refinement explicitly iterable while qualified.
------------------------------------------------------------------------

data ProtocolStage : Set where
  parserCandidateStage
  reviewedSemanticStage
  logicalConsequenceStage
  empiricalQualifiedStage
  empiricallySupportedStage
  : ProtocolStage

data ProtocolStep : ProtocolStage → ProtocolStage → Set where
  parserToReviewedSemantic :
    ProtocolStep parserCandidateStage reviewedSemanticStage
  semanticToLogicalConsequence :
    ProtocolStep reviewedSemanticStage logicalConsequenceStage
  logicalToEmpiricalQualified :
    ProtocolStep logicalConsequenceStage empiricalQualifiedStage
  refineQualifiedResidual :
    ProtocolStep empiricalQualifiedStage empiricalQualifiedStage
  dischargeQualifiedDesign :
    ProtocolStep empiricalQualifiedStage empiricallySupportedStage

ProtocolPath : ProtocolStage → ProtocolStage → Set
ProtocolPath = Trajectory.Trace ProtocolStep

canonicalParserToLogicalPath :
  ProtocolPath parserCandidateStage logicalConsequenceStage
canonicalParserToLogicalPath =
  Trajectory.traceStep parserToReviewedSemantic
    (Trajectory.traceStep semanticToLogicalConsequence Trajectory.traceRefl)

canonicalLogicalToSupportedPath :
  ProtocolPath logicalConsequenceStage empiricallySupportedStage
canonicalLogicalToSupportedPath =
  Trajectory.traceStep logicalToEmpiricalQualified
    (Trajectory.traceStep dischargeQualifiedDesign Trajectory.traceRefl)

canonicalQualifiedRefinementThenDischarge :
  ProtocolPath empiricalQualifiedStage empiricallySupportedStage
canonicalQualifiedRefinementThenDischarge =
  Trajectory.traceStep refineQualifiedResidual
    (Trajectory.traceStep dischargeQualifiedDesign Trajectory.traceRefl)

------------------------------------------------------------------------
-- Edge-kind interpretation of the protocol.
------------------------------------------------------------------------

protocolEdgeKind :
  ∀ {from to} → ProtocolStep from to → Path.DerivationEdgeKind
protocolEdgeKind parserToReviewedSemantic = Path.semanticResolutionEdge
protocolEdgeKind semanticToLogicalConsequence = Path.logicalEntailmentEdge
protocolEdgeKind logicalToEmpiricalQualified = Path.empiricalPromotionEdge
protocolEdgeKind refineQualifiedResidual = Path.residualRefinementEdge
protocolEdgeKind dischargeQualifiedDesign = Path.designDischargeEdge

------------------------------------------------------------------------
-- Forbidden shortcuts are empty types, not low-probability choices.
------------------------------------------------------------------------

data DirectLogicalSupportShortcut : Set where

data ParserToWorldFactShortcut : Set where

directLogicalSupportShortcutImpossible : DirectLogicalSupportShortcut → ⊥
directLogicalSupportShortcutImpossible ()

parserToWorldFactShortcutImpossible : ParserToWorldFactShortcut → ⊥
parserToWorldFactShortcutImpossible ()

record EvidencePromotionProtocolBoundary : Set where
  constructor evidencePromotionProtocolBoundary
  field
    logicalConsequenceDirectlyBecomesEmpiricalSupport : Bool
    logicalConsequenceDirectlyBecomesEmpiricalSupportIsFalse :
      logicalConsequenceDirectlyBecomesEmpiricalSupport ≡ false
    empiricalQualificationMayBeResidualRefinedRepeatedly : Bool
    empiricalQualificationMayBeResidualRefinedRepeatedlyIsTrue :
      empiricalQualificationMayBeResidualRefinedRepeatedly ≡ true
    supportedEmpiricalStateRequiresDesignDischarge : Bool
    supportedEmpiricalStateRequiresDesignDischargeIsTrue :
      supportedEmpiricalStateRequiresDesignDischarge ≡ true
    parserObservationDirectlyBecomesWorldFact : Bool
    parserObservationDirectlyBecomesWorldFactIsFalse :
      parserObservationDirectlyBecomesWorldFact ≡ false

canonicalEvidencePromotionProtocolBoundary : EvidencePromotionProtocolBoundary
canonicalEvidencePromotionProtocolBoundary =
  evidencePromotionProtocolBoundary false refl true refl true refl false refl
