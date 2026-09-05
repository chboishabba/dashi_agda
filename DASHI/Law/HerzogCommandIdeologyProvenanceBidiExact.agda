module DASHI.Law.HerzogCommandIdeologyProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact as Source
import DASHI.Law.OperationalCommandAuthorityConstitutionalBidiExact as Command

------------------------------------------------------------------------
-- A source-backed finding about Herzog is not itself a producer for the motive,
-- content, or provenance of an NSW Police command.  This module makes the
-- missing causal/provenance bridge explicit.
------------------------------------------------------------------------

data IdeologyRelationState : Set where
  relationClosed relationOpen relationConflict : IdeologyRelationState

record CommandIdeologyProvenanceFibre : Set where
  constructor commandIdeologyProvenanceFibre
  field
    publicFigureSourceReceipt : Source.SourceReceipt
    commandAuthorityFibre : Command.CommandAuthorityFibre
    commandContentReceipt : IdeologyRelationState
    policyTransmissionReceipt : IdeologyRelationState
    operationalMotiveReceipt : IdeologyRelationState
    coordinationReceipt : IdeologyRelationState
    provenanceReference : String

open CommandIdeologyProvenanceFibre public

------------------------------------------------------------------------
-- Claims and reverse producers.
------------------------------------------------------------------------

data IdeologyCommandClaim : Set where
  herzogHasCommissionIncitementFinding
  nswCommandReflectedHerzogPosition
  nswCommandWasZionistIdeologyMotivated
  nswPoliceCoordinatedWithHerzogOrIsraeliOfficials : IdeologyCommandClaim

data IdeologyCommandProducer : Set where
  commissionFindingProducer
  commandContentAndPolicyBridgeProducer
  motiveEvidenceProducer
  coordinationEvidenceProducer : IdeologyCommandProducer

reverseIdeologyCommand : IdeologyCommandClaim → IdeologyCommandProducer
reverseIdeologyCommand herzogHasCommissionIncitementFinding = commissionFindingProducer
reverseIdeologyCommand nswCommandReflectedHerzogPosition = commandContentAndPolicyBridgeProducer
reverseIdeologyCommand nswCommandWasZionistIdeologyMotivated = motiveEvidenceProducer
reverseIdeologyCommand nswPoliceCoordinatedWithHerzogOrIsraeliOfficials = coordinationEvidenceProducer

record IdeologyCommandCutset : Set where
  constructor ideologyCommandCutset
  field
    commissionFindingClosed : Bool
    commandContentBridgeClosed : Bool
    motiveClosed : Bool
    coordinationClosed : Bool
    cutsetReference : String

open IdeologyCommandCutset public

data IdeologyCommandResidual : Set where
  commissionResidual commandContentBridgeResidual motiveResidual coordinationResidual ideologyCommandClosed : IdeologyCommandResidual

firstIdeologyCommandResidual : IdeologyCommandClaim → IdeologyCommandCutset → IdeologyCommandResidual
firstIdeologyCommandResidual herzogHasCommissionIncitementFinding c with commissionFindingClosed c
... | false = commissionResidual
... | true = ideologyCommandClosed
firstIdeologyCommandResidual nswCommandReflectedHerzogPosition c with commissionFindingClosed c
... | false = commissionResidual
... | true with commandContentBridgeClosed c
...   | false = commandContentBridgeResidual
...   | true = ideologyCommandClosed
firstIdeologyCommandResidual nswCommandWasZionistIdeologyMotivated c with commissionFindingClosed c
... | false = commissionResidual
... | true with motiveClosed c
...   | false = motiveResidual
...   | true = ideologyCommandClosed
firstIdeologyCommandResidual nswPoliceCoordinatedWithHerzogOrIsraeliOfficials c with commissionFindingClosed c
... | false = commissionResidual
... | true with coordinationClosed c
...   | false = coordinationResidual
...   | true = ideologyCommandClosed

canonicalCommissionOnlyCutset : IdeologyCommandCutset
canonicalCommissionOnlyCutset = ideologyCommandCutset true false false false
  "UN Commission incitement finding closed; NSW command ideology/motive/coordination bridges open"

commissionFindingDoesNotCloseCommandContentBridge :
  firstIdeologyCommandResidual nswCommandReflectedHerzogPosition canonicalCommissionOnlyCutset
  ≡ commandContentBridgeResidual
commissionFindingDoesNotCloseCommandContentBridge = refl

commissionFindingDoesNotCloseMotive :
  firstIdeologyCommandResidual nswCommandWasZionistIdeologyMotivated canonicalCommissionOnlyCutset
  ≡ motiveResidual
commissionFindingDoesNotCloseMotive = refl

commissionFindingDoesNotCloseCoordination :
  firstIdeologyCommandResidual nswPoliceCoordinatedWithHerzogOrIsraeliOfficials canonicalCommissionOnlyCutset
  ≡ coordinationResidual
commissionFindingDoesNotCloseCoordination = refl

record HerzogCommandBoundary : Set where
  constructor herzogCommandBoundary
  field
    herzogIncitementFindingImpliesNSWPoliceMotive : Bool
    herzogIncitementFindingImpliesNSWPoliceMotiveIsFalse : herzogIncitementFindingImpliesNSWPoliceMotive ≡ false
    protestTargetIdentityImpliesPoliceCoordination : Bool
    protestTargetIdentityImpliesPoliceCoordinationIsFalse : protestTargetIdentityImpliesPoliceCoordination ≡ false
    ideologicalSimilarityImpliesOperationalCausation : Bool
    ideologicalSimilarityImpliesOperationalCausationIsFalse : ideologicalSimilarityImpliesOperationalCausation ≡ false

canonicalHerzogCommandBoundary : HerzogCommandBoundary
canonicalHerzogCommandBoundary = herzogCommandBoundary false refl false refl false refl
