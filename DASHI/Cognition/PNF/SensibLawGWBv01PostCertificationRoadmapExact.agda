module DASHI.Cognition.PNF.SensibLawGWBv01PostCertificationRoadmapExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact as Direct
import DASHI.Cognition.PNF.DirectStreamingRoadmapSynthesisExact as OldRoadmap
import DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationExact as GWB

------------------------------------------------------------------------
-- Current roadmap owner after the GWB v0.1 full certification run.
--
-- The old roadmap remains a faithful pre-run snapshot whose current stage was
-- boundedParity.  This owner advances the live frontier only as far as the
-- receipt licenses: bounded parity is closed on GWB v0.1; production cutover is
-- now the next decision gate, not an already-earned global authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Declared production cutover.
--
-- This receipt is a governed physical-policy choice. It uses the bounded GWB
-- parity receipt as evidence. It does not claim parity for every future corpus.
------------------------------------------------------------------------

record ProductionCutoverReceipt : Set where
  constructor productionCutoverReceipt
  field
    certifiedRun : GWB.GWBv01RuntimeCertificationReceipt
    projectionMode : Direct.ParserProjectionMode
    productionMode : projectionMode ≡ Direct.productionDirect
    sentenceLocalDatabaseCrossings : Nat
    sentenceLocalDatabaseCrossingsZero :
      sentenceLocalDatabaseCrossings ≡ zero
    productionParserTokenWrites : Nat
    productionParserTokenWritesZero :
      productionParserTokenWrites ≡ zero
    referencePathRetained : Bool
    referencePathRetainedTrue : referencePathRetained ≡ true
    universalParityClaimed : Bool
    universalParityClaimedFalse : universalParityClaimed ≡ false

open ProductionCutoverReceipt public

sensibLawGWBv01ProductionCutover : ProductionCutoverReceipt
sensibLawGWBv01ProductionCutover =
  productionCutoverReceipt
    GWB.gwbV01CertifiedRun
    Direct.productionDirect
    refl
    zero
    refl
    zero
    refl
    true
    refl
    false
    refl

data PostGWBStage : Set where
  boundedParityClosed : PostGWBStage
  productionCutoverDecision : PostGWBStage
  semanticDeltaExpansion : PostGWBStage
  multiCorpusRebenchmark : PostGWBStage
  cryptographicPublication : PostGWBStage

record PostGWBFrontier : Set where
  constructor postGWBFrontier
  field
    certifiedRun : GWB.GWBv01RuntimeCertificationReceipt
    currentStage : PostGWBStage

    boundedParityClosedOnGWB : Bool
    boundedParityClosedOnGWBTrue : boundedParityClosedOnGWB ≡ true

    productionCutoverUniversallyAuthorized : Bool
    productionCutoverUniversallyAuthorizedFalse :
      productionCutoverUniversallyAuthorized ≡ false

    measuredOnePointTwoTierOnGWB : Bool
    measuredOnePointTwoTierOnGWBTrue : measuredOnePointTwoTierOnGWB ≡ true

    onePointTwoTierUniversallyCertified : Bool
    onePointTwoTierUniversallyCertifiedFalse :
      onePointTwoTierUniversallyCertified ≡ false

open PostGWBFrontier public

currentSensibLawPostGWBFrontier : PostGWBFrontier
currentSensibLawPostGWBFrontier =
  postGWBFrontier
    GWB.gwbV01CertifiedRun
    productionCutoverDecision
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- The historical roadmap owner is preserved, not retroactively rewritten.
------------------------------------------------------------------------

oldRoadmapSnapshotWasAtBoundedParity :
  OldRoadmap.currentStage OldRoadmap.currentDirectCertificationFrontier
  ≡ OldRoadmap.boundedParity
oldRoadmapSnapshotWasAtBoundedParity = refl

------------------------------------------------------------------------
-- Highest-alpha next implementation lane.
--
-- We now have enough bounded evidence to expand semantic delta structure under
-- the already-certified no-rescan/no-auto-publication runtime shape.  That work
-- must preserve residuals for unresolved scope/attachment and must later earn
-- fresh parity/performance receipts rather than inheriting them automatically.
------------------------------------------------------------------------

data NextSemanticLane : Set where
  richerLegalRoleDelta : NextSemanticLane
  negationScopeDelta : NextSemanticLane
  modalityDelta : NextSemanticLane
  conditionalDelta : NextSemanticLane
  temporalDelta : NextSemanticLane
  referenceDelta : NextSemanticLane
  crossSentenceDelta : NextSemanticLane

record SemanticExpansionBoundary : Set where
  constructor semanticExpansionBoundary
  field
    unresolvedScopeMayBeSilentlyPromoted : Bool
    unresolvedScopeMayBeSilentlyPromotedFalse :
      unresolvedScopeMayBeSilentlyPromoted ≡ false
    oldParityReceiptAutomaticallyCoversNewSemantics : Bool
    oldParityReceiptAutomaticallyCoversNewSemanticsFalse :
      oldParityReceiptAutomaticallyCoversNewSemantics ≡ false
    oldPerformanceReceiptAutomaticallyCoversNewSemantics : Bool
    oldPerformanceReceiptAutomaticallyCoversNewSemanticsFalse :
      oldPerformanceReceiptAutomaticallyCoversNewSemantics ≡ false

open SemanticExpansionBoundary public

canonicalSemanticExpansionBoundary : SemanticExpansionBoundary
canonicalSemanticExpansionBoundary =
  semanticExpansionBoundary
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Invalid authority escalations remain uninhabited.
------------------------------------------------------------------------

data GWBReceiptMakesAllFutureCorporaParityCertified : Set where

data DeclaredCutoverMakesParityUniversal : Set where

data GWBReceiptMakesAllFutureSemanticExpansionsPerformanceCertified : Set where

boundedReceiptCannotCertifyAllFutureCorpora :
  GWBReceiptMakesAllFutureCorporaParityCertified → ⊥
boundedReceiptCannotCertifyAllFutureCorpora ()

declaredCutoverDoesNotMakeParityUniversal :
  DeclaredCutoverMakesParityUniversal → ⊥
declaredCutoverDoesNotMakeParityUniversal ()

boundedReceiptCannotCertifyFutureExpandedSemantics :
  GWBReceiptMakesAllFutureSemanticExpansionsPerformanceCertified → ⊥
boundedReceiptCannotCertifyFutureExpandedSemantics ()
