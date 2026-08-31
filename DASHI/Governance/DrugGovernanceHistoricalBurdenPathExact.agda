module DASHI.Governance.DrugGovernanceHistoricalBurdenPathExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as History
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Governance.DrugGovernanceHistoricalBurdenExternalisationExact as Burden
import DASHI.Governance.DrugGovernanceBenefitCaptureRepairResidueExact as BenefitRepair

------------------------------------------------------------------------
-- ORDERED HISTORICAL BURDEN PATH
--
-- Present category/benefit surfaces do not determine the ordered path by which
-- uncertainty, burden, benefit and repair standing were redistributed.
------------------------------------------------------------------------

data BurdenStage : Set where
  punitiveExternalisedStage
  therapeuticReopenedStage
  commercialCaptureStage
  repairAcknowledgedStage
  repairDischargedStage
  : BurdenStage

data BurdenEdge : BurdenStage → BurdenStage → Set where
  punitiveToTherapeutic :
    BurdenEdge punitiveExternalisedStage therapeuticReopenedStage
  therapeuticToCommercial :
    BurdenEdge therapeuticReopenedStage commercialCaptureStage
  commercialToAcknowledged :
    BurdenEdge commercialCaptureStage repairAcknowledgedStage
  acknowledgedToDischarged :
    BurdenEdge repairAcknowledgedStage repairDischargedStage
  directTherapeuticAcknowledgement :
    BurdenEdge therapeuticReopenedStage repairAcknowledgedStage

data BurdenPath : BurdenStage → BurdenStage → Set where
  pathRefl : ∀ {stage} → BurdenPath stage stage
  pathStep :
    ∀ {before middle after} →
    BurdenEdge before middle →
    BurdenPath middle after →
    BurdenPath before after

canonicalCommercialRepairPath :
  BurdenPath punitiveExternalisedStage repairAcknowledgedStage
canonicalCommercialRepairPath =
  pathStep punitiveToTherapeutic
    (pathStep therapeuticToCommercial
      (pathStep commercialToAcknowledged pathRefl))

canonicalDirectAcknowledgementPath :
  BurdenPath punitiveExternalisedStage repairAcknowledgedStage
canonicalDirectAcknowledgementPath =
  pathStep punitiveToTherapeutic
    (pathStep directTherapeuticAcknowledgement pathRefl)

------------------------------------------------------------------------
-- Proof-relevant occurrence of the commercial-capture edge.
------------------------------------------------------------------------

data ContainsCommercialCapture :
    ∀ {before after} → BurdenPath before after → Set where
  commercialHere :
    ∀ {after} {rest : BurdenPath commercialCaptureStage after} →
    ContainsCommercialCapture
      (pathStep therapeuticToCommercial rest)
  commercialLater :
    ∀ {before middle after}
      {edge : BurdenEdge before middle}
      {rest : BurdenPath middle after} →
    ContainsCommercialCapture rest →
    ContainsCommercialCapture (pathStep edge rest)

canonicalCommercialPathContainsCapture :
  ContainsCommercialCapture canonicalCommercialRepairPath
canonicalCommercialPathContainsCapture =
  commercialLater commercialHere

------------------------------------------------------------------------
-- Same present endpoint, different retained path code.
------------------------------------------------------------------------

data BurdenHistoryVariant : Set where
  commercialisedHistory
  directAcknowledgementHistory
  : BurdenHistoryVariant

data PresentEndpointSurface : Set where
  samePositiveAcknowledgedEndpoint : PresentEndpointSurface

data RetainedPathCode : Set where
  commercialCaptureRetained
  directAcknowledgementRetained
  : RetainedPathCode

presentEndpoint : BurdenHistoryVariant → PresentEndpointSurface
presentEndpoint _ = samePositiveAcknowledgedEndpoint

retainedPath : BurdenHistoryVariant → RetainedPathCode
retainedPath commercialisedHistory = commercialCaptureRetained
retainedPath directAcknowledgementHistory = directAcknowledgementRetained

samePresentEndpoint :
  presentEndpoint commercialisedHistory
  ≡ presentEndpoint directAcknowledgementHistory
samePresentEndpoint = refl

retainedPathDiffers :
  retainedPath commercialisedHistory
  ≡ retainedPath directAcknowledgementHistory → ⊥
retainedPathDiffers ()

presentEndpointCannotRecoverBurdenPath :
  INF.FactorsThrough presentEndpoint retainedPath → ⊥
presentEndpointCannotRecoverBurdenPath =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      commercialisedHistory
      directAcknowledgementHistory
      samePresentEndpoint
      retainedPathDiffers)

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

historyBoundary : History.HistoryQualifiedSelectionBoundary
historyBoundary = History.canonicalHistoryQualifiedSelectionBoundary

repairBoundary : Repair.NonSubstitutionBoundary
repairBoundary = Repair.canonicalNonSubstitutionBoundary

burdenBoundary : Burden.HistoricalBurdenExternalisationBoundary
burdenBoundary = Burden.canonicalHistoricalBurdenExternalisationBoundary

benefitRepairBoundary : BenefitRepair.BenefitCaptureRepairResidueBoundary
benefitRepairBoundary = BenefitRepair.canonicalBenefitCaptureRepairResidueBoundary

------------------------------------------------------------------------
-- Scope boundaries.
------------------------------------------------------------------------

data SameEndpointPromotesSameBurdenHistory : Set where

data AcknowledgementPromotesMultiAxisRepairClosure : Set where

data CommercialCapturePromotesHistoricalCausation : Set where

sameEndpointDoesNotPromoteSameBurdenHistory :
  SameEndpointPromotesSameBurdenHistory → ⊥
sameEndpointDoesNotPromoteSameBurdenHistory ()

acknowledgementDoesNotPromoteMultiAxisRepairClosure :
  AcknowledgementPromotesMultiAxisRepairClosure → ⊥
acknowledgementDoesNotPromoteMultiAxisRepairClosure ()

commercialCaptureDoesNotPromoteHistoricalCausation :
  CommercialCapturePromotesHistoricalCausation → ⊥
commercialCaptureDoesNotPromoteHistoricalCausation ()

record HistoricalBurdenPathBoundary : Set where
  constructor historicalBurdenPathBoundary
  field
    burdenPathIsOrderRetaining : Bool
    burdenPathIsOrderRetainingIsTrue : burdenPathIsOrderRetaining ≡ true
    presentEndpointDeterminesHistory : Bool
    presentEndpointDeterminesHistoryIsFalse : presentEndpointDeterminesHistory ≡ false
    commercialCaptureOccurrenceIsProofRelevant : Bool
    commercialCaptureOccurrenceIsProofRelevantIsTrue :
      commercialCaptureOccurrenceIsProofRelevant ≡ true
    repairIsMultiAxisNonSubstitutional : Bool
    repairIsMultiAxisNonSubstitutionalIsTrue :
      repairIsMultiAxisNonSubstitutional ≡ true

canonicalHistoricalBurdenPathBoundary : HistoricalBurdenPathBoundary
canonicalHistoricalBurdenPathBoundary =
  historicalBurdenPathBoundary true refl false refl true refl true refl
