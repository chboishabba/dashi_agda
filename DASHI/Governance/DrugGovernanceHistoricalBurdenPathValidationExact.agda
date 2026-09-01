module DASHI.Governance.DrugGovernanceHistoricalBurdenPathValidationExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Governance.DrugGovernanceHistoricalBurdenPathExact as Path
import DASHI.Governance.DrugGovernanceBurdenPathEdgeIndexedReopeningExact as Reopening
import DASHI.Governance.DrugGovernanceHistoricalBurdenFarCrossPollinationExact as Cross
import DASHI.Governance.DrugGovernanceHistoricalBurdenPhilosophyAuditExact as PhilosophyBurden

------------------------------------------------------------------------
-- Focused pins for the historical burden-path tranche.
------------------------------------------------------------------------

commercialPath :
  Path.BurdenPath Path.punitiveExternalisedStage Path.repairAcknowledgedStage
commercialPath = Path.canonicalCommercialRepairPath

commercialOccurrence :
  Path.ContainsCommercialCapture Path.canonicalCommercialRepairPath
commercialOccurrence = Path.canonicalCommercialPathContainsCapture

commercialMaterialReopening :
  Affected.ReopeningObligation
    Reopening.Depends
    (Reopening.edgeArtifact Reopening.commercialCaptureEdge)
    (Reopening.consumerArtifact Reopening.materialBenefitConsequence)
commercialMaterialReopening = Reopening.commercialCaptureReopensMaterialBenefit

commercialRepairReopening :
  Affected.ReopeningObligation
    Reopening.Depends
    (Reopening.edgeArtifact Reopening.commercialCaptureEdge)
    (Reopening.consumerArtifact Reopening.historicalRepairConsequence)
commercialRepairReopening = Reopening.commercialCaptureReopensHistoricalRepair

pathBoundary : Path.HistoricalBurdenPathBoundary
pathBoundary = Path.canonicalHistoricalBurdenPathBoundary

reopeningBoundary : Reopening.BurdenPathEdgeIndexedReopeningBoundary
reopeningBoundary = Reopening.canonicalBurdenPathEdgeIndexedReopeningBoundary

crossBoundary : Cross.HistoricalBurdenFarCrossPollinationBoundary
crossBoundary = Cross.canonicalHistoricalBurdenFarCrossPollinationBoundary

philosophyBoundary : PhilosophyBurden.HistoricalBurdenPhilosophyAuditBoundary
philosophyBoundary = PhilosophyBurden.canonicalHistoricalBurdenPhilosophyAuditBoundary
