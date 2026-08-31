module DASHI.Governance.DrugGovernanceHistoricalBurdenPhilosophyAuditExact where

open import DASHI.Core.Prelude

import DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact as Philosophy
import DASHI.Governance.DrugGovernanceHistoricalBurdenFarCrossPollinationExact as Cross
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous

------------------------------------------------------------------------
-- PHILOSOPHY-SEEDed HISTORICAL BURDEN AUDIT
--
-- Philosophy selects candidate questions/probes.  It does not prove the
-- historical path, burden distribution, causal mechanism or repair mandate.
------------------------------------------------------------------------

philosophyProbe : Philosophy.DrugCategoryAudit → Cross.ProbeFamily
philosophyProbe Philosophy.wittgensteinUseAudit = Cross.historyPathProbe
philosophyProbe Philosophy.zizekClosureFantasyAudit = Cross.historyPathProbe
philosophyProbe Philosophy.foucaultPowerClassificationAudit = Cross.controlTopologyProbe
philosophyProbe Philosophy.marxMaterialInterestAudit = Cross.benefitRoutingProbe
philosophyProbe Philosophy.nietzscheValuationFormationAudit = Cross.historyPathProbe
philosophyProbe Philosophy.spinozaPowerToActAudit = Cross.burdenDistributionProbe
philosophyProbe Philosophy.kantNonInstrumentalisationAudit = Cross.repairAxisProbe
philosophyProbe Philosophy.levinasOtherExceedsChartAudit = Cross.burdenDistributionProbe
philosophyProbe Philosophy.derridaNoFinalClosureAudit = Cross.historyPathProbe
philosophyProbe Philosophy.feministSubjectPositionAudit = Cross.burdenDistributionProbe
philosophyProbe Philosophy.intersectionalAxisAudit = Cross.burdenDistributionProbe

record PhilosophyBurdenProbeReceipt (audit : Philosophy.DrugCategoryAudit) : Set where
  constructor philosophyBurdenProbeReceipt
  field
    probe : Cross.ProbeFamily
    agreesWithDeclaredAuditMap : probe ≡ philosophyProbe audit
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    empiricalHistoricalEvidenceStillRequired : Bool
    empiricalHistoricalEvidenceStillRequiredIsTrue :
      empiricalHistoricalEvidenceStillRequired ≡ true

open PhilosophyBurdenProbeReceipt public

marxBenefitProbe : PhilosophyBurdenProbeReceipt Philosophy.marxMaterialInterestAudit
marxBenefitProbe = philosophyBurdenProbeReceipt
  Cross.benefitRoutingProbe refl true refl true refl

foucaultControlProbe :
  PhilosophyBurdenProbeReceipt Philosophy.foucaultPowerClassificationAudit
foucaultControlProbe = philosophyBurdenProbeReceipt
  Cross.controlTopologyProbe refl true refl true refl

zizekHistoryProbe :
  PhilosophyBurdenProbeReceipt Philosophy.zizekClosureFantasyAudit
zizekHistoryProbe = philosophyBurdenProbeReceipt
  Cross.historyPathProbe refl true refl true refl

feministBurdenProbe :
  PhilosophyBurdenProbeReceipt Philosophy.feministSubjectPositionAudit
feministBurdenProbe = philosophyBurdenProbeReceipt
  Cross.burdenDistributionProbe refl true refl true refl

------------------------------------------------------------------------
-- Source-authority welds and non-promotions.
------------------------------------------------------------------------

philosophyBoundary : Philosophy.DrugCategoryPhilosophyOperatorBoundary
philosophyBoundary = Philosophy.canonicalDrugCategoryPhilosophyOperatorBoundary

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

data PhilosophyProbePromotesEmpiricalHistory : Set where

data MarxProbePromotesCapitalistCause : Set where

data FoucaultProbePromotesLegitimateAuthorityVerdict : Set where

data WesternPhilosophyProbePromotesIndigenousSovereignty : Set where

data FeministProbePromotesUniversalSubjectPosition : Set where

philosophyProbeDoesNotPromoteEmpiricalHistory :
  PhilosophyProbePromotesEmpiricalHistory → ⊥
philosophyProbeDoesNotPromoteEmpiricalHistory ()

marxProbeDoesNotPromoteCapitalistCause :
  MarxProbePromotesCapitalistCause → ⊥
marxProbeDoesNotPromoteCapitalistCause ()

foucaultProbeDoesNotPromoteLegitimateAuthorityVerdict :
  FoucaultProbePromotesLegitimateAuthorityVerdict → ⊥
foucaultProbeDoesNotPromoteLegitimateAuthorityVerdict ()

westernPhilosophyDoesNotPromoteIndigenousSovereignty :
  WesternPhilosophyProbePromotesIndigenousSovereignty → ⊥
westernPhilosophyDoesNotPromoteIndigenousSovereignty ()

feministProbeDoesNotPromoteUniversalSubjectPosition :
  FeministProbePromotesUniversalSubjectPosition → ⊥
feministProbeDoesNotPromoteUniversalSubjectPosition ()

record HistoricalBurdenPhilosophyAuditBoundary : Set where
  constructor historicalBurdenPhilosophyAuditBoundary
  field
    philosophyCanSeedCandidateBurdenProbe : Bool
    philosophyCanSeedCandidateBurdenProbeIsTrue :
      philosophyCanSeedCandidateBurdenProbe ≡ true
    philosophicalProbeAutomaticallyProvesHistory : Bool
    philosophicalProbeAutomaticallyProvesHistoryIsFalse :
      philosophicalProbeAutomaticallyProvesHistory ≡ false
    marxBenefitAuditAutomaticallyProvesCause : Bool
    marxBenefitAuditAutomaticallyProvesCauseIsFalse :
      marxBenefitAuditAutomaticallyProvesCause ≡ false
    foucaultPowerAuditAutomaticallyDeterminesLegitimacy : Bool
    foucaultPowerAuditAutomaticallyDeterminesLegitimacyIsFalse :
      foucaultPowerAuditAutomaticallyDeterminesLegitimacy ≡ false
    westernPhilosophyTransfersIndigenousAuthority : Bool
    westernPhilosophyTransfersIndigenousAuthorityIsFalse :
      westernPhilosophyTransfersIndigenousAuthority ≡ false

canonicalHistoricalBurdenPhilosophyAuditBoundary :
  HistoricalBurdenPhilosophyAuditBoundary
canonicalHistoricalBurdenPhilosophyAuditBoundary =
  historicalBurdenPhilosophyAuditBoundary
    true refl false refl false refl false refl false refl
