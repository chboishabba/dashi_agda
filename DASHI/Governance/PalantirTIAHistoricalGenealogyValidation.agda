module DASHI.Governance.PalantirTIAHistoricalGenealogyValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

-- RED-first contract: production owners intentionally added afterwards.
import DASHI.Governance.PalantirTIAHistoricalGenealogyExact as G
import DASHI.Governance.PalantirTIAPartyBenefitDistributionExact as Distribution
import DASHI.Governance.PalantirTIAInvestigativeParetoSnowballExact as Pareto
import DASHI.Governance.TIAComponentDispositionAtlasExact as Disposition
import DASHI.Governance.WadeRoleChronologyExact as Wade
import DASHI.Governance.PalantirEarlyIntelDevelopmentChronologyExact as Early
import DASHI.Governance.InformationAwarenessProgrammeMigrationHypergraphExact as Migration

validation :
  G.tiaProgrammeDocumented G.canonicalTIAGenealogy ≡ true
  × G.poindexterDirectedTIA G.canonicalTIAGenealogy ≡ true
  × G.perleHouseMeetingDocumented G.canonicalTIAGenealogy ≡ true
  × G.inQTelPalantirInvestmentDocumented G.canonicalTIAGenealogy ≡ true
  × G.chiliadMaxwellCofounderDocumented G.canonicalTIAGenealogy ≡ true
  × G.chiliadWadeFounderDocumented G.canonicalTIAGenealogy ≡ true
  × G.wadeTIAPointManPrimaryReceiptInstalled G.canonicalTIAGenealogy ≡ false
  × G.palantirIsPrivatizedTIAPromoted G.canonicalTIAGenealogy ≡ false
  × G.iranContraAnalogyCreatesGenealogy G.canonicalTIAGenealogy ≡ false
validation = refl , refl , refl , refl , refl , refl , refl , refl , refl

distributionValidation :
  Distribution.firstOrderBenefitDoesNotEstablishIntent ≡ true
  × Distribution.secondOrderBenefitDoesNotEstablishControl ≡ true
  × Distribution.thirdOrderBenefitDoesNotEstablishCausation ≡ true
  × Distribution.sameAggregateCannotRecoverPartyDistribution ≡ true
  × Distribution.currentStrongPrivatizationClaimStillBlocked ≡ true
distributionValidation = refl , refl , refl , refl , refl

paretoValidation :
  Pareto.officialWadeTIARoleOnFrontier ≡ true
  × Pareto.tiaDispositionOnFrontier ≡ true
  × Pareto.earlyPalantirCIAIQTOnFrontier ≡ true
  × Pareto.broadKeywordSweepOffFrontier ≡ true
  × Pareto.paretoPriorityCreatesHistoricalTruth ≡ false
  × Pareto.offFrontierDeletesRequirement ≡ false
paretoValidation = refl , refl , refl , refl , refl , refl

terminalMaxCutValidation :
  Disposition.publicTerminationReceiptPaid ≡ true
  × Disposition.nfipContinuationExceptionPaid ≡ true
  × Disposition.namedSuccessorComponentIdentityPaid ≡ false
  × Wade.dualCIAAndICCIOReceiptPaid ≡ true
  × Wade.primaryWadeTIARoleReceiptPaid ≡ false
  × Wade.secondaryWadeTIAClaimRetained ≡ true
  × Early.inQTel2005InvestmentChronologyPaid ≡ true
  × Early.ciaAnalystRefinement2005To2008Paid ≡ true
  × Early.nctcLiveDatabaseBetaSecondaryReceiptPaid ≡ true
  × Early.tiaAssetOrCodeTransferPaid ≡ false
  × Migration.programmeReconstitutionPromoted ≡ false
  × Migration.capabilityMigrationHypothesisLive ≡ true
  × Migration.networkPathCreatesDirectTransfer ≡ false
terminalMaxCutValidation =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl
