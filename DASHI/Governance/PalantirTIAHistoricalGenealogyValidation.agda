module DASHI.Governance.PalantirTIAHistoricalGenealogyValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

-- RED-first contract: production owners intentionally added afterwards.
import DASHI.Governance.PalantirTIAHistoricalGenealogyExact as G
import DASHI.Governance.PalantirTIAPartyBenefitDistributionExact as Distribution
import DASHI.Governance.PalantirTIAInvestigativeParetoSnowballExact as Pareto

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

-- Distributional max-cut: first-/second-/third-order consequence is a path
-- coordinate, not a truth or intent score.  Aggregate national-security value
-- cannot recover party benefit, burden, voice, or authority/control.
distributionValidation :
  Distribution.firstOrderBenefitDoesNotEstablishIntent ≡ true
  × Distribution.secondOrderBenefitDoesNotEstablishControl ≡ true
  × Distribution.thirdOrderBenefitDoesNotEstablishCausation ≡ true
  × Distribution.sameAggregateCannotRecoverPartyDistribution ≡ true
  × Distribution.currentStrongPrivatizationClaimStillBlocked ≡ true
distributionValidation = refl , refl , refl , refl , refl

-- Acquisition max-cut: exact source/object payment and live-fibre splitting
-- dominate broad keyword sweeping; a route priority never pays truth/authority.
paretoValidation :
  Pareto.officialWadeTIARoleOnFrontier ≡ true
  × Pareto.tiaDispositionOnFrontier ≡ true
  × Pareto.earlyPalantirCIAIQTOnFrontier ≡ true
  × Pareto.broadKeywordSweepOffFrontier ≡ true
  × Pareto.paretoPriorityCreatesHistoricalTruth ≡ false
  × Pareto.offFrontierDeletesRequirement ≡ false
paretoValidation = refl , refl , refl , refl , refl , refl
