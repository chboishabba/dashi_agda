module DASHI.Unified.WealthTaxEvidenceNonPromotionTOEExact where

-- TOE consumer for original DASHI Economics/Philosophy/Sociology owners.
-- No new political philosophy, economic causal law or empirical certificate.
-- The finite proofs are source-written by the respective existing modules.
-- Research direction: Johl Brown; ChatGPT assisted integration 2026-10-27.
-- Original Piketty, Crenshaw, Fraser, Collins, Arnstein, Marx, FATF, OECD,
-- Fagereng et al. and historical sources retain their dated original claims.
-- Ibrahim 2017 FLN navigation is not a wealth-tax proof or Monster action.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Economics.WealthInheritanceVacancyTaxMaxCut20261027Exact as Base
import DASHI.Economics.WealthTaxPowerCareSociologyBidi20261027Exact as Soc
import DASHI.Economics.WealthTaxFiscalTransmissionControlBidi20261027Exact as Fiscal

-- Flow/stock tax bases are separate even when numerical liabilities agree.
toeWealthIsNotIncomeTax :
  Base.incomeHundredAboveThreshold ≡
  Base.wealthHundredAboveThreshold → ⊥
toeWealthIsNotIncomeTax = Base.incomeTaxIsNotStockCap

-- Corporate multinational top-ups do not equal a personal stock cap.
toeGloBEIsNotPersonalStockCap :
  Base.multinationalGloBEProfitTopUp ≡
  Base.wealthHundredAboveThreshold → ⊥
toeGloBEIsNotPersonalStockCap =
  Base.corporateMinimumTaxIsNotPersonalWealthCap

-- Hypothetical idle equity and statutory vacant residential property do not
-- share a legal taxable object merely because first-year rates can match.
toeProposedIdleEquityLevyIsNotVacancyTax :
  Base.proposedDurationEscalatingIdleEquityLevy ≡
  Base.vacantHomesStatusLevy → ⊥
toeProposedIdleEquityLevyIsNotVacancyTax =
  Base.idleEquityIsNotVacantHouse

toeIdleEquityAIScheduleDoesNotCreateStatute :
  Base.AIIdleEquityProposalIsEnactedLaw → ⊥
toeIdleEquityAIScheduleDoesNotCreateStatute =
  Base.aiIdleEquitySuggestionCannotSelfEnact

-- Source-written exact witness: one tax observation cannot recover votes.
toeTaxReceiptDoesNotDetermineVoting :
  INF.FactorsThrough Soc.assessedTax Soc.controllingVotes → ⊥
toeTaxReceiptDoesNotDetermineVoting =
  Soc.votesCannotFactorThroughTaxReceipt

-- Source-written exact witness: the same observation cannot recover care.
toeTaxReceiptDoesNotDetermineCare :
  INF.FactorsThrough Soc.assessedTax Soc.accessibleCareCapacity → ⊥
toeTaxReceiptDoesNotDetermineCare =
  Soc.careCannotFactorThroughTaxReceipt

-- The tax amount cannot identify whether the liability was paid.
toeAssessmentDoesNotDetermineCashCollection :
  INF.FactorsThrough Fiscal.assessedLiability Fiscal.taxPaidCash → ⊥
toeAssessmentDoesNotDetermineCashCollection =
  Fiscal.liabilityAloneDoesNotDetermineCollection

-- The cash receipt cannot determine which budget appropriations followed.
toeCashCollectionDoesNotDetermineCareAppropriation :
  INF.FactorsThrough Fiscal.taxPaidCash Fiscal.appropriatedCareCash → ⊥
toeCashCollectionDoesNotDetermineCareAppropriation =
  Fiscal.cashReceiptsDoNotDetermineCareAppropriation

-- A matching AI-risk feature alone does not identify legal tax liability.
toeAIRiskScoreDoesNotDetermineTaxLiability :
  INF.FactorsThrough
    Fiscal.auditSignal Fiscal.auditedIllustrativeWealthLiability → ⊥
toeAIRiskScoreDoesNotDetermineTaxLiability =
  Fiscal.riskSignalAloneIsNotTaxAuthority

-- Interpretive source provenance cannot certify real-world tax incidence.
toeAuthoredPoliticalTextDoesNotProveOutcome :
  Base.AnyPoliticalTextProvesContemporaryPolicyOutcome → ⊥
toeAuthoredPoliticalTextDoesNotProveOutcome =
  Base.authoredTheoryIsNotOutcomeProof

toeFiniteWorldsDoNotProvePolicyCausation :
  Soc.FiniteTaxCounterexampleProvesCausalOutcome → ⊥
toeFiniteWorldsDoNotProvePolicyCausation =
  Soc.finiteWitnessDoesNotCertifyRealWorldCausation

toeInequalityTheoryDoesNotFixUniversalTaxRate :
  Soc.SocialTheoryDictatesOneTaxRate → ⊥
toeInequalityTheoryDoesNotFixUniversalTaxRate =
  Soc.socialTheoryDoesNotDictateOneTaxRate

-- Repository import alone is a source-reachability relationship.
-- It is NOT an Agda kernel certification receipt or a substitute for an
-- observed, exact-head compiler run. No ESD imports are changed.
