module DASHI.Economics.AICapitalPhaseRoadmap20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICapitalSOTAReconciliation20261016Exact as SOTA
import DASHI.Economics.AICapitalOutcomeSignatures20261016Exact as Outcome
import DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact as Fit
import DASHI.Economics.AICapitalPhase2Acquisition20261016Exact as Acquisition
import DASHI.Economics.AICoreWeaveSameObjectFinancingMaxCut20261016Exact as FinancingMax
import DASHI.Economics.AICoreWeaveSameObjectFinancingClock20261016Exact as FinancingClock
import DASHI.Economics.AICoreWeave2032BondRepricing20261016Exact as Bond
import DASHI.Economics.AICoreWeaveMicrosoftHistoricalRevenue20261016Exact as MicrosoftRevenue
import DASHI.Economics.AIAustraliaDataCentrePolicyShift20261016Exact as AUInfraPolicy
import DASHI.Economics.AIContractBackedFinancingReplication20261016Exact as FinancingReplication
import DASHI.Economics.AIFinancingCohortMatchedOutcomeExperiment20261017Exact as Cohort

data PhaseState : Set where
  structurallyPaid currentAcquisition longitudinalIdentification causalAttribution outcomeValidation : PhaseState

record PhaseDeliverable : Set where
  constructor phase-deliverable
  field
    phaseName : String
    state : PhaseState
    alreadyPaid : String
    nextDeliverable : String
    completionCriterion : String
    newGenericAbstractionNeeded : Bool

open PhaseDeliverable public

phase0Architecture : PhaseDeliverable
phase0Architecture = phase-deliverable
  "Phase 0 — architecture / attribution / non-collapse"
  structurallyPaid
  "capital graph, terminal-payer conductance, capital/inference/scarcity spreads, time-series state, observer non-descent, legal/policy attribution gates, human-review gate, fleet-age non-identifiability, stack-layer return separation"
  "maintain/deduplicate shared Core owners only when a landed generic owner removes branch-local duplication"
  "no remaining domain-generic economic ontology or score is required to answer a live residual"
  false

phase1EmpiricalCoordinates : PhaseDeliverable
phase1EmpiricalCoordinates = phase-deliverable
  "Phase 1 — same-object empirical coordinate acquisition"
  currentAcquisition
  "aggregate CoreWeave customer cash; historical Microsoft named recognised revenue; capacity-vintage surfaces; same-object CoreWeave contractual GPU depreciation 66-78 months with common six-year basis; project/customer-specific DDTL financing spreads; customer-credit-to-financing coupling; DDTL4 borrower-SPV to Polaris Forge 1 site mapping; DDTL3 named OpenAI/Phoenix 1 cash-control architecture, contract-realisation metric and private GPU-rack serial reporting; CRR equity-cure mechanism plus non-descent of covenant compliance to customer cash; current multi-generation rental ladder; commercial secondary-market residual-value envelope; provider segment costs and owned-node acquisition/depreciation envelopes; contract/cash-backed financing replicated through Nebius and IREN; GPU-backed SPV financing paid for Sharon AI; developer-level customer-prepayment plus project-debt/preferred-equity funding paid for the AIB/Nebius 50 MW project"
  "public OpenAI customer-cash versus CRR-cure decomposition; public contract-realisation ratio; public GPU serial/generation inventory; exact financed MW/count; workload-normalised provider serving cost; exact owned-node PUE/operations; CoreWeave-owned realised residual/resale receipts; serial refresh/retirement; realised generation ASP/utilisation; realised enacted-obligation compliance costs"
  "each previously-open coordinate is populated from the same economic object and same declared horizon/basis, or explicitly classified as privately measured but publicly unobserved; covenant/equity-cure values must not be collapsed into customer cash; common financing mechanisms must not be promoted to common realised returns"
  false

phase2Longitudinal : PhaseDeliverable
phase2Longitudinal = phase-deliverable
  "Phase 2 — longitudinal and matched-cohort identification"
  longitudinalIdentification
  "dated state machinery, fixed-basket market series, open-weight production trajectory, debt/vintage scenario calendars, same-issuer CoreWeave CDS deterioration, same-instrument 9.625-percent 2032 note repricing, cross-company/cross-layer financing replication, and a five-subject matched-cohort contract covering CoreWeave, Nebius, IREN, Sharon AI and the AIB/Nebius developer layer"
  "repeat full X_t under identical producer definitions; acquire matched layer/customer-credit/instrument/collateral/prepayment/maturity/spread/capex denominators; compare realised project-return/refinancing/default outcomes across the five-subject cohort; repeat same-instrument bond/CDS observations; customer-cash-versus-cure histories; same-generation price/utilisation/resale decay; named contract-realisation histories; repeat Vercel model/provider shares under the same published methodology"
  "at least two comparable later state points across each promoted consumer and multiple financing subjects under unchanged measurement contracts, with validator-side financing similarity kept distinct from consumer-side realised return/distress; one stressed issuer cannot select the cohort regime"
  false

phase3CausalPolicy : PhaseDeliverable
phase3CausalPolicy = phase-deliverable
  "Phase 3 — causal/policy attribution"
  causalAttribution
  "typed estimands, identification-family gates, exact review binding, withdrawal of the earlier general mandatory model/deployment guardrail proposal, current Data Centre Expectations affecting Commonwealth prioritisation, and a separately announced future mandatory infrastructure-standards route for large data centres"
  "for model/deployment policy and infrastructure policy separately: identify the actually enacted/operative obligation -> actor-class realised cost -> entry/open-weight/project-finance/concentration response with comparator/control -> reviewed same-object causal-identification receipt"
  "proposal/announcement is not enactment; infrastructure externality rules do not become a model/open-weight moat by analogy; causal bridge is inhabited without chronology, correlation, review or policy salience substituting for identification; motive/capture remains a separate evidential claim"
  false

phase4OutcomeValidation : PhaseDeliverable
phase4OutcomeValidation = phase-deliverable
  "Phase 4 — real-world outcome / thesis falsification"
  outcomeValidation
  "predeclared rival signatures plus current compatibility surface: refinancing stress remains strongly compatible; commoditisation-with-volume-growth remains strongly compatible; orderly capital rotation is co-leading on selected coordinates because open-weight expansion coexists with closed-model spend growth and provider intermediation; Anthropic's reported adjusted profitability is a bounded durable-rent counterweight; contract-backed financing now replicates across provider/neocloud/developer layers; no terminal regime is selected"
  "populate missing signature coordinates longitudinally and discriminate among rivals only when same-basis realised returns, matched-cohort financing/refinancing outcomes, provider-layer rent trajectories, scarcity-rent trajectories, utilisation, customer-cash decomposition and market-structure observations are available"
  "one or more hypotheses are discriminated without post-hoc redefining the consumer; currentOutcomePromotionReady and anyTerminalRegimeSelected remain false until those longitudinal payments exist"
  false

allNewGenericAbstractionFlagsFalse :
  (newGenericAbstractionNeeded phase0Architecture ≡ false) ×
  (newGenericAbstractionNeeded phase1EmpiricalCoordinates ≡ false) ×
  (newGenericAbstractionNeeded phase2Longitudinal ≡ false) ×
  (newGenericAbstractionNeeded phase3CausalPolicy ≡ false) ×
  (newGenericAbstractionNeeded phase4OutcomeValidation ≡ false)
allNewGenericAbstractionFlagsFalse = refl , refl , refl , refl , refl

phase2AcquisitionCoordinatesPaid : Acquisition.issuerCreditTrajectoryPaid Acquisition.currentPhase2AcquisitionState ≡ true
phase2AcquisitionCoordinatesPaid = refl

sameObjectFinancingMaxCutPaid : FinancingMax.sameObjectDepreciationClock FinancingMax.coreWeaveSameObjectFinancingStatus ≡ true
sameObjectFinancingMaxCutPaid = FinancingMax.sameObjectDepreciationClockPaid

contractRealisationCureNonDescentPaid : FinancingMax.covenantComplianceInsufficientForCustomerCash FinancingMax.coreWeaveSameObjectFinancingStatus ≡ true
contractRealisationCureNonDescentPaid = FinancingMax.covenantComplianceInsufficientForCustomerCashPaid

sameInstrumentBondRepricingPaid : Bond.sameInstrumentLongitudinalRepricing Bond.coreWeave2032BondRepricing ≡ true
sameInstrumentBondRepricingPaid = Bond.sameInstrumentLongitudinalRepricingPaid

historicalNamedMicrosoftRevenuePaid : MicrosoftRevenue.historicalNamedRevenue MicrosoftRevenue.coreWeaveMicrosoft2025Revenue ≡ true
historicalNamedMicrosoftRevenuePaid = MicrosoftRevenue.historicalNamedRevenuePaid

generic36To48MonthClockNotSameObject : FinancingClock.generic36To48MonthHorizonSameObject FinancingClock.coreWeaveSameObjectFinancingClock ≡ false
generic36To48MonthClockNotSameObject = FinancingClock.generic36To48MonthHorizonIsNotSameObject

realisedRefinancingStillOpen : Bond.realisedRefinancingCostPaid Bond.coreWeave2032BondRepricing ≡ false
realisedRefinancingStillOpen = refl

australianPolicyLocusShiftPaid :
  (AUInfraPolicy.generalMandatoryModelGuardrailsProceeding AUInfraPolicy.currentPolicyShift ≡ false) ×
  (AUInfraPolicy.currentDataCentreExpectations AUInfraPolicy.currentPolicyShift ≡ true) ×
  (AUInfraPolicy.announcedFutureMandatoryDataCentreStandards AUInfraPolicy.currentPolicyShift ≡ true)
australianPolicyLocusShiftPaid = AUInfraPolicy.policyLocusShiftPaid

australianDataCentreEnactmentStillOpen : AUInfraPolicy.newMandatoryDataCentreDutyEnacted AUInfraPolicy.currentPolicyShift ≡ false
australianDataCentreEnactmentStillOpen = AUInfraPolicy.enactmentStillOpen

crossCompanyFinancingReplicationPaid : FinancingReplication.crossCompanyMechanismReplication ≡ true
crossCompanyFinancingReplicationPaid = FinancingReplication.crossCompanyReplicationPaid

crossLayerFinancingReplicationPaid : FinancingReplication.crossLayerMechanismReplication ≡ true
crossLayerFinancingReplicationPaid = FinancingReplication.crossLayerReplicationPaid

matchedFinancingCohortDeclared : Cohort.matchedComparatorDeclared Cohort.currentCohortExperiment ≡ true
matchedFinancingCohortDeclared = Cohort.matchedComparatorContractPaid

matchedCohortRealisedOutcomesStillOpen : Cohort.allRealisedOutcomeCoordinatesPaid Cohort.currentCohortExperiment ≡ false
matchedCohortRealisedOutcomesStillOpen = Cohort.realisedOutcomesRemainOpen

orderlyRotationCounterweightPaid : Fit.supportedCoordinates Fit.orderlyCapitalRotationFit ≡ 6
orderlyRotationCounterweightPaid = Fit.orderlyRotationNowCoLeadingOnSelectedCoordinates

sotaBubbleStillOpen : SOTA.bubbleEstablished SOTA.currentSOTAReconciliation ≡ false
sotaBubbleStillOpen = SOTA.bubbleStillNotEstablished

outcomePromotionStillOpen : Outcome.currentOutcomePromotionReady ≡ false
outcomePromotionStillOpen = refl

compatibilityDoesNotSelectRegime : Fit.anyTerminalRegimeSelected ≡ false
compatibilityDoesNotSelectRegime = refl

boundary : String
boundary =
  "The roadmap is measurement-first and now materially more comparative. Phase 1 has identified private lender measurement surfaces for named OpenAI/Phoenix 1 customer cash, contract realization and GPU serials and has replicated customer/contract-linked financing across Nebius, IREN, Sharon AI and the AIB/Nebius developer layer rather than treating CoreWeave as the sole mechanism specimen. Phase 2 is now explicitly a matched-cohort outcome experiment: financing-mechanism similarity is only validator-side structure; the consumer is realised project return, refinancing, default/restructuring and persistence. The cohort must match layer, customer-credit, instrument, collateral, prepayment, maturity, spread/coupon, capex and outcome definitions before comparison. Phase 3 remains split by regulatory locus. Phase 4 keeps refinancing stress, commoditisation and orderly capital rotation simultaneously live; common contract-backed financing does not select any regime without realised longitudinal cash and return outcomes."
