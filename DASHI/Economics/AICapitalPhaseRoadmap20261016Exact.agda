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
  "aggregate CoreWeave customer cash; historical Microsoft named recognised revenue; capital-spread lower bound; capacity-vintage surfaces; same-object CoreWeave financing depreciation 66-78 months with common six-year basis; project/customer-specific DDTL financing spreads; explicit customer-credit-to-financing coupling; DDTL4 borrower-SPV to Polaris Forge 1 site mapping; current multi-generation rental ladder; commercial secondary-market residual-value envelope; provider segment costs; MI355X purchase/depreciation envelope; 37bp AI-linked credit spread cross-section; demand/distress SOTA surface; OpenAI reported multi-year negative-FCF/external-financing dependence; current Australian operative-policy baseline"
  "named current payer cash; workload-normalised provider serving cost; exact owned-node PUE/operations; CoreWeave-owned realised residual/resale receipts; exact financed GPU generation/count/MW and associated customer identities; serial GPU refresh/retirement; realised generation ASP/utilisation; realised enacted-obligation compliance costs"
  "each previously-open coordinate is populated from the same economic object and same declared horizon/basis, or explicitly bounded as unobservable; commercial/private-reporting proxies remain separate from audited realised ledgers"
  false

phase2Longitudinal : PhaseDeliverable
phase2Longitudinal = phase-deliverable
  "Phase 2 — longitudinal identification"
  longitudinalIdentification
  "dated state machinery, fixed-basket market series, open-weight production trajectory, debt/vintage scenario calendars, same-issuer CoreWeave CDS deterioration, and a stronger same-instrument 9.625-percent 2032 note repricing from issue coupon to above-15-percent October yield"
  "repeat the full X_t under identical producer definitions; repeated same-instrument yields plus realised refinancing transactions/default/restructuring; same-generation price/utilisation/resale decay; named customer-cash and contract-realisation histories"
  "at least two comparable later state points across each promoted consumer with unchanged measurement contracts, permitting persistence/regime inference rather than one stressed issuer/instrument coordinate"
  false

phase3CausalPolicy : PhaseDeliverable
phase3CausalPolicy = phase-deliverable
  "Phase 3 — causal/policy attribution"
  causalAttribution
  "typed estimands, identification-family gates, exact review binding, proposal chronology, proposal withdrawal/control observation, and current baseline of existing-law regulation plus AI Safety Institute/guidance rather than the abandoned general mandatory-guardrail proposal"
  "measure enacted obligation -> actor-class realised cost -> entry/open-weight/concentration response with comparator/control and reviewed same-object identification receipt"
  "causal bridge is inhabited without chronology, correlation, review or policy salience substituting for identification; motive/capture remains a separate evidential claim"
  false

phase4OutcomeValidation : PhaseDeliverable
phase4OutcomeValidation = phase-deliverable
  "Phase 4 — real-world outcome / thesis falsification"
  outcomeValidation
  "predeclared rival signatures plus a current compatibility surface: selected coordinates most strongly support refinancing-stress and commoditisation-with-volume-growth, while orderly capital rotation remains materially compatible and no terminal regime is selected"
  "populate the missing signature coordinates longitudinally and discriminate among rivals only when same-basis realised returns, funding/refinancing outcomes, scarcity-rent trajectories, utilisation and market-structure observations are available"
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

sameInstrumentBondRepricingPaid : Bond.sameInstrumentLongitudinalRepricing Bond.coreWeave2032BondRepricing ≡ true
sameInstrumentBondRepricingPaid = Bond.sameInstrumentLongitudinalRepricingPaid

historicalNamedMicrosoftRevenuePaid : MicrosoftRevenue.historicalNamedRevenue MicrosoftRevenue.coreWeaveMicrosoft2025Revenue ≡ true
historicalNamedMicrosoftRevenuePaid = MicrosoftRevenue.historicalNamedRevenuePaid

generic36To48MonthClockNotSameObject : FinancingClock.generic36To48MonthHorizonSameObject FinancingClock.coreWeaveSameObjectFinancingClock ≡ false
generic36To48MonthClockNotSameObject = FinancingClock.generic36To48MonthHorizonIsNotSameObject

realisedRefinancingStillOpen : Bond.realisedRefinancingCostPaid Bond.coreWeave2032BondRepricing ≡ false
realisedRefinancingStillOpen = refl

sotaBubbleStillOpen : SOTA.bubbleEstablished SOTA.currentSOTAReconciliation ≡ false
sotaBubbleStillOpen = SOTA.bubbleStillNotEstablished

outcomePromotionStillOpen : Outcome.currentOutcomePromotionReady ≡ false
outcomePromotionStillOpen = refl

compatibilityDoesNotSelectRegime : Fit.anyTerminalRegimeSelected ≡ false
compatibilityDoesNotSelectRegime = refl

boundary : String
boundary =
  "The roadmap is measurement-first and now materially more same-object. Phase 1 has corrected the generic 36-48 month lender-horizon shortcut using CoreWeave's own filed GPU-backed agreements, which disclose contractual depreciation around 66-78 months and commonly six years; project financing rates and availability are contract/customer specific, customer credit directly enters financing terms, and DDTL4 is source-joined through the same borrower SPV to identified Polaris Forge 1 lease space. Historical Microsoft named recognised revenue is paid without de-anonymising 2026 or creating named cash. Phase 2 now contains both same-issuer CDS deterioration and a same-instrument 2032-note repricing of at least 5.375 percentage points versus issue coupon, while realised refinancing/default outcomes remain open. Phase 4 continues to favour no terminal regime until realised longitudinal cash, asset and financing outcomes discriminate the predeclared rivals."
