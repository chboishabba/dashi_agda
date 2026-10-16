module DASHI.Economics.AICapitalPhaseRoadmap20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICapitalSOTAReconciliation20261016Exact as SOTA
import DASHI.Economics.AICapitalOutcomeSignatures20261016Exact as Outcome

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
  "aggregate CoreWeave customer cash; capital-spread lower bound; capacity-vintage and three-clock surfaces; provider segment costs; MI355X purchase/depreciation envelope; 37bp AI-linked credit spread cross-section; demand/distress SOTA surface"
  "named payer cash; workload-normalised provider serving cost; exact owned-node finance/PUE/operations/residual; serial GPU generations/refresh; realised generation ASP/utilisation/resale; enacted regulatory obligations and realised compliance costs"
  "each previously-open coordinate is populated from the same economic object and same declared horizon/basis, or explicitly bounded as unobservable"
  false

phase2Longitudinal : PhaseDeliverable
phase2Longitudinal = phase-deliverable
  "Phase 2 — longitudinal identification"
  longitudinalIdentification
  "dated state machinery, fixed-basket market series, open-weight production trajectory, debt/vintage exposure calendars"
  "repeat X_t under identical producer definitions; issuer-level spread/refinancing histories; generation-specific price/utilisation decay; customer-cash and contract-realisation histories"
  "at least two comparable later state points with unchanged measurement contracts, permitting trend/persistence rather than snapshot inference"
  false

phase3CausalPolicy : PhaseDeliverable
phase3CausalPolicy = phase-deliverable
  "Phase 3 — causal/policy attribution"
  causalAttribution
  "typed estimands, identification-family gates, exact review binding, Australian proposal chronology plus negative/control withdrawal observation"
  "measure enacted obligation -> actor-class realised cost -> entry/open-weight/concentration response with comparator/control and reviewed same-object identification receipt"
  "causal bridge is inhabited without chronology, correlation, review or policy salience substituting for identification; motive/capture remains a separate evidential claim"
  false

phase4OutcomeValidation : PhaseDeliverable
phase4OutcomeValidation = phase-deliverable
  "Phase 4 — real-world outcome / thesis falsification"
  outcomeValidation
  "explicit coexistence tests plus predeclared rival signatures for durable-rent expansion, commoditisation-with-volume-growth, refinancing stress, orderly capital rotation and policy/compliance moat"
  "populate the signature coordinates longitudinally and discriminate among rivals only when same-basis realised returns, funding/refinancing outcomes, scarcity-rent trajectories, utilisation and market-structure observations are available"
  "one or more hypotheses are discriminated without post-hoc redefining the consumer; currentOutcomePromotionReady remains false until those longitudinal payments exist"
  false

allNewGenericAbstractionFlagsFalse :
  (newGenericAbstractionNeeded phase0Architecture ≡ false) ×
  (newGenericAbstractionNeeded phase1EmpiricalCoordinates ≡ false) ×
  (newGenericAbstractionNeeded phase2Longitudinal ≡ false) ×
  (newGenericAbstractionNeeded phase3CausalPolicy ≡ false) ×
  (newGenericAbstractionNeeded phase4OutcomeValidation ≡ false)
allNewGenericAbstractionFlagsFalse = refl , refl , refl , refl , refl

sotaBubbleStillOpen : SOTA.bubbleEstablished SOTA.currentSOTAReconciliation ≡ false
sotaBubbleStillOpen = SOTA.bubbleStillNotEstablished

outcomePromotionStillOpen : Outcome.currentOutcomePromotionReady ≡ false
outcomePromotionStillOpen = refl

boundary : String
boundary =
  "The roadmap is measurement-first. Phase 0 generic architecture is paid. Phase 1 is the current max-cut: same-object cash/cost/hardware/policy coordinates. Phase 2 requires comparable repeated measurements before trajectory claims. Phase 3 permits causal policy claims only after realised obligations/costs/responses plus identification and review. Phase 4 now has rival outcome signatures fixed in advance; the remaining payment is longitudinal discrimination, not another narrative score."
