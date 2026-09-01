module DASHI.Analysis.RiemannG2HAConsumerFanoutPriorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact as Frontier

------------------------------------------------------------------------
-- CONSUMER-FANOUT PRIORITY INSIDE THE LAWFUL H_A FRONTIER
--
-- Cross-pollination inspiration: the merged Yang--Mills consumer-weighted
-- frontier ranks live proof leaves by declared downstream consumer fanout, but
-- does not let fanout manufacture theorem closure or activate prerequisites.
--
-- This RH owner reimplements only that generic planning idea on the H_A
-- carrier.  There is no theorem-strength transfer from Yang--Mills to RH.
-- The hard order is:
--
--   dependency-enabled probe
--     -> declared downstream consumer fanout
--     -> priority ranking among the enabled probes only.
------------------------------------------------------------------------

data HAConsumer : Set where
  admissibilityReceiptConsumer
  canonicalHXAgreementConsumer
  sameFormulaShiftConsumer
  sameWeilTransformShiftConsumer
  mathematicalHACompilerConsumer
  sourceAuditConsumer
  : HAConsumer

probeConsumers : HA.HARecoveryProbe → List HAConsumer
probeConsumers HA.recoverImplementationIdentity =
  admissibilityReceiptConsumer ∷
  canonicalHXAgreementConsumer ∷
  sameFormulaShiftConsumer ∷
  sameWeilTransformShiftConsumer ∷
  mathematicalHACompilerConsumer ∷ []
probeConsumers HA.recoverParameterizedAction =
  admissibilityReceiptConsumer ∷
  canonicalHXAgreementConsumer ∷
  sameFormulaShiftConsumer ∷
  sameWeilTransformShiftConsumer ∷
  mathematicalHACompilerConsumer ∷ []
probeConsumers HA.recoverAdmissibility =
  mathematicalHACompilerConsumer ∷ []
probeConsumers HA.recoverCanonicalHXAgreement =
  mathematicalHACompilerConsumer ∷ []
probeConsumers HA.recoverSameFormulaSpectralShift =
  mathematicalHACompilerConsumer ∷ []
probeConsumers HA.recoverSameWeilTransformShift =
  mathematicalHACompilerConsumer ∷ []
probeConsumers HA.recoverSourceProvenance =
  sourceAuditConsumer ∷ []
probeConsumers HA.compileProofRelevantHA = []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

probeFanoutScore : HA.HARecoveryProbe → Nat
probeFanoutScore probe = listLength (probeConsumers probe)

implementationFanoutIsFive :
  probeFanoutScore HA.recoverImplementationIdentity
  ≡ suc (suc (suc (suc (suc zero))))
implementationFanoutIsFive = refl

actionFanoutIsFive :
  probeFanoutScore HA.recoverParameterizedAction
  ≡ suc (suc (suc (suc (suc zero))))
actionFanoutIsFive = refl

provenanceFanoutIsOne :
  probeFanoutScore HA.recoverSourceProvenance ≡ suc zero
provenanceFanoutIsOne = refl

postTransportTheoremFanoutsAreOne :
  probeFanoutScore HA.recoverAdmissibility ≡ suc zero ×
  (probeFanoutScore HA.recoverCanonicalHXAgreement ≡ suc zero ×
  (probeFanoutScore HA.recoverSameFormulaSpectralShift ≡ suc zero ×
   probeFanoutScore HA.recoverSameWeilTransformShift ≡ suc zero))
postTransportTheoremFanoutsAreOne = refl , (refl , (refl , refl))

------------------------------------------------------------------------
-- Priority is proof-relevantly subordinate to ProbeEnabled.
------------------------------------------------------------------------

record PriorityCandidate
    (state : HA.HARecoveryState)
    (probe : HA.HARecoveryProbe) : Set where
  constructor priority-candidate
  field
    enabled : Frontier.ProbeEnabled state probe

open PriorityCandidate public

priorityCandidateScore :
  ∀ {state probe} → PriorityCandidate state probe → Nat
priorityCandidateScore {probe = probe} candidate = probeFanoutScore probe

initialImplementationPriority :
  PriorityCandidate Frontier.allMissingState HA.recoverImplementationIdentity
initialImplementationPriority =
  priority-candidate Frontier.implementationIdentityLive

initialActionPriority :
  PriorityCandidate Frontier.allMissingState HA.recoverParameterizedAction
initialActionPriority =
  priority-candidate Frontier.parameterizedActionLive

initialProvenancePriority :
  PriorityCandidate Frontier.allMissingState HA.recoverSourceProvenance
initialProvenancePriority =
  priority-candidate Frontier.sourceProvenanceLive

initialFormulaShiftCannotBecomePriorityCandidate :
  PriorityCandidate Frontier.allMissingState HA.recoverSameFormulaSpectralShift → ⊥
initialFormulaShiftCannotBecomePriorityCandidate candidate =
  Frontier.formulaShiftBlockedBeforeTransportedAction (enabled candidate)

------------------------------------------------------------------------
-- Exact initial-frontier classification.
--
-- The two mathematical producer probes occupy the five-consumer top class.
-- Provenance remains enabled but belongs to a distinct one-consumer audit
-- branch.  This is a planning priority only: either top probe still leaves the
-- other prerequisite open.
------------------------------------------------------------------------

data InitialFanoutClass : HA.HARecoveryProbe → Set where
  implementationTopFanout :
    InitialFanoutClass HA.recoverImplementationIdentity
  actionTopFanout :
    InitialFanoutClass HA.recoverParameterizedAction
  provenanceAuditFanout :
    InitialFanoutClass HA.recoverSourceProvenance

classifyInitialEnabledProbe :
  ∀ {probe} →
  Frontier.ProbeEnabled Frontier.allMissingState probe →
  InitialFanoutClass probe
classifyInitialEnabledProbe Frontier.implementationIdentityLive =
  implementationTopFanout
classifyInitialEnabledProbe Frontier.parameterizedActionLive =
  actionTopFanout
classifyInitialEnabledProbe Frontier.sourceProvenanceLive =
  provenanceAuditFanout

TopFanoutAtInitialFrontier : HA.HARecoveryProbe → Set
TopFanoutAtInitialFrontier probe =
  PriorityCandidate Frontier.allMissingState probe ×
  probeFanoutScore probe ≡ suc (suc (suc (suc (suc zero))))

implementationIsInitialTopFanout :
  TopFanoutAtInitialFrontier HA.recoverImplementationIdentity
implementationIsInitialTopFanout = initialImplementationPriority , refl

actionIsInitialTopFanout :
  TopFanoutAtInitialFrontier HA.recoverParameterizedAction
actionIsInitialTopFanout = initialActionPriority , refl

provenanceIsEnabledButNotInitialTopFanout :
  TopFanoutAtInitialFrontier HA.recoverSourceProvenance → ⊥
provenanceIsEnabledButNotInitialTopFanout (candidate , ())

------------------------------------------------------------------------
-- Once implementation + action are owned, fanout alone no longer separates
-- the four mathematical theorem consequences.  A later scheduler therefore
-- needs a genuinely independent discriminator (source availability, proof
-- cost, expected information gain, etc.) rather than inventing an ordering.
------------------------------------------------------------------------

postTransportAdmissibilityPriority :
  PriorityCandidate Frontier.postTransportState HA.recoverAdmissibility
postTransportAdmissibilityPriority =
  priority-candidate Frontier.admissibilityLive

postTransportHXPriority :
  PriorityCandidate Frontier.postTransportState HA.recoverCanonicalHXAgreement
postTransportHXPriority =
  priority-candidate Frontier.canonicalHXAgreementLive

postTransportFormulaPriority :
  PriorityCandidate Frontier.postTransportState HA.recoverSameFormulaSpectralShift
postTransportFormulaPriority =
  priority-candidate Frontier.sameFormulaShiftLive

postTransportWeilPriority :
  PriorityCandidate Frontier.postTransportState HA.recoverSameWeilTransformShift
postTransportWeilPriority =
  priority-candidate Frontier.sameWeilTransformShiftLive

postTransportFanoutCannotChooseAmongFourMathReceipts :
  priorityCandidateScore postTransportAdmissibilityPriority
  ≡ priorityCandidateScore postTransportHXPriority ×
  (priorityCandidateScore postTransportHXPriority
   ≡ priorityCandidateScore postTransportFormulaPriority ×
   priorityCandidateScore postTransportFormulaPriority
   ≡ priorityCandidateScore postTransportWeilPriority)
postTransportFanoutCannotChooseAmongFourMathReceipts =
  refl , (refl , refl)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record HAConsumerFanoutPriorityBoundary : Set where
  constructor ha-consumer-fanout-priority-boundary
  field
    fanoutMayActivateDisabledProbe : Bool
    fanoutMayActivateDisabledProbeIsFalse :
      fanoutMayActivateDisabledProbe ≡ false

    implementationAndActionShareInitialTopFanout : Bool
    implementationAndActionShareInitialTopFanoutIsTrue :
      implementationAndActionShareInitialTopFanout ≡ true

    provenanceIsMathematicallyTopFanoutAtInitialState : Bool
    provenanceIsMathematicallyTopFanoutAtInitialStateIsFalse :
      provenanceIsMathematicallyTopFanoutAtInitialState ≡ false

    fanoutAloneOrdersFourPostTransportMathReceipts : Bool
    fanoutAloneOrdersFourPostTransportMathReceiptsIsFalse :
      fanoutAloneOrdersFourPostTransportMathReceipts ≡ false

    highestFanoutAutomaticallyProvesReceipt : Bool
    highestFanoutAutomaticallyProvesReceiptIsFalse :
      highestFanoutAutomaticallyProvesReceipt ≡ false

    yangMillsCarrierTheoremTransferredIntoRH : Bool
    yangMillsCarrierTheoremTransferredIntoRHIsFalse :
      yangMillsCarrierTheoremTransferredIntoRH ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHAConsumerFanoutPriorityBoundary : HAConsumerFanoutPriorityBoundary
canonicalHAConsumerFanoutPriorityBoundary =
  ha-consumer-fanout-priority-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Rank only inside the proof-relevant H_A dependency frontier. At the all-missing state, implementation identity and source-native action each feed four theorem consequences plus final mathematical H_A compilation and therefore tie for the declared five-consumer top fanout; provenance remains independently enabled for source audit but has one declared consumer. Fanout cannot activate same-formula or same-Weil shift before transport. After implementation and action are owned, the four mathematical consequence probes all have equal one-consumer fanout, so fanout alone cannot justify a fake serial order there. A secondary consumer-relevant discriminator is then required. This reuses only the consumer-weighted-search architecture seen elsewhere in DASHI, not any Yang--Mills theorem on the RH carrier, and RH is not derived."
