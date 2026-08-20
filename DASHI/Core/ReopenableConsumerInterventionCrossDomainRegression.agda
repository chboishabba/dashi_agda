module DASHI.Core.ReopenableConsumerInterventionCrossDomainRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using ([])

import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity
import DASHI.Core.AuthorityPreservingFutureAbstractionExact as FutureAuthority
import DASHI.Core.AuthorityPromotionHierarchyExact as AuthorityHierarchy
import DASHI.Core.CompositionalComplianceExact as Compliance
import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Core.ConsumerObserverJoinResidualExact as ObserverResidual
import DASHI.Core.ConsumerSafeFidelityEscalationExact as Escalation
import DASHI.Core.EvidenceReliabilityPolarityExact as Polarity
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel
import DASHI.Core.SelectiveAuthorityCertificateExact as Selective
import DASHI.Core.TypedEvidenceDependencyExact as Evidence

------------------------------------------------------------------------
-- 1. Consumer relativity: one coarse projection is safe for a constant public
-- consumer but not for a finer thermal/semantic/physical consumer.
------------------------------------------------------------------------

data Fine : Set where
  left right : Fine

data Coarse : Set where
  coarse : Coarse

data OneAction : Set where
  tick : OneAction

data OneConsumer : Set where
  public : OneConsumer

data Obs : Set where
  sameObs differentObs : Obs

stepFine : OneAction → Fine → Fine
stepFine tick state = state

observePublic : OneConsumer → Fine → Obs
observePublic public left = sameObs
observePublic public right = sameObs

declaredPublic : OneConsumer → OneAction → Set
declaredPublic public tick = ⊤

authorityPublic : OneConsumer → Fine → Governed.AuthorityDecision
authorityPublic public state = Governed.promote

publicSystem :
  Governed.ConsumerIndexedGovernedTransition Fine OneAction OneConsumer Obs
publicSystem =
  Governed.consumerIndexedGovernedTransition
    stepFine observePublic declaredPublic authorityPublic

project : Fine → Coarse
project state = coarse

coarseStep : OneAction → Coarse → Coarse
coarseStep tick coarse = coarse

coarseObserve : OneConsumer → Coarse → Obs
coarseObserve public coarse = sameObs

coarseAuthority : OneConsumer → Coarse → Governed.AuthorityDecision
coarseAuthority public coarse = Governed.promote

publicAbstraction : Governed.ConsumerSafeAbstraction publicSystem project
publicAbstraction =
  Governed.consumerSafeAbstraction
    coarseStep coarseObserve coarseAuthority
    (λ action state → refl)
    (λ consumer state → refl)
    (λ consumer state → refl)

publicStatesEquivalentAtEveryRequestedDepth :
  (depth : Nat) →
  Governed.FutureEquivalent publicSystem public depth left right
publicStatesEquivalentAtEveryRequestedDepth depth =
  Governed.sameProjectionFutureEquivalent
    publicAbstraction public depth refl

------------------------------------------------------------------------
-- Explicit downstream decision preservation strengthens observation/authority
-- preservation without claiming fine-state identity.
------------------------------------------------------------------------

data Decision : Set where allow : Decision

fineDecision : OneConsumer → Fine → Decision
fineDecision public state = allow

coarseDecision : OneConsumer → Coarse → Decision
coarseDecision public coarse = allow

decisionSafe :
  FutureAuthority.DecisionPreservingAbstraction
    publicSystem project publicAbstraction
decisionSafe =
  FutureAuthority.decisionPreservingAbstraction
    fineDecision coarseDecision (λ consumer state → refl)

publicStatesGovernedFutureAgree :
  (depth : Nat) →
  FutureAuthority.GovernedFutureAgreement
    publicSystem fineDecision public depth left right
publicStatesGovernedFutureAgree depth =
  FutureAuthority.sameProjectionGivesGovernedFutureAgreement
    publicAbstraction decisionSafe public depth refl

------------------------------------------------------------------------
-- A second consumer on the same fine/coarse carrier distinguishes the states,
-- giving a literal descent defect.
------------------------------------------------------------------------

observeFineConsumer : Fine → Obs
observeFineConsumer left = sameObs
observeFineConsumer right = differentObs

sameObsNotDifferentObs : sameObs ≡ differentObs → ⊥
sameObsNotDifferentObs ()

fineConsumerDescentDefect :
  Kernel.ConsumerDescentDefect project observeFineConsumer
fineConsumerDescentDefect =
  Kernel.consumerDescentDefect
    left right refl sameObsNotDifferentObs

------------------------------------------------------------------------
-- 2. Selective authority: abstention selects the independent anchor.
------------------------------------------------------------------------

data Input : Set where input : Input
data Candidate : Set where candidate : Candidate
data Anchor : Set where anchor : Anchor

abstainingAuthority : Selective.SelectiveAuthority Input Candidate Anchor
abstainingAuthority =
  Selective.selectiveAuthority
    (λ _ → anchor)
    (λ _ _ → Governed.abstain)
    "cross-domain abstention regression"

abstentionPreservesAnchor :
  Selective.selectCanonical abstainingAuthority input candidate
  ≡ Selective.selectedAnchor anchor
abstentionPreservesAnchor =
  Selective.abstainSelectsAnchor
    abstainingAuthority input candidate refl

------------------------------------------------------------------------
-- 3. Adaptive fidelity: equality is a trivial but exact discrepancy bound and
-- therefore lies inside an equality-stable Boolean consumer margin.
------------------------------------------------------------------------

pair : Fidelity.FidelityPair ⊤ Bool
pair = Fidelity.fidelityPair
  (λ _ → true)
  (λ _ → true)
  "cheap"
  "materialised"

bounded : Fidelity.BoundedDiscrepancy pair
bounded = Fidelity.boundedDiscrepancy
  _≡_
  "exact equality regression"
  []
  (λ _ → refl)

identityBool : Bool → Bool
identityBool x = x

margin : Fidelity.ConsumerDecisionMargin identityBool
margin = Fidelity.consumerDecisionMargin
  _≡_
  (λ same → same)
  "identity Boolean consumer equality margin"

inside : Fidelity.FidelityInsideConsumerMargin bounded margin
inside = Fidelity.fidelityInsideConsumerMargin (λ same → same)

lowAndHighDecisionsAgree :
  identityBool (Fidelity.low pair tt)
  ≡ identityBool (Fidelity.high pair tt)
lowAndHighDecisionsAgree =
  Fidelity.lowFidelityDecisionIsSafe bounded margin inside tt

certifiedLowExecution :
  Escalation.FidelityDecisionAt pair identityBool margin tt
certifiedLowExecution = Escalation.certifiedLow refl

certifiedLowUsesLowFidelity :
  Escalation.dispositionFromEvidence certifiedLowExecution
  ≡ Escalation.useLow
certifiedLowUsesLowFidelity = refl

------------------------------------------------------------------------
-- 4. Proof-carrying compliance composition keeps the intermediate carrier.
------------------------------------------------------------------------

First : ⊤ → ⊤ → Set
First _ _ = ⊤

Second : ⊤ → ⊤ → Set
Second _ _ = ⊤

firstStage : Compliance.CertifiedStage ⊤ ⊤ First
firstStage = Compliance.certifiedStage tt tt tt "first" "producer-a"

secondStage : Compliance.CertifiedStage ⊤ ⊤ Second
secondStage = Compliance.certifiedStage tt tt tt "second" "producer-b"

composedCompliance : Compliance.CompositeCompliance First Second tt tt
composedCompliance =
  Compliance.composeCertifiedStages firstStage secondStage refl

------------------------------------------------------------------------
-- 5. Provenance-root multiplicity is not independence.
------------------------------------------------------------------------

data Root : Set where root0 root1 : Root

data Payload : Set where payload0 payload1 : Payload

evidenceA : Evidence.EvidenceItem Root Payload
evidenceA = Evidence.evidenceItem root0 payload0

evidenceB : Evidence.EvidenceItem Root Payload
evidenceB = Evidence.evidenceItem root0 payload1

sameEpisodeCannotBeCertifiedIndependent :
  Evidence.ProvenanceIndependent evidenceA evidenceB → ⊥
sameEpisodeCannotBeCertifiedIndependent =
  Evidence.sameRootContradictsProvenanceIndependence refl

------------------------------------------------------------------------
-- 6. Low reliability becomes ignorance, not opposition.
------------------------------------------------------------------------

untrustedSupportBecomesIgnorance :
  Polarity.discountByReliability false Kernel.support ≡ Kernel.ignorance
untrustedSupportBecomesIgnorance = refl

untrustedSupportCannotBecomeOpposition :
  Polarity.discountByReliability false Kernel.support ≡ Kernel.opposition → ⊥
untrustedSupportCannotBecomeOpposition =
  Polarity.lowReliabilityCannotCreateOpposition Kernel.support

------------------------------------------------------------------------
-- 7. Authority can reach actionability only through the declared adjacent
-- promotion path.  The exact chain evidence remains a separate obligation.
------------------------------------------------------------------------

fullAuthorityPath :
  AuthorityHierarchy.PromotionPath Kernel.computed Kernel.actionable
fullAuthorityPath = AuthorityHierarchy.computedToActionablePath

------------------------------------------------------------------------
-- 8. Hot consumer state plus cold residual can reopen the exact fine carrier.
------------------------------------------------------------------------

hotFine : Fine → Coarse
hotFine state = coarse

residualFine : Fine → Fine
residualFine state = state

reopenFine : Coarse → Fine → Fine
reopenFine coarse state = state

recoverableFine : ObserverResidual.RecoverableHotCold Fine Coarse Fine
recoverableFine =
  ObserverResidual.recoverableHotCold
    hotFine residualFine reopenFine (λ state → refl)

sameHotResidualReopensSameFine :
  {x y : Fine} →
  hotFine x ≡ hotFine y →
  residualFine x ≡ residualFine y →
  x ≡ y
sameHotResidualReopensSameFine =
  ObserverResidual.sameHotAndResidualSameFine recoverableFine
