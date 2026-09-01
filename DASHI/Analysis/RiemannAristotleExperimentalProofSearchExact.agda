module DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Cut
import DASHI.Analysis.RiemannAristotlePoleQuotientLeanReturn8889Exact as Return
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice

------------------------------------------------------------------------
-- RH POLE-QUOTIENT CUT AS EXPERIMENT-DESIGNED PROOF SEARCH
------------------------------------------------------------------------

data RHResearchSocket : Set where
  offOrdinateSocket gammaSocket clusterMarginSocket : RHResearchSocket

data RHResearchMove : Set where
  attackOffOrdinateCancellation
  payGammaResidual
  instantiateClusterMargin
  auditExternalAnalyticDonor
  : RHResearchMove

data ResearchOutcome : Set where
  openOutcome
  theoremOwned
  boundOwnedButConsumerOpen
  refutedRoute
  : ResearchOutcome

MovePays : RHResearchMove → RHResearchSocket → Set
MovePays attackOffOrdinateCancellation offOrdinateSocket = ⊤
MovePays payGammaResidual gammaSocket = ⊤
MovePays instantiateClusterMargin clusterMarginSocket = ⊤
MovePays _ _ = ⊥

currentOutcome : RHResearchSocket → ResearchOutcome
currentOutcome offOrdinateSocket = openOutcome
currentOutcome gammaSocket = boundOwnedButConsumerOpen
currentOutcome clusterMarginSocket = theoremOwned

record AnalyticDonorAudit : Set where
  constructor analytic-donor-audit
  field
    donorName : String
    donorReference : String
    TargetSocket : RHResearchSocket
    literalCarrierBridge : Set
    bridgeReference : String

open AnalyticDonorAudit public

record RHResearchCostSurface : Set₁ where
  constructor rh-research-cost-surface
  field
    cost : RHResearchMove → Nat
    declared : RHResearchMove → Set
    costReference : String
    admissibilityReference : RHResearchMove → String

open RHResearchCostSurface public

moveInformation : RHResearchCostSurface → RHResearchMove → Choice.InformationMove
moveInformation surface move =
  Choice.informationMove
    Choice.increaseFidelity
    (cost surface move)
    "RH pole-quotient proof-search move"
    (costReference surface)
    (admissibilityReference surface move)

record CheapestDeclaredSocketMove
    (surface : RHResearchCostSurface)
    (socket : RHResearchSocket) : Set₁ where
  constructor cheapest-declared-socket-move
  field
    selected : RHResearchMove
    selectedDeclared : declared surface selected
    selectedPays : MovePays selected socket
    minimal :
      (alternative : RHResearchMove) →
      declared surface alternative →
      MovePays alternative socket →
      cost surface selected ≤ cost surface alternative

open CheapestDeclaredSocketMove public

------------------------------------------------------------------------
-- Exact cross-prover feedback.
------------------------------------------------------------------------

clusterMarginExperimentSucceededInLean :
  Return.quantitativeClusterMarginOwned Return.canonicalPoleQuotientLeanReturn8889
  ≡ true
clusterMarginExperimentSucceededInLean = refl

gammaExperimentProducedBoundButDidNotCloseConsumer :
  Return.gammaUniformBoundOwned Return.canonicalPoleQuotientLeanReturn8889 ≡ true
  ×
  Return.gammaBoundClosesRequiredAccuracyWindow
    Return.canonicalPoleQuotientLeanReturn8889 ≡ false
gammaExperimentProducedBoundButDidNotCloseConsumer = refl , refl

offOrdinateExperimentStillOpen :
  Return.offOrdinateEvaluationOwned Return.canonicalPoleQuotientLeanReturn8889
  ≡ false
offOrdinateExperimentStillOpen = refl

budgetCircularityRouteRefutedInLean :
  Return.budgetCircularityNoGoOwned Return.canonicalPoleQuotientLeanReturn8889
  ≡ true
budgetCircularityRouteRefutedInLean = refl

genericContradictionAlgebraAlreadyClosed :
  Cut.genericContradictionAlgebraRemaining
    Cut.canonicalPoleQuotientCurrentCut ≡ false
genericContradictionAlgebraAlreadyClosed = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record RiemannExperimentalProofSearchBoundary : Set where
  constructor riemann-experimental-proof-search-boundary
  field
    clusterMarginSearchShouldRemainQueuedAsOpen : Bool
    clusterMarginSearchShouldRemainQueuedAsOpenIsFalse :
      clusterMarginSearchShouldRemainQueuedAsOpen ≡ false

    gammaSearchFullyClosed : Bool
    gammaSearchFullyClosedIsFalse : gammaSearchFullyClosed ≡ false

    offOrdinateSearchRemainsPrimaryOpenAnalyticLeaf : Bool
    offOrdinateSearchRemainsPrimaryOpenAnalyticLeafIsTrue :
      offOrdinateSearchRemainsPrimaryOpenAnalyticLeaf ≡ true

    deterministicGammaAutomaticallyCheapest : Bool
    deterministicGammaAutomaticallyCheapestIsFalse :
      deterministicGammaAutomaticallyCheapest ≡ false

    hardyNamedDonorAutomaticallyPaysRHSocket : Bool
    hardyNamedDonorAutomaticallyPaysRHSocketIsFalse :
      hardyNamedDonorAutomaticallyPaysRHSocket ≡ false

    donorAuditRequiresLiteralCarrierBridge : Bool
    donorAuditRequiresLiteralCarrierBridgeIsTrue :
      donorAuditRequiresLiteralCarrierBridge ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRiemannExperimentalProofSearchBoundary :
  RiemannExperimentalProofSearchBoundary
canonicalRiemannExperimentalProofSearchBoundary =
  riemann-experimental-proof-search-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
