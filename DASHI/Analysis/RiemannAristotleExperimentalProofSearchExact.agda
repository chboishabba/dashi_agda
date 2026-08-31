module DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Cut
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice

------------------------------------------------------------------------
-- RH POLE-QUOTIENT CUT AS EXPERIMENT-DESIGNED PROOF SEARCH
--
-- The current high-ordinate cut has exactly three analytic producer sockets:
--
--   H_off^pole      signed off-ordinate reflection/cosine evaluation
--   H_Gamma         deterministic Gamma residual payment
--   M_cluster^pole  quantitative target-cluster lower margin
--
-- This module turns those sockets into explicit research moves.  It does not
-- assign mathematical difficulty or success probability.  A cost-aware policy
-- is available only after an application supplies a declared cost surface.
------------------------------------------------------------------------

data RHResearchSocket : Set where
  offOrdinateSocket gammaSocket clusterMarginSocket : RHResearchSocket

data RHResearchMove : Set where
  attackOffOrdinateCancellation
  payGammaResidual
  instantiateClusterMargin
  auditExternalAnalyticDonor
  : RHResearchMove

MovePays : RHResearchMove → RHResearchSocket → Set
MovePays attackOffOrdinateCancellation offOrdinateSocket = ⊤
MovePays payGammaResidual gammaSocket = ⊤
MovePays instantiateClusterMargin clusterMarginSocket = ⊤
MovePays _ _ = ⊥

------------------------------------------------------------------------
-- External-donor audit is a search move, not a payment.  In particular, merely
-- finding a theorem labelled Hardy / Hardy-Ramanujan / Hardy-Littlewood does
-- not discharge any RH socket until a literal carrier/interface bridge is
-- proved.
------------------------------------------------------------------------

record AnalyticDonorAudit : Set where
  constructor analytic-donor-audit
  field
    donorName : String
    donorReference : String
    TargetSocket : RHResearchSocket
    literalCarrierBridge : Set
    bridgeReference : String

open AnalyticDonorAudit public

------------------------------------------------------------------------
-- Costed search policy.  Costs are supplied, not inferred.
------------------------------------------------------------------------

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
-- Exact sync to the current cut.
------------------------------------------------------------------------

poleOffSocketStillOpen :
  Cut.poleQuotientSignedOffOrdinateBoundClosed
    Cut.canonicalPoleQuotientCurrentCut ≡ false
poleOffSocketStillOpen = refl

gammaSocketStillOpen :
  Cut.gammaResidualBudgetClosed Cut.canonicalPoleQuotientCurrentCut ≡ false
gammaSocketStillOpen = refl

clusterMarginSocketStillOpen :
  Cut.quantitativePoleQuotientClusterMarginClosed
    Cut.canonicalPoleQuotientCurrentCut ≡ false
clusterMarginSocketStillOpen = refl

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
    threeLivePoleQuotientSocketsExposed : Bool
    threeLivePoleQuotientSocketsExposedIsTrue :
      threeLivePoleQuotientSocketsExposed ≡ true

    deterministicGammaAutomaticallyCheapest : Bool
    deterministicGammaAutomaticallyCheapestIsFalse :
      deterministicGammaAutomaticallyCheapest ≡ false

    hardyNamedDonorAutomaticallyPaysRHSocket : Bool
    hardyNamedDonorAutomaticallyPaysRHSocketIsFalse :
      hardyNamedDonorAutomaticallyPaysRHSocket ≡ false

    donorAuditRequiresLiteralCarrierBridge : Bool
    donorAuditRequiresLiteralCarrierBridgeIsTrue :
      donorAuditRequiresLiteralCarrierBridge ≡ true

    genericContradictionAlgebraNeedsMoreSearch : Bool
    genericContradictionAlgebraNeedsMoreSearchIsFalse :
      genericContradictionAlgebraNeedsMoreSearch ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRiemannExperimentalProofSearchBoundary :
  RiemannExperimentalProofSearchBoundary
canonicalRiemannExperimentalProofSearchBoundary =
  riemann-experimental-proof-search-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
