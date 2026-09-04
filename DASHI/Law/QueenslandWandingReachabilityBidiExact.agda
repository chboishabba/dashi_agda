module DASHI.Law.QueenslandWandingReachabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition

------------------------------------------------------------------------
-- Wanding is represented as a situated transition system.  Direct doctrinal
-- authority and operational reachability are distinct coordinates.
------------------------------------------------------------------------

data EncounterPhase : Set where
  publicPresence compelledContact wandRequirement scannerResponse
  downstreamPredicate personalSearch arrestOrRelease : EncounterPhase

data Move : Set where
  compelStop requireWand observeResponse createDownstreamPredicate
  conductSearch concludeEncounter : Move

record EncounterFibre : Set where
  constructor encounterFibre
  field
    phase : EncounterPhase
    wandAuthority : Bool
    directSearchAuthorityFromWand : Bool
    separateSearchPredicate : Bool
    personSearchReachable : Bool
    scannerAlarm : Bool
    nonCompliance : Bool
    bodyCamPresent : Bool
    bodyCamActivated : Bool
    physicalTracePresent : Bool
    independentWitness : Bool
    sourceReference : String

open EncounterFibre public

wandFirewall : EncounterFibre → Set
wandFirewall e = directSearchAuthorityFromWand e ≡ false

indirectSearchReachability : EncounterFibre → Set
indirectSearchReachability e = personSearchReachable e ≡ true

record FirewallWithReachability (e : EncounterFibre) : Set where
  constructor firewallWithReachability
  field
    noDirectConferral : wandFirewall e
    searchStillReachable : indirectSearchReachability e

open FirewallWithReachability public

firewallDoesNotBlockReachability :
  (e : EncounterFibre) →
  FirewallWithReachability e →
  indirectSearchReachability e
firewallDoesNotBlockReachability e receipt = searchStillReachable receipt

------------------------------------------------------------------------
-- A later predicate cannot be silently substituted for the producer of the
-- earlier wand authority.  The history is retained as a fibre coordinate.
------------------------------------------------------------------------

record AuthorityProvenance : Set where
  constructor authorityProvenance
  field
    initialWandAuthority : Bool
    laterSearchPredicate : Bool
    laterPredicateIsInitialAuthority : Bool
    laterPredicateIsInitialAuthorityIsFalse :
      laterPredicateIsInitialAuthority ≡ false
    provenanceReference : String

open AuthorityProvenance public

------------------------------------------------------------------------
-- Aggregate reporting is a projection.  It does not reconstruct encounter
-- provenance, selection basis, or the intermediate transition path.
------------------------------------------------------------------------

record AggregateProjection : Set where
  constructor aggregateProjection
  field
    wandCount weaponCount chargeCount : ℕ
    reportsSelectionBasis : Bool
    reportsAlarmToSearchCrossTab : Bool
    reportsNonWeaponChargeCrossTab : Bool
    projectionReference : String

open AggregateProjection public

record AggregateBoundary (a : AggregateProjection) : Set where
  constructor aggregateBoundary
  field
    selectionBasisErased : reportsSelectionBasis a ≡ false
    alarmSearchCrossTabErased : reportsAlarmToSearchCrossTab a ≡ false
    nonWeaponChargeCrossTabErased : reportsNonWeaponChargeCrossTab a ≡ false

------------------------------------------------------------------------
-- BIDI: downstream consumers route backwards to exact producer obligations.
------------------------------------------------------------------------

data ConsumerClaim : Set where
  lawfulInitialWand lawfulDownstreamSearch gatewayRate selectionDisparity
  deterrenceEffect forceHistoryReconstruction : ConsumerClaim

data ProducerObligation : Set where
  wandAuthorityReceipt searchPredicateReceipt transitionCrossTab
  eligiblePopulationDenominator counterfactualControl
  physicalTraceReceipt recordingReceipt telemetryReceipt witnessReceipt : ProducerObligation

reverseRoute : ConsumerClaim → ProducerObligation
reverseRoute lawfulInitialWand = wandAuthorityReceipt
reverseRoute lawfulDownstreamSearch = searchPredicateReceipt
reverseRoute gatewayRate = transitionCrossTab
reverseRoute selectionDisparity = eligiblePopulationDenominator
reverseRoute deterrenceEffect = counterfactualControl
reverseRoute forceHistoryReconstruction = recordingReceipt

record BidiPromotionGate : Set where
  constructor bidiPromotionGate
  field
    requestedClaim : ConsumerClaim
    suppliedProducer : ProducerObligation
    exactProducerMatch : suppliedProducer ≡ reverseRoute requestedClaim
    consumerReference : String

open BidiPromotionGate public

promotionUsesExactProducer :
  (gate : BidiPromotionGate) →
  suppliedProducer gate ≡ reverseRoute (requestedClaim gate)
promotionUsesExactProducer = exactProducerMatch

------------------------------------------------------------------------
-- Repo-native transition x-pollination: enablement precedes transition.
------------------------------------------------------------------------

record WandingTransitionAdapter : Set₁ where
  constructor wandingTransitionAdapter
  field
    system : Transition.AdmissibleTransitionSystem
    contactMove searchMove : Transition.Move system
    parameter : Transition.Parameter system
    before after : Transition.State system
    contactChangesCone :
      Transition.EnablesMove system (λ _ → after) searchMove parameter before
    adapterReference : String

open WandingTransitionAdapter public

contactCanOpenPreviouslyClosedSearchEdge :
  (adapter : WandingTransitionAdapter) →
  Transition.Enabled (system adapter) (searchMove adapter)
    (parameter adapter) (after adapter)
contactCanOpenPreviouslyClosedSearchEdge adapter =
  Transition.enabledAfter (contactChangesCone adapter)

------------------------------------------------------------------------
-- Firewall constants corresponding to the current statutory architecture.
-- The source string is provenance only; legal conclusions remain typed above.
------------------------------------------------------------------------

queenslandSection39KReference : String
queenslandSection39KReference =
  "Queensland Police Powers and Responsibilities Act 2000, ss 29, 30(1)(l), 39K"

canonicalFirewallBoundary : EncounterFibre
canonicalFirewallBoundary =
  encounterFibre compelledContact true false true true false true false false false false
    queenslandSection39KReference

canonicalFirewallReachability : FirewallWithReachability canonicalFirewallBoundary
canonicalFirewallReachability = firewallWithReachability refl refl
