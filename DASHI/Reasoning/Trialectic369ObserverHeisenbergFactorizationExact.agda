module DASHI.Reasoning.Trialectic369ObserverHeisenbergFactorizationExact where

------------------------------------------------------------------------
-- TRIALECTIC OBSERVER MATRIX <-> INTERACTION T3 x APPRAISAL X6
--
-- DASHI CONTRIBUTION
--
-- Existing exact charts already provide:
--
--   ObserverMatrix3 SSPTrit <-> TernaryHyperformalPoint
--   TernaryHyperformalPoint <-> Ternary27Point x X6
--
-- composing them yields the literal factorisation
--
--   ObserverMatrix3 SSPTrit <-> rowA(T^3) x X6(rows B,C).
--
-- This is an exact carrier rechart only.  It does not identify observer roles
-- with Monster representation semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Bridge

------------------------------------------------------------------------
-- 1. Factorized trialectic carrier.
------------------------------------------------------------------------

record TrialecticInteractionHeisenbergPoint : Set where
  constructor trialectic-interaction-heisenberg-point
  field
    interactionRow : Fabric.Ternary27Point
    appraisalRowsX6 : H.X6

open TrialecticInteractionHeisenbergPoint public

observerToInteractionHeisenberg :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  TrialecticInteractionHeisenbergPoint
observerToInteractionHeisenberg matrix =
  trialectic-interaction-heisenberg-point
    (Bridge.observerRowA matrix)
    (Carrier.appraisalFibreToX6
      (Fabric.appraisalFibrePoint
        (Bridge.observerRowB matrix)
        (Bridge.observerRowC matrix)))

interactionHeisenbergToObserver :
  TrialecticInteractionHeisenbergPoint ->
  Observer.ObserverMatrix3 SSP.SSPTrit
interactionHeisenbergToObserver
  (trialectic-interaction-heisenberg-point interaction fibre) =
  Bridge.fabricToObserver
    (Fabric.rebuildOverInteraction
      interaction
      (Carrier.x6ToAppraisalFibre fibre))

------------------------------------------------------------------------
-- 2. Exact two-sided recovery.
------------------------------------------------------------------------

observerInteractionHeisenbergRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  interactionHeisenbergToObserver
    (observerToInteractionHeisenberg matrix)
  ≡ matrix
observerInteractionHeisenbergRoundTrip matrix =
  trans
    (cong
      Bridge.fabricToObserver
      (cong
        (Fabric.rebuildOverInteraction (Bridge.observerRowA matrix))
        (Carrier.appraisalFibreRoundTrip
          (Fabric.appraisalFibrePoint
            (Bridge.observerRowB matrix)
            (Bridge.observerRowC matrix)))))
    (Bridge.observerFabricRoundTrip matrix)

interactionHeisenbergObserverRoundTrip :
  (state : TrialecticInteractionHeisenbergPoint) ->
  observerToInteractionHeisenberg
    (interactionHeisenbergToObserver state)
  ≡ state
interactionHeisenbergObserverRoundTrip
    (trialectic-interaction-heisenberg-point interaction fibre)
  rewrite Bridge.fabricObserverRoundTrip
            (Fabric.rebuildOverInteraction
              interaction
              (Carrier.x6ToAppraisalFibre fibre))
        | Carrier.x6RoundTrip fibre = refl

------------------------------------------------------------------------
-- 3. Commutation with the existing hyperfabric factorisation.
------------------------------------------------------------------------

observerToFabricFactorizationCommutes :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Carrier.fabricToInteractionHeisenberg
    (Bridge.observerToFabric matrix)
  ≡
  Carrier.interactionHeisenbergPoint
    (interactionRow (observerToInteractionHeisenberg matrix))
    (appraisalRowsX6 (observerToInteractionHeisenberg matrix))
observerToFabricFactorizationCommutes matrix = refl

interactionRowIsObserverRowA :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  interactionRow (observerToInteractionHeisenberg matrix)
  ≡ Bridge.observerRowA matrix
interactionRowIsObserverRowA matrix = refl

appraisalRowsDecodeToObserverRowsBC :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Carrier.x6ToAppraisalFibre
    (appraisalRowsX6 (observerToInteractionHeisenberg matrix))
  ≡
  Fabric.appraisalFibrePoint
    (Bridge.observerRowB matrix)
    (Bridge.observerRowC matrix)
appraisalRowsDecodeToObserverRowsBC matrix =
  Carrier.appraisalFibreRoundTrip
    (Fabric.appraisalFibrePoint
      (Bridge.observerRowB matrix)
      (Bridge.observerRowC matrix))

------------------------------------------------------------------------
-- 4. Semantic firewall.
------------------------------------------------------------------------

data TrialecticRowsBecomeMonsterRepresentation : Set where
data InteractionRowIsIntrinsicPsychologicalBase : Set where
data AppraisalX6FactorizationCreatesMonsterAction : Set where

trialecticRowsDoNotBecomeMonsterRepresentation :
  TrialecticRowsBecomeMonsterRepresentation -> ⊥
trialecticRowsDoNotBecomeMonsterRepresentation ()

interactionRowNotPromotedToIntrinsicPsychologicalBase :
  InteractionRowIsIntrinsicPsychologicalBase -> ⊥
interactionRowNotPromotedToIntrinsicPsychologicalBase ()

appraisalX6FactorizationDoesNotCreateMonsterAction :
  AppraisalX6FactorizationCreatesMonsterAction -> ⊥
appraisalX6FactorizationDoesNotCreateMonsterAction ()

record Trialectic369ObserverHeisenbergFactorizationBoundary : Set where
  constructor trialectic-369-observer-heisenberg-factorization-boundary
  field
    observerToInteractionX6Constructed : Bool
    exactTwoSidedRoundTrip : Bool
    rowAIsInteractionCoordinate : Bool
    rowsBCFormExactX6Coordinate : Bool
    commutesWithHyperformalFactorization : Bool
    semanticMonsterIdentityClaimed : Bool
    psychologicalBaseRoleClaimedIntrinsic : Bool
    monsterActionObtainedFromCarrierFactorization : Bool

canonicalTrialectic369ObserverHeisenbergFactorizationBoundary :
  Trialectic369ObserverHeisenbergFactorizationBoundary
canonicalTrialectic369ObserverHeisenbergFactorizationBoundary =
  trialectic-369-observer-heisenberg-factorization-boundary
    true true true true true
    false false false
