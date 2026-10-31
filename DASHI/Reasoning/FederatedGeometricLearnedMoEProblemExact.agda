{-# OPTIONS --safe #-}
module DASHI.Reasoning.FederatedGeometricLearnedMoEProblemExact where

-- FULL PROBLEM INTERFACE, NOT A PROOF THAT AN EXISTING LEARNED
-- NETWORK, CRYPTOGRAPHIC CODEC, OR LEETCH ACTION SATISFIES IT.
-- Reuse existing ownership without equating finite numerology to
-- trained tensor semantics or opposing arguments to an antipode.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact as Orbits
import DASHI.Foundations.TernaryHypervoxelPermutationTransportExact as Hyper
import DASHI.Core.ConsumerQuotientBaseChangeExact as Consumer
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Argument
import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as Sign
import DASHI.Reasoning.LeechWeightedHistoryMoEBidiExact as Finite
import DASHI.Reasoning.IEEEOrbitSignWitnessBidiExact as IEEE
import DASHI.Reasoning.FederatedExpertTransportBidiExact as Wire

-- Exact orbit owner: arithmetic 3=1+2, 9=1+4*2, 27=1+13*2.
-- These counts are NOT a proof that network experts form Leech orbits.
orbit3Receipt : 3 ≡ 1 + 1 * 2
orbit3Receipt = Orbits.threeDecomposesAsCentrePlusOnePair

-- Explicit owner reuse: do not duplicate the concrete finite codecs.
finiteCodecRoundtrip :
  (word : IEEE.EncodedWord) →
  IEEE.decode (IEEE.encode word) ≡ word
finiteCodecRoundtrip = IEEE.decoderEncoderRoundtrip

-- Semantic argument response type is imported, NOT identified with
-- either the geometric carrier or its inverse.
SemanticResponse : Set
SemanticResponse = Argument.ResponseKind

record FederatedMoEProblem : Set₁ where
  field
    Input : Set
    History : Set
    ExpertId : Set
    ExpertWeights : Set
    ExpertOutput : Set
    ModelOutput : Set
    Route : Set
    GeometricAction : Set
    SemanticAction : Set
    EncodedPacket : Set
    ConsumerObservation : Set
    Peer : Set
    SchedulerDecision : Set
    Cost : Set
    TrainingState : Set
    TrainingExample : Set
    AuthenticationReceipt : Set
    HistoryRevision : Set

    -- Learned functions are indexed by distinct expert identities.
    -- The training rule is independently supplied, never inferred
    -- merely from having a family of functions.
    expert : ExpertId → Input → History → ExpertOutput
    update : ExpertId → Input → History → History
    router : Input → History → Route
    weights : Input → History → Route → ExpertWeights
    learn : TrainingState → TrainingExample → TrainingState
    parametersAt : TrainingState → ExpertId → Input → History →
                   ExpertOutput
    routeUnderAction : GeometricAction → Route → Route
    weightsUnderAction : GeometricAction → ExpertWeights →
                         ExpertWeights
    aggregate : Route → ExpertWeights →
                (ExpertId → ExpertOutput) → ModelOutput
    compute : Input → History → ModelOutput
    computeAgreesWithMixture :
      (x : Input) (h : History) →
      compute x h ≡ aggregate (router x h)
          (weights x h (router x h))
          (λ e → expert e x h)

    -- Each operation on a *joint activation/history* must be specified.
    invertInput : Input → Input
    invertHistory : History → History
    invertOutput : ModelOutput → ModelOutput
    involutionInput : (x : Input) →
      invertInput (invertInput x) ≡ x
    involutionHistory : (h : History) →
      invertHistory (invertHistory h) ≡ h
    involutionOutput : (y : ModelOutput) →
      invertOutput (invertOutput y) ≡ y

    -- Semantic action is NOT the geometric involution; any relation
    -- between them is a learned/fitted and tested structure.
    actSemantic : SemanticAction → Input → Input
    actGeometric : GeometricAction → Input → Input
    actionOnOutput : GeometricAction → ModelOutput → ModelOutput
    actionOnHistory : GeometricAction → History → History
    fittedSemanticAction : SemanticAction → GeometricAction
    actionFitEvidence : SemanticAction → Input → History → Set
    fittedActionMatches :
      (s : SemanticAction) (x : Input) (h : History) →
      actionFitEvidence s x h →
      actGeometric (fittedSemanticAction s) x ≡ actSemantic s x

    -- A positive action-commuting receipt is conditional on the actual
    -- route, weights, selected computations and history update.
    RoutingCompatible : GeometricAction → Input → History → Set
    routeCompatible :
      (a : GeometricAction) (x : Input) (h : History) →
      RoutingCompatible a x h →
      router (actGeometric a x) (actionOnHistory a h)
        ≡ routeUnderAction a (router x h)
    weightCompatible :
      (a : GeometricAction) (x : Input) (h : History) →
      RoutingCompatible a x h →
      weights (actGeometric a x) (actionOnHistory a h)
        (router (actGeometric a x) (actionOnHistory a h))
        ≡ weightsUnderAction a (weights x h (router x h))

    -- The full model may NOT commute. A residual/corrective operation
    -- is therefore explicit and consumer-relative.
    correction : GeometricAction → Input → History → ModelOutput
    correctedOutput : GeometricAction → Input → History → ModelOutput
    correctedOutputSound :
      (a : GeometricAction) (x : Input) (h : History) →
      correctedOutput a x h ≡ compute (actGeometric a x)
                                         (actionOnHistory a h)

    -- Independent exact observation of the downstream consumer.
    observe : ModelOutput → ConsumerObservation
    projected : Input → History → ConsumerObservation
    consumerFactorisation :
      (x : Input) (h : History) →
      projected x h ≡ observe (compute x h)
    observeAction : GeometricAction →
                    ConsumerObservation → ConsumerObservation
    modelActionSound : GeometricAction → Input → History → Set
    observeActionCompatible :
      (a : GeometricAction) (x : Input) (h : History) →
      modelActionSound a x h →
      observe (compute (actGeometric a x) (actionOnHistory a h))
        ≡ observeAction a (observe (compute x h))

    -- Encoding and decoding are about a complete transportable
    -- state sufficient for the consumer, not just a sign byte.
    packet : Input → History → EncodedPacket
    receive : EncodedPacket → Input
    receiveHistory : EncodedPacket → History
    exactReopenInput :
      (x : Input) (h : History) → receive (packet x h) ≡ x
    exactReopenHistory :
      (x : Input) (h : History) → receiveHistory (packet x h) ≡ h

    -- Distribution requires explicit execution placement and cost
    -- models; no ratio alone proves faster WAN inference.
    schedule : Peer → Input → History → SchedulerDecision
    networkCost : Peer → SchedulerDecision → EncodedPacket → Cost
    localCost : Input → History → Cost

    -- A history update is not averaged with expert outputs.
    stepHistory : Input → History → History
    stepHistoryCompatible :
      (a : GeometricAction) (x : Input) (h : History) →
      RoutingCompatible a x h →
      stepHistory (actGeometric a x) (actionOnHistory a h)
        ≡ actionOnHistory a (stepHistory x h)

    -- Authentication is not inferred from hashing or compression.
    historyVersion : History → HistoryRevision
    authenticate : Peer → EncodedPacket → AuthenticationReceipt
    Authenticated : Peer → EncodedPacket → AuthenticationReceipt → Set
    ValidSession : Peer → EncodedPacket → Set
    admissibleReceipt :
      (peer : Peer) (x : Input) (h : History) →
      Authenticated peer (packet x h)
        (authenticate peer (packet x h)) →
      ValidSession peer (packet x h) →
      receiveHistory (packet x h) ≡ h

open FederatedMoEProblem public

-- Under the specified packet roundtrip receipts, the consumer sees
-- the identical model result after a complete transport and reopen.
-- This is a *conditional theorem*, not proof of the real packet format.
consumerAfterWire :
  (P : FederatedMoEProblem) (x : Input P) (h : History P) →
  observe P (compute P (receive P (packet P x h))
                       (receiveHistory P (packet P x h)))
    ≡ observe P (compute P x h)
consumerAfterWire P x h
  rewrite exactReopenInput P x h | exactReopenHistory P x h = refl

-- Consumer-relative transport is a weaker criterion than exact wire
-- reopening, but it requires its own proof. The finite numbers and
-- opposite-argument witnesses never discharge that criterion by count.

-- Under a *separate* action-admissibility receipt, the transformed
-- computation has the agreed consumer observation. A sign flip or
-- semantic objection alone does not construct the receipt.
consumerAfterAdmittedAction :
  (P : FederatedMoEProblem)
  (a : GeometricAction P) (x : Input P) (h : History P) →
  modelActionSound P a x h →
  observe P (compute P (actGeometric P a x)
                      (actionOnHistory P a h))
    ≡ observeAction P a (observe P (compute P x h))
consumerAfterAdmittedAction P a x h witness =
  observeActionCompatible P a x h witness
