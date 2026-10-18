module DASHI.Analysis.RiemannG2FinalNearObserverDescentExact where

------------------------------------------------------------------------
-- LITERAL RH R1 AS SAME-OBJECT FOLD GLUING + CONSUMER DESCENT
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The current direct RH route does not require a whole concrete realization of
-- the universal pole-quotient scalar.  The canonical concrete-certificate seam
-- already isolates the least-privilege representation theorem:
--
--   final nearResponseAt(J)
--      = embed(certified concrete finite fold).
--
-- This owner makes that equality a SameObjectChartGluing and then asks the
-- consumer-relative question directly.  For the actual Off budget
--
--   near + far,
--
-- the embedded fold is sufficient once the same-object witness is present.
-- Thus R1 is an exact fold-level representation/descent obligation; no stronger
-- global identification is required by this consumer.
--
-- The bridge is still an input.  This module does not fabricate its embedded
-- fold equality and does not prove the independent strict ClusterResponse
-- inequality.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Unit using (⊤; tt)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Foundations.HyperformChartGluingExact as Glue

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as Concrete

------------------------------------------------------------------------
-- 1. The existing concrete certificate bridge is literally a two-chart weld.
------------------------------------------------------------------------

finalNearEmbeddedFoldGluing :
  ∀ {S transport offInput carrier certificate} →
  Concrete.ConcreteCertificateFinalScalarBridge
    {S = S} {transport = transport}
    offInput carrier certificate →
  Glue.SameObjectChartGluing
    ⊤
    (NearFar.Scalar S)
    _≡_
finalNearEmbeddedFoldGluing
    {S} {transport} {offInput} {carrier} {certificate} bridge = record
  { Glue.chartA = λ _ →
      Transport.nearResponseAt transport
        (Direct.chosenCutoff offInput)
  ; Glue.chartB = λ _ →
      Concrete.embed bridge
        (Cert.foldScalars carrier
          (Cert.mapValues
            (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
            (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))
  ; Glue.glueOnOverlap = λ _ →
      Concrete.finalNearIsEmbeddedCertifiedFold bridge
  }

------------------------------------------------------------------------
-- 2. Generic state carrying actual near, observed fold, and exact weld.
------------------------------------------------------------------------

record FinalNearFoldState
    (S : NearFar.OrderedAdditiveNearFarSurface) : Set where
  constructor final-near-fold-state
  field
    actualNear : NearFar.Scalar S
    observedFold : NearFar.Scalar S
    actualNearIsObservedFold : actualNear ≡ observedFold

open FinalNearFoldState public

finalNearFoldObserver :
  (S : NearFar.OrderedAdditiveNearFarSurface) →
  Glue.ObserverWithFibre
    (FinalNearFoldState S)
    (NearFar.Scalar S)
finalNearFoldObserver S = record
  { Glue.observe = observedFold
  }

finalNearPlusFarConsumer :
  (S : NearFar.OrderedAdditiveNearFarSurface) →
  NearFar.Scalar S →
  FinalNearFoldState S →
  NearFar.Scalar S
finalNearPlusFarConsumer S far state =
  NearFar.add S (actualNear state) far

finalNearPlusFarFactorsThroughObservedFold :
  (S : NearFar.OrderedAdditiveNearFarSurface) →
  (far : NearFar.Scalar S) →
  Descent.FactorsThrough
    (Glue.observe (finalNearFoldObserver S))
    (finalNearPlusFarConsumer S far)
finalNearPlusFarFactorsThroughObservedFold S far =
  Factorized.factorizedRefinement
    (λ observed → NearFar.add S observed far)
    (λ state →
      cong
        (λ near → NearFar.add S near far)
        (actualNearIsObservedFold state))

------------------------------------------------------------------------
-- 3. Instantiate the generic state from the existing concrete bridge.
------------------------------------------------------------------------

stateFromConcreteCertificateBridge :
  ∀ {S transport offInput carrier certificate} →
  (bridge : Concrete.ConcreteCertificateFinalScalarBridge
    {S = S} {transport = transport}
    offInput carrier certificate) →
  FinalNearFoldState S
stateFromConcreteCertificateBridge
    {S} {transport} {offInput} {carrier} {certificate} bridge =
  final-near-fold-state
    (Transport.nearResponseAt transport
      (Direct.chosenCutoff offInput))
    (Concrete.embed bridge
      (Cert.foldScalars carrier
        (Cert.mapValues
          (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
          (Cert.ProofCarryingFiniteSumEnclosure.terms certificate))))
    (Concrete.finalNearIsEmbeddedCertifiedFold bridge)

observedStateIsEmbeddedCertifiedFold :
  ∀ {S transport offInput carrier certificate}
    (bridge : Concrete.ConcreteCertificateFinalScalarBridge
      {S = S} {transport = transport}
      offInput carrier certificate) →
  Glue.observe
    (finalNearFoldObserver S)
    (stateFromConcreteCertificateBridge bridge)
  ≡
  Concrete.embed bridge
    (Cert.foldScalars carrier
      (Cert.mapValues
        (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
        (Cert.ProofCarryingFiniteSumEnclosure.terms certificate))
observedStateIsEmbeddedCertifiedFold bridge = refl

consumerAtBridgeIsLiteralDirectOffBudget :
  ∀ {S transport offInput carrier certificate}
    (bridge : Concrete.ConcreteCertificateFinalScalarBridge
      {S = S} {transport = transport}
      offInput carrier certificate) →
  finalNearPlusFarConsumer S
    (Transport.farBudgetAt transport
      (Direct.chosenCutoff offInput))
    (stateFromConcreteCertificateBridge bridge)
  ≡
  Direct.directOffBudget offInput
    (Transport.universalPoleQuotientTaper transport)
consumerAtBridgeIsLiteralDirectOffBudget bridge = refl

------------------------------------------------------------------------
-- 4. Authority / frontier boundary.
------------------------------------------------------------------------

record FinalNearObserverDescentBoundary : Set where
  constructor final-near-observer-descent-boundary
  field
    concreteCertificateMayUseDistinctScalarCarrier : Bool
    embeddedFoldEqualityIsSameObjectChartWitness : Bool
    directOffBudgetFactorsThroughEmbeddedNearFold : Bool
    wholePoleQuotientScalarRealizationRequiredForOffBudgetConsumer : Bool
    sameObjectWitnessStillRequired : Bool
    strictClusterResponseMarginPaidHere : Bool
    rhDerived : Bool

open FinalNearObserverDescentBoundary public

canonicalFinalNearObserverDescentBoundary :
  FinalNearObserverDescentBoundary
canonicalFinalNearObserverDescentBoundary =
  final-near-observer-descent-boundary
    true true true false true false false
