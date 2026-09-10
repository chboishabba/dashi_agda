{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact where

------------------------------------------------------------------------
-- MARKED LOG-PARTITION -> CONNECTED CORRELATION COMPILER
--
-- This owner intentionally does NOT prove exponential clustering.  It isolates
-- the representation identity needed by the Step-V / marked-polymer producer:
-- a mixed source derivative of log Z is the connected two-point response.
--
-- The source/analytic implementation of derivatives is deliberately abstract.
-- What this module prevents is charging the algebraic identification
--
--   d_A d_B log Z = <AB> - <A><B>
--
-- as a second physical theorem once a same-carrier source-response authority
-- has supplied it.  The remaining Level-2 content is the decay estimate for
-- that mixed derivative on the actual marked Step-V polymer carrier, followed
-- by the already-separated physical-scale and continuum same-family transports.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

record MarkedTwoSourceResponse
    (Observable Scalar : Set) : Set₁ where
  field
    multiply subtract : Scalar → Scalar → Scalar

    expectation : Observable → Scalar
    productExpectation : Observable → Observable → Scalar

    mixedLogPartitionDerivative : Observable → Observable → Scalar

    -- Same-carrier source-response identity.  This is the only calculus/source
    -- input of this compiler; it must not be manufactured from analyticity or
    -- a theorem name alone.
    mixedDerivativeMeaning : ∀ A B →
      mixedLogPartitionDerivative A B
      ≡ subtract
          (productExpectation A B)
          (multiply (expectation A) (expectation B))

open MarkedTwoSourceResponse public

connectedCorrelation :
  ∀ {Observable Scalar} →
  MarkedTwoSourceResponse Observable Scalar →
  Observable → Observable → Scalar
connectedCorrelation response A B =
  subtract response
    (productExpectation response A B)
    (multiply response
      (expectation response A)
      (expectation response B))

mixedLogPartitionDerivativeIsConnectedCorrelation :
  ∀ {Observable Scalar}
    (response : MarkedTwoSourceResponse Observable Scalar)
    (A B : Observable) →
  mixedLogPartitionDerivative response A B
  ≡ connectedCorrelation response A B
mixedLogPartitionDerivativeIsConnectedCorrelation response A B =
  mixedDerivativeMeaning response A B

record SeparationDecayProducer
    {Observable Scalar Bound Distance : Set}
    (response : MarkedTwoSourceResponse Observable Scalar) : Set₁ where
  field
    absoluteValue : Scalar → Bound
    LessEqual : Bound → Bound → Set
    distance : Observable → Observable → Distance
    decayEnvelope : Distance → Bound

    -- THIS is the theorem-bearing analytic field.  It is intentionally stated
    -- on the mixed source derivative, before compiling to the correlation
    -- presentation below.
    mixedDerivativeDecay : ∀ A B →
      LessEqual
        (absoluteValue (mixedLogPartitionDerivative response A B))
        (decayEnvelope (distance A B))

open SeparationDecayProducer public

connectedCorrelationDecayFromMarkedSource :
  ∀ {Observable Scalar Bound Distance}
    {response : MarkedTwoSourceResponse Observable Scalar}
    (producer : SeparationDecayProducer response)
    (A B : Observable) →
  LessEqual producer
    (absoluteValue producer (connectedCorrelation response A B))
    (decayEnvelope producer (distance producer A B))
connectedCorrelationDecayFromMarkedSource {response = response} producer A B
  rewrite
    (sym (mixedLogPartitionDerivativeIsConnectedCorrelation response A B)) =
  mixedDerivativeDecay producer A B

------------------------------------------------------------------------
-- Boundary / proof-search classification.
------------------------------------------------------------------------

mixedDerivativeConnectedCorrelationIdentityIsCompiler : Bool
mixedDerivativeConnectedCorrelationIdentityIsCompiler = true

markedAnalyticityAloneImpliesDecay : Bool
markedAnalyticityAloneImpliesDecay = false

singleMarkedMomentBoundAloneImpliesConnectedDecay : Bool
singleMarkedMomentBoundAloneImpliesConnectedDecay = false

mixedDerivativeSeparationDecayStillPhysical : Bool
mixedDerivativeSeparationDecayStillPhysical = true

continuumSameFamilyTransportStillSeparate : Bool
continuumSameFamilyTransportStillSeparate = true

clayPromotion : Bool
clayPromotion = false

mixedDerivativeConnectedCorrelationIdentityIsCompilerIsTrue :
  mixedDerivativeConnectedCorrelationIdentityIsCompiler ≡ true
mixedDerivativeConnectedCorrelationIdentityIsCompilerIsTrue = refl

markedAnalyticityAloneImpliesDecayIsFalse :
  markedAnalyticityAloneImpliesDecay ≡ false
markedAnalyticityAloneImpliesDecayIsFalse = refl

singleMarkedMomentBoundAloneImpliesConnectedDecayIsFalse :
  singleMarkedMomentBoundAloneImpliesConnectedDecay ≡ false
singleMarkedMomentBoundAloneImpliesConnectedDecayIsFalse = refl

mixedDerivativeSeparationDecayStillPhysicalIsTrue :
  mixedDerivativeSeparationDecayStillPhysical ≡ true
mixedDerivativeSeparationDecayStillPhysicalIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
