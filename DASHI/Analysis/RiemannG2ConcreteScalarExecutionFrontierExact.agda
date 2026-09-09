module DASHI.Analysis.RiemannG2ConcreteScalarExecutionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as LegacyDirect
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as Reconcile

------------------------------------------------------------------------
-- CONCRETE-SCALAR EXECUTION FRONTIER
--
-- The theorem-bearing finite certificate API is generic in the final
-- NearFar.Scalar.  A runtime cannot emit a meaningful numerical certificate for
-- that carrier until a concrete exact/enclosure scalar is identified with it.
--
-- Keep this strictly below the RH mathematics.  A concrete implementation may
-- choose rationals, exact algebraic values, interval endpoints, or another
-- certifiable carrier; this module does not prescribe which one.  It requires
-- only the same-object/value/order structure consumed by the final certificate
-- route.
------------------------------------------------------------------------

record ConcreteFinalNearScalarRealization
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    ConcreteScalar : Set
    concreteZero : ConcreteScalar
    concreteAdd : ConcreteScalar -> ConcreteScalar -> ConcreteScalar
    embedConcrete : ConcreteScalar -> NearFar.Scalar S

    concreteOrder : ConcreteScalar -> ConcreteScalar -> Set

    embedZero : embedConcrete concreteZero ≡ concreteZeroMapped
      where
      concreteZeroMapped : NearFar.Scalar S
      concreteZeroMapped = embedConcrete concreteZero

    embedAdd :
      (x y : ConcreteScalar) ->
      embedConcrete (concreteAdd x y)
      ≡ NearFar.add S (embedConcrete x) (embedConcrete y)

    orderSound :
      {x y : ConcreteScalar} ->
      concreteOrder x y ->
      NearFar._≤_ S (embedConcrete x) (embedConcrete y)

    realizationReference : String

open ConcreteFinalNearScalarRealization public

------------------------------------------------------------------------
-- The historical rational/direct finite lane is not an R0 payment.
--
-- It may contain rational helper cells, but its substantive producer is indexed
-- by the older LiteralTargetCenteredScalarProblem and requires the stronger
-- DirectSignedConsumerPayment.  The repository explicitly classifies the
-- determinant/direct lane as diagnostic relative to the final universal
-- pole-quotient carrier, and no same-object bridge to final NearFar.Scalar is
-- recovered on current master.
------------------------------------------------------------------------

legacyDirectLaneIsFinalPoleCarrier :
  Reconcile.PoleQuotientFinalCutBoundary.determinantLaneIsFinalPoleQuotientCarrier
    Reconcile.canonicalPoleQuotientFinalCutBoundary ≡ false
legacyDirectLaneIsFinalPoleCarrier = refl

legacyDirectPaymentAutomaticallyPaysFinalOff :
  Reconcile.PoleQuotientFinalCutBoundary.determinantDirectPaymentAutomaticallyPaysFinalOffSocket
    Reconcile.canonicalPoleQuotientFinalCutBoundary ≡ false
legacyDirectPaymentAutomaticallyPaysFinalOff = refl

record ConcreteScalarExecutionFrontierBoundary : Set where
  constructor concrete-scalar-execution-frontier-boundary
  field
    finalNearFarScalarConcreteByDefinition : Bool
    finalNearFarScalarConcreteByDefinitionIsFalse :
      finalNearFarScalarConcreteByDefinition ≡ false

    executableCertificateNeedsConcreteScalarRealization : Bool
    executableCertificateNeedsConcreteScalarRealizationIsTrue :
      executableCertificateNeedsConcreteScalarRealization ≡ true

    concreteRealizationIsNewRHAnalyticTheorem : Bool
    concreteRealizationIsNewRHAnalyticTheoremIsFalse :
      concreteRealizationIsNewRHAnalyticTheorem ≡ false

    legacyRationalDirectLanePaysConcreteFinalScalar : Bool
    legacyRationalDirectLanePaysConcreteFinalScalarIsFalse :
      legacyRationalDirectLanePaysConcreteFinalScalar ≡ false

    toyWeilNatCarrierPaysConcreteFinalScalar : Bool
    toyWeilNatCarrierPaysConcreteFinalScalarIsFalse :
      toyWeilNatCarrierPaysConcreteFinalScalar ≡ false

    sameObjectEmbeddingAndOrderSoundnessRemainRequired : Bool
    sameObjectEmbeddingAndOrderSoundnessRemainRequiredIsTrue :
      sameObjectEmbeddingAndOrderSoundnessRemainRequired ≡ true

    r0RealizationInhabitedHere : Bool
    r0RealizationInhabitedHereIsFalse :
      r0RealizationInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalConcreteScalarExecutionFrontierBoundary :
  ConcreteScalarExecutionFrontierBoundary
canonicalConcreteScalarExecutionFrontierBoundary =
  concrete-scalar-execution-frontier-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "For actual proof-carrying numerical execution, first realize the final universal pole-quotient NearFar scalar by a concrete certifiable scalar with proof-relevant additive and order transport. This is execution/representation debt, not the RH analytic payment. The historical rational DirectFinitePoleNearProducer lane cannot be reused silently: its substantive endpoint is the older LiteralTargetCenteredScalarProblem/DirectSignedConsumerPayment and the repository explicitly denies automatic transport from the determinant/direct lane to the final pole-quotient consumer. A toy Nat Weil space is likewise not a final-carrier payment. After a genuine same-object scalar realization, R1 and the finite certificate machinery may be executed; RH is not derived here."
