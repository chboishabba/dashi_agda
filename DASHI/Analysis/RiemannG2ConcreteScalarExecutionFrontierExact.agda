module DASHI.Analysis.RiemannG2ConcreteScalarExecutionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as Reconcile

------------------------------------------------------------------------
-- CONCRETE-SCALAR EXECUTION FRONTIER
--
-- The theorem-bearing finite certificate API is generic in the final
-- NearFar.Scalar. A runtime cannot emit a meaningful numerical certificate for
-- that carrier until a concrete exact/enclosure scalar is identified with it.
--
-- Keep this strictly below the RH mathematics. A concrete implementation may
-- choose rationals, exact algebraic values, interval endpoints, or another
-- certifiable carrier. We ask only for the additive/order transport actually
-- consumed by the finite-fold certificate path.
------------------------------------------------------------------------

record ConcreteFinalNearScalarRealization
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    ConcreteScalar : Set
    concreteZero : ConcreteScalar
    concreteAdd : ConcreteScalar -> ConcreteScalar -> ConcreteScalar
    concreteOrder : ConcreteScalar -> ConcreteScalar -> Set

    embedConcrete : ConcreteScalar -> NearFar.Scalar S

    -- The final certificate chooses its fold-zero explicitly; NearFar itself
    -- does not own a distinguished zero.
    finalFoldZero : NearFar.Scalar S
    concreteZeroIsFinalFoldZero :
      embedConcrete concreteZero ≡ finalFoldZero

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

    nearFarDistinguishedZeroRequired : Bool
    nearFarDistinguishedZeroRequiredIsFalse :
      nearFarDistinguishedZeroRequired ≡ false

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
    false refl
    true refl
    false refl
    false refl
    "For actual proof-carrying numerical execution, first realize the final universal pole-quotient NearFar scalar by a concrete certifiable scalar with proof-relevant additive and order transport. NearFar owns no distinguished zero, so the certificate's fold-zero is supplied locally rather than inflating the surface. This is execution/representation debt, not the RH analytic payment. The historical rational DirectFinitePoleNearProducer lane cannot be reused silently: its substantive endpoint is the older determinant/direct scalar problem and the repository explicitly denies automatic transport to the final pole-quotient consumer. A toy Nat Weil space is likewise not a final-carrier payment. After a genuine same-object scalar realization, R1 and the finite certificate machinery may be executed; RH is not derived here."
