module DASHI.Analysis.RiemannG2ConcreteScalarExecutionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as Reconcile
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as FoldBridge

record ConcreteFinalNearScalarRealization
    {S : NearFar.OrderedAdditiveNearFarSurface}
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    ConcreteScalar : Set
    concreteZero : ConcreteScalar
    concreteAdd : ConcreteScalar -> ConcreteScalar -> ConcreteScalar
    concreteOrder : ConcreteScalar -> ConcreteScalar -> Set
    embedConcrete : ConcreteScalar -> NearFar.Scalar S
    finalFoldZero : NearFar.Scalar S
    concreteZeroIsFinalFoldZero : embedConcrete concreteZero ≡ finalFoldZero
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

legacyDirectLaneIsFinalPoleCarrier :
  Reconcile.PoleQuotientFinalCutBoundary.determinantLaneIsFinalPoleQuotientCarrier
    Reconcile.canonicalPoleQuotientFinalCutBoundary ≡ false
legacyDirectLaneIsFinalPoleCarrier = refl

legacyDirectPaymentAutomaticallyPaysFinalOff :
  Reconcile.PoleQuotientFinalCutBoundary.determinantDirectPaymentAutomaticallyPaysFinalOffSocket
    Reconcile.canonicalPoleQuotientFinalCutBoundary ≡ false
legacyDirectPaymentAutomaticallyPaysFinalOff = refl

foldLocalBridgeDoesNotRequireScalarEquality :
  FoldBridge.ConcreteCertificateFinalScalarBoundary.certificateScalarMustDefinitionallyEqualFinalAnalyticScalar
    FoldBridge.canonicalConcreteCertificateFinalScalarBoundary ≡ false
foldLocalBridgeDoesNotRequireScalarEquality = refl

foldLocalBridgeStillRequiresExactEmbeddedFold :
  FoldBridge.ConcreteCertificateFinalScalarBoundary.exactEmbeddedFoldIdentityStillRequired
    FoldBridge.canonicalConcreteCertificateFinalScalarBoundary ≡ true
foldLocalBridgeStillRequiresExactEmbeddedFold = refl

record ConcreteScalarExecutionFrontierBoundary : Set where
  constructor concrete-scalar-execution-frontier-boundary
  field
    finalNearFarScalarConcreteByDefinition : Bool
    finalNearFarScalarConcreteByDefinitionIsFalse : finalNearFarScalarConcreteByDefinition ≡ false
    executableCertificateNeedsWholeScalarRealization : Bool
    executableCertificateNeedsWholeScalarRealizationIsFalse : executableCertificateNeedsWholeScalarRealization ≡ false
    executableCertificateNeedsFoldLocalEmbedding : Bool
    executableCertificateNeedsFoldLocalEmbeddingIsTrue : executableCertificateNeedsFoldLocalEmbedding ≡ true
    certificateScalarMayRemainConcreteAndDistinct : Bool
    certificateScalarMayRemainConcreteAndDistinctIsTrue : certificateScalarMayRemainConcreteAndDistinct ≡ true
    fullConcreteScalarRealizationStillCompatible : Bool
    fullConcreteScalarRealizationStillCompatibleIsTrue : fullConcreteScalarRealizationStillCompatible ≡ true
    concreteRealizationIsNewRHAnalyticTheorem : Bool
    concreteRealizationIsNewRHAnalyticTheoremIsFalse : concreteRealizationIsNewRHAnalyticTheorem ≡ false
    legacyRationalDirectLanePaysConcreteFinalScalar : Bool
    legacyRationalDirectLanePaysConcreteFinalScalarIsFalse : legacyRationalDirectLanePaysConcreteFinalScalar ≡ false
    toyWeilNatCarrierPaysConcreteFinalScalar : Bool
    toyWeilNatCarrierPaysConcreteFinalScalarIsFalse : toyWeilNatCarrierPaysConcreteFinalScalar ≡ false
    exactEmbeddedFoldAndOrderTransportRemainRequired : Bool
    exactEmbeddedFoldAndOrderTransportRemainRequiredIsTrue : exactEmbeddedFoldAndOrderTransportRemainRequired ≡ true
    r0FoldLocalBridgeInhabitedHere : Bool
    r0FoldLocalBridgeInhabitedHereIsFalse : r0FoldLocalBridgeInhabitedHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalConcreteScalarExecutionFrontierBoundary : ConcreteScalarExecutionFrontierBoundary
canonicalConcreteScalarExecutionFrontierBoundary =
  concrete-scalar-execution-frontier-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "For proof-carrying numerical execution, do not require a whole concrete realization of the final universal pole-quotient NearFar scalar unless a producer naturally supplies one. The certified consumer only needs a concrete certificate carrier, one embedding of its certified fold into final nearResponseAt(J), and one transport of the certified upper relation. This permits exact rational/interval certification without asserting that rationals are definitionally the analytic real carrier or requiring the still-unowned Fast-Cauchy quotient backend. A full additive/order-preserving scalar realization remains a compatible stronger producer. The historical determinant/direct rational lane and toy Weil carriers still do not pay the final pole-quotient same-object seam. RH is not derived here."
