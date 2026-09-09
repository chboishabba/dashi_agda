module DASHI.Analysis.RiemannG2ConcreteScalarExecutionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as Reconcile
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as FoldBridge

------------------------------------------------------------------------
-- CONCRETE-SCALAR EXECUTION FRONTIER
--
-- A full concrete realization of the final NearFar scalar is a useful stronger
-- producer, but it is NOT required by the certified finite-sum consumer.
--
-- Least privilege is now factored through canonical R1:
--
--   R1: final nearResponseAt(J) = literal finite near sum
--   C0: embed(concrete certified fold) = literal finite near sum
--
-- The fold-local bridge compiles final nearResponseAt(J)=embed(certifiedFold)
-- mechanically.  Only one upper-order transport is then required.
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

r1RemovesSecondFinalNearIdentity :
  FoldBridge.ConcreteCertificateFinalScalarBoundary.independentSecondFinalNearIdentityRequiredAfterR1
    FoldBridge.canonicalConcreteCertificateFinalScalarBoundary ≡ false
r1RemovesSecondFinalNearIdentity = refl

foldLocalBridgeStillRequiresEmbeddedConcreteFold :
  FoldBridge.ConcreteCertificateFinalScalarBoundary.embeddedConcreteFoldToLiteralSumStillRequired
    FoldBridge.canonicalConcreteCertificateFinalScalarBoundary ≡ true
foldLocalBridgeStillRequiresEmbeddedConcreteFold = refl

r1PlusConcreteFoldCompilesFinalBridge :
  FoldBridge.ConcreteCertificateFinalScalarBoundary.r1PlusEmbeddedFoldCompilesFinalBridge
    FoldBridge.canonicalConcreteCertificateFinalScalarBoundary ≡ true
r1PlusConcreteFoldCompilesFinalBridge = refl

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

    secondFinalNearSameObjectTheoremAfterR1 : Bool
    secondFinalNearSameObjectTheoremAfterR1IsFalse : secondFinalNearSameObjectTheoremAfterR1 ≡ false

    embeddedConcreteFoldToLiteralSumStillRequired : Bool
    embeddedConcreteFoldToLiteralSumStillRequiredIsTrue : embeddedConcreteFoldToLiteralSumStillRequired ≡ true

    fullConcreteScalarRealizationStillCompatible : Bool
    fullConcreteScalarRealizationStillCompatibleIsTrue : fullConcreteScalarRealizationStillCompatible ≡ true

    concreteRealizationIsNewRHAnalyticTheorem : Bool
    concreteRealizationIsNewRHAnalyticTheoremIsFalse : concreteRealizationIsNewRHAnalyticTheorem ≡ false

    legacyRationalDirectLanePaysConcreteFinalScalar : Bool
    legacyRationalDirectLanePaysConcreteFinalScalarIsFalse : legacyRationalDirectLanePaysConcreteFinalScalar ≡ false

    toyWeilNatCarrierPaysConcreteFinalScalar : Bool
    toyWeilNatCarrierPaysConcreteFinalScalarIsFalse : toyWeilNatCarrierPaysConcreteFinalScalar ≡ false

    oneUpperOrderTransportStillRequired : Bool
    oneUpperOrderTransportStillRequiredIsTrue : oneUpperOrderTransportStillRequired ≡ true

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
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "For proof-carrying numerical execution, do not require a whole concrete realization of the final universal pole-quotient NearFar scalar. Reuse canonical R1 for final nearResponseAt(J)=literal finite sum; the machine backend proves only embed(certifiedFold)=that same literal finite sum, and equality transitivity compiles the final-near bridge. Then transport the certified upper relation once. Exact rational/interval arithmetic may remain on a distinct concrete carrier; no Fast-Cauchy quotient backend, selected Weil window, or determinant-q carrier equality is required. RH is not derived here."
