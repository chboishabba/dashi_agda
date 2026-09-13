module DASHI.Analysis.RiemannG2DirectComplementUnpaidContextExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Legacy
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- UNPAID DIRECT-COMPLEMENT CONTEXT
--
-- The historical DirectIndependentComplementMarginInput mixed two logically
-- different things in one record:
--
--   * same-object/order/taper/cluster representation needed to state the final
--     consumer; and
--   * the strict joint complement inequality that is the actual analytic leaf.
--
-- That makes it impossible for a lower theorem (for example the literal phase
-- sum theorem) to be indexed by the final representation context without also
-- presupposing the theorem it is intended to produce.
--
-- This record is the least-privilege unpaid context: it contains every old field
-- except `literalComplementStrictBelowMargin`.
------------------------------------------------------------------------

record DirectComplementUnpaidContext
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    surface : Split.OrderedAdditiveComplementSurface
    cluster : Cluster.PoleQuotientClusterMarginTarget

    offScalarIdentity :
      Off.Scalar off ≡ Complement.Scalar (Split.order surface)
    gammaScalarIdentity :
      Gamma.Scalar gamma ≡ Complement.Scalar (Split.order surface)
    clusterScalarIdentity :
      Cluster.Scalar cluster ≡ Complement.Scalar (Split.order surface)

    offGammaTaperCarrierIdentity : Off.Taper off ≡ Gamma.Taper gamma
    offClusterTaperCarrierIdentity : Off.Taper off ≡ Cluster.Taper cluster

    sameUniversalTaperOffGamma :
      Existing.cast offGammaTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Gamma.universalPoleQuotientTaper gamma

    sameUniversalTaperOffCluster :
      Existing.cast offClusterTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Cluster.universalPoleQuotientTaper cluster

    offOrderTransport :
      {x y : Off.Scalar off} ->
      Off._≤_ off x y ->
      Complement._≤_ (Split.order surface)
        (Existing.cast offScalarIdentity x)
        (Existing.cast offScalarIdentity y)

    gammaOrderTransport :
      {x y : Gamma.Scalar gamma} ->
      Gamma._≤_ gamma x y ->
      Complement._≤_ (Split.order surface)
        (Existing.cast gammaScalarIdentity x)
        (Existing.cast gammaScalarIdentity y)

    clusterOrderTransport :
      {x y : Cluster.Scalar cluster} ->
      Cluster._≤_ cluster x y ->
      Complement._≤_ (Split.order surface)
        (Existing.cast clusterScalarIdentity x)
        (Existing.cast clusterScalarIdentity y)

    clusterEqualsOffPlusGamma :
      Existing.cast clusterScalarIdentity
        (Cluster.ClusterResponse cluster
          (Cluster.universalPoleQuotientTaper cluster))
      ≡ Split.add surface
          (Existing.cast offScalarIdentity
            (Off.OffOrdinateResponse off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast gammaScalarIdentity
            (Gamma.GammaResponse gamma
              (Gamma.universalPoleQuotientTaper gamma)))

    complementEstimateIndependentOfFinalBalance : Set
    complementEstimateIndependentOfFinalBalanceReceipt :
      complementEstimateIndependentOfFinalBalance

    contextReference : String

open DirectComplementUnpaidContext public

------------------------------------------------------------------------
-- The one genuine scalar theorem, now separated from the context that states it.
------------------------------------------------------------------------

record CanonicalJointMarginPayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : DirectComplementUnpaidContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
    cluster0 = cluster context
  field
    literalComplementStrictBelowMargin :
      Complement._<_ (Split.order (surface context))
        (Split.add (surface context)
          (Existing.cast (offScalarIdentity context)
            (Off.OffOrdinateBudget off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast (gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (clusterScalarIdentity context)
          (Cluster.ClusterMargin cluster0
            (Cluster.universalPoleQuotientTaper cluster0)))

    paymentReference : String

open CanonicalJointMarginPayment public

------------------------------------------------------------------------
-- Compatibility compiler to the old combined record.  This proves that the
-- split removes a prerequisite; it does not change the downstream theorem.
------------------------------------------------------------------------

compileContextAndPaymentToLegacyInput :
  forall {S transport targets} ->
  (context : DirectComplementUnpaidContext
    {S = S} {transport = transport} targets) ->
  CanonicalJointMarginPayment context ->
  Legacy.DirectIndependentComplementMarginInput targets
compileContextAndPaymentToLegacyInput context payment = record
  { Legacy.surface = surface context
  ; Legacy.cluster = cluster context
  ; Legacy.offScalarIdentity = offScalarIdentity context
  ; Legacy.gammaScalarIdentity = gammaScalarIdentity context
  ; Legacy.clusterScalarIdentity = clusterScalarIdentity context
  ; Legacy.offGammaTaperCarrierIdentity = offGammaTaperCarrierIdentity context
  ; Legacy.offClusterTaperCarrierIdentity = offClusterTaperCarrierIdentity context
  ; Legacy.sameUniversalTaperOffGamma = sameUniversalTaperOffGamma context
  ; Legacy.sameUniversalTaperOffCluster = sameUniversalTaperOffCluster context
  ; Legacy.offOrderTransport = offOrderTransport context
  ; Legacy.gammaOrderTransport = gammaOrderTransport context
  ; Legacy.clusterOrderTransport = clusterOrderTransport context
  ; Legacy.clusterEqualsOffPlusGamma = clusterEqualsOffPlusGamma context
  ; Legacy.complementEstimateIndependentOfFinalBalance =
      complementEstimateIndependentOfFinalBalance context
  ; Legacy.complementEstimateIndependentOfFinalBalanceReceipt =
      complementEstimateIndependentOfFinalBalanceReceipt context
  ; Legacy.literalComplementStrictBelowMargin =
      literalComplementStrictBelowMargin payment
  ; Legacy.estimateReference = paymentReference payment
  ; Legacy.transportReference = contextReference context
  }

contextAndPaymentContradiction :
  forall {S transport targets} ->
  (context : DirectComplementUnpaidContext
    {S = S} {transport = transport} targets) ->
  CanonicalJointMarginPayment context ->
  ⊥
contextAndPaymentContradiction context payment =
  Legacy.directIndependentComplementContradiction
    (compileContextAndPaymentToLegacyInput context payment)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record UnpaidContextBoundary : Set where
  constructor unpaid-context-boundary
  field
    representationContextContainsStrictMarginPayment : Bool
    representationContextContainsStrictMarginPaymentIsFalse :
      representationContextContainsStrictMarginPayment ≡ false

    strictMarginIsSeparateTheoremBearingRecord : Bool
    strictMarginIsSeparateTheoremBearingRecordIsTrue :
      strictMarginIsSeparateTheoremBearingRecord ≡ true

    oldCombinedInputStillSupportedByCompiler : Bool
    oldCombinedInputStillSupportedByCompilerIsTrue :
      oldCombinedInputStillSupportedByCompiler ≡ true

    splittingContextFromPaymentProvesMargin : Bool
    splittingContextFromPaymentProvesMarginIsFalse :
      splittingContextFromPaymentProvesMargin ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalUnpaidContextBoundary : UnpaidContextBoundary
canonicalUnpaidContextBoundary =
  unpaid-context-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    "The final same-object/order/taper/cluster context is now unpaid: it no longer contains the strict joint margin theorem. The sole scalar payment is a separate CanonicalJointMarginPayment. Context plus payment compiles back to the historical DirectIndependentComplementMarginInput and hence to contradiction. This removes the structural circularity that prevented a literal phase theorem from genuinely producing the final margin; it does not prove that theorem or RH."
