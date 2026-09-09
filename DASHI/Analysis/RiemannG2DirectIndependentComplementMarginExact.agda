module DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- DIRECT ONE-LEAF COMPLEMENT CONTRADICTION
--
-- This is the canonical consumer path after the allowance-authority audit.
-- It bypasses producer-assigned allowances completely and feeds the literal
-- channel targets directly into the already-owned split-complement compiler.
--
-- The sole scalar theorem is the independently established strict margin
--
--   cast(B_off(J)) + cast(B_Gamma(g_pole)) < cast(M_cluster),
--
-- where
--
--   B_off(J)   = D_near(J) + B_far(J),
--   B_Gamma(g) = D_Gamma(g).
--
-- The final cluster balance is a separate same-object receipt and may not be
-- used to manufacture this margin.
------------------------------------------------------------------------

record DirectIndependentComplementMarginInput
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

    literalComplementStrictBelowMargin :
      Complement._<_ (Split.order surface)
        (Split.add surface
          (Existing.cast offScalarIdentity
            (Off.OffOrdinateBudget off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast gammaScalarIdentity
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast clusterScalarIdentity
          (Cluster.ClusterMargin cluster
            (Cluster.universalPoleQuotientTaper cluster)))

    estimateReference : String
    transportReference : String

open DirectIndependentComplementMarginInput public

compiledClusterLower :
  forall {S transport targets} ->
  (input : DirectIndependentComplementMarginInput
    {S = S} {transport = transport} targets) ->
  let cluster0 = cluster input
  in Complement._≤_ (Split.order (surface input))
      (Existing.cast (clusterScalarIdentity input)
        (Cluster.ClusterMargin cluster0
          (Cluster.universalPoleQuotientTaper cluster0)))
      (Existing.cast (clusterScalarIdentity input)
        (Cluster.ClusterResponse cluster0
          (Cluster.universalPoleQuotientTaper cluster0)))
compiledClusterLower input =
  clusterOrderTransport input
    (Cluster.quantitativeClusterMarginLower (cluster input))

compiledOffUpper :
  forall {S transport targets} ->
  (input : DirectIndependentComplementMarginInput
    {S = S} {transport = transport} targets) ->
  let off = Direct.directOffTarget targets
  in Complement._≤_ (Split.order (surface input))
      (Existing.cast (offScalarIdentity input)
        (Off.OffOrdinateResponse off
          (Off.universalPoleQuotientTaper off)))
      (Existing.cast (offScalarIdentity input)
        (Off.OffOrdinateBudget off
          (Off.universalPoleQuotientTaper off)))
compiledOffUpper {targets = targets} input =
  offOrderTransport input
    (Off.signedOffOrdinateUpper (Direct.directOffTarget targets))

compiledGammaUpper :
  forall {S transport targets} ->
  (input : DirectIndependentComplementMarginInput
    {S = S} {transport = transport} targets) ->
  let gamma = Direct.directGammaTarget targets
  in Complement._≤_ (Split.order (surface input))
      (Existing.cast (gammaScalarIdentity input)
        (Gamma.GammaResponse gamma
          (Gamma.universalPoleQuotientTaper gamma)))
      (Existing.cast (gammaScalarIdentity input)
        (Gamma.GammaBudget gamma
          (Gamma.universalPoleQuotientTaper gamma)))
compiledGammaUpper {targets = targets} input =
  gammaOrderTransport input
    (Gamma.gammaResponseUpper (Direct.directGammaTarget targets))

compileSplitComplementMargin :
  forall {S transport targets} ->
  (input : DirectIndependentComplementMarginInput
    {S = S} {transport = transport} targets) ->
  Split.SplitPoleQuotientComplementMargin (surface input)
compileSplitComplementMargin {targets = targets} input =
  Split.split-pole-quotient-complement-margin
    (Existing.cast (clusterScalarIdentity input)
      (Cluster.ClusterResponse (cluster input)
        (Cluster.universalPoleQuotientTaper (cluster input))))
    (Existing.cast (offScalarIdentity input)
      (Off.OffOrdinateResponse (Direct.directOffTarget targets)
        (Off.universalPoleQuotientTaper (Direct.directOffTarget targets))))
    (Existing.cast (gammaScalarIdentity input)
      (Gamma.GammaResponse (Direct.directGammaTarget targets)
        (Gamma.universalPoleQuotientTaper (Direct.directGammaTarget targets))))
    (Existing.cast (offScalarIdentity input)
      (Off.OffOrdinateBudget (Direct.directOffTarget targets)
        (Off.universalPoleQuotientTaper (Direct.directOffTarget targets))))
    (Existing.cast (gammaScalarIdentity input)
      (Gamma.GammaBudget (Direct.directGammaTarget targets)
        (Gamma.universalPoleQuotientTaper (Direct.directGammaTarget targets))))
    (Existing.cast (clusterScalarIdentity input)
      (Cluster.ClusterMargin (cluster input)
        (Cluster.universalPoleQuotientTaper (cluster input))))
    (clusterEqualsOffPlusGamma input)
    (compiledClusterLower input)
    (compiledOffUpper input)
    (compiledGammaUpper input)
    (literalComplementStrictBelowMargin input)

directIndependentComplementContradiction :
  forall {S transport targets} ->
  DirectIndependentComplementMarginInput
    {S = S} {transport = transport} targets ->
  ⊥
directIndependentComplementContradiction input =
  Split.splitPoleQuotientComplementContradiction
    (surface input)
    (compileSplitComplementMargin input)

record DirectIndependentComplementMarginBoundary : Set where
  constructor direct-independent-complement-margin-boundary
  field
    consumerAssignedAllowanceLayerRequired : Bool
    consumerAssignedAllowanceLayerRequiredIsFalse :
      consumerAssignedAllowanceLayerRequired ≡ false

    producerChoosesDownstreamAllowance : Bool
    producerChoosesDownstreamAllowanceIsFalse :
      producerChoosesDownstreamAllowance ≡ false

    separateFiniteNearEnvelopeLeafRequired : Bool
    separateFiniteNearEnvelopeLeafRequiredIsFalse :
      separateFiniteNearEnvelopeLeafRequired ≡ false

    separateGammaEnvelopeLeafRequired : Bool
    separateGammaEnvelopeLeafRequiredIsFalse :
      separateGammaEnvelopeLeafRequired ≡ false

    transportedFarUpperStillUsed : Bool
    transportedFarUpperStillUsedIsTrue :
      transportedFarUpperStillUsed ≡ true

    oneIndependentJointMarginIsScalarLeaf : Bool
    oneIndependentJointMarginIsScalarLeafIsTrue :
      oneIndependentJointMarginIsScalarLeaf ≡ true

    finalBalanceMayManufactureJointMargin : Bool
    finalBalanceMayManufactureJointMarginIsFalse :
      finalBalanceMayManufactureJointMargin ≡ false

    directSplitCompilerProducesContradiction : Bool
    directSplitCompilerProducesContradictionIsTrue :
      directSplitCompilerProducesContradiction ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalDirectIndependentComplementMarginBoundary :
  DirectIndependentComplementMarginBoundary
canonicalDirectIndependentComplementMarginBoundary =
  direct-independent-complement-margin-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    "The canonical one-leaf route now bypasses the historical allowance layer rather than letting a producer choose a consumer allowance. Off uses the independently constructed cutoff budget D_near(J)+B_far(J); Gamma uses its literal response as a source-order budget. The only scalar analytic leaf is their transported sum strictly below the quantitative cluster margin, independently of the final cluster balance. Source order/scalar/taper identities and the balance remain representation inputs. The existing split-complement compiler then yields contradiction directly. RH is not derived here."
