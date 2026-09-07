module DASHI.Analysis.RiemannG2LiteralPhaseJointMarginCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Margin
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- LITERAL PHASE-SUM -> CANONICAL ONE-LEAF MARGIN
--
-- The canonical consumer is phrased using the final transport scalar
-- `nearResponseAt chosenJ`.  The introspective observer refinement instead
-- exposes the literal phase-visible finite sum.  Once those are identified on
-- the same object, the research theorem should be stated directly on the
-- literal sum; rewriting then produces the canonical one-leaf margin.
------------------------------------------------------------------------

record LiteralPhaseJointMarginPayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (model : Literal.FinalPoleNearLiteralModel (Direct.offInput targets))
    (input : Margin.DirectIndependentComplementMarginInput targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
    cluster0 = Margin.cluster input
  field
    literalPhaseStrictBelowMargin :
      Complement._<_ (Split.order (Margin.surface input))
        (Split.add (Margin.surface input)
          (Existing.cast (Margin.offScalarIdentity input)
            (NearFar.add S
              (Literal.literalFiniteNearValue model)
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff (Direct.offInput targets)))))
          (Existing.cast (Margin.gammaScalarIdentity input)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (Margin.clusterScalarIdentity input)
          (Cluster.ClusterMargin cluster0
            (Cluster.universalPoleQuotientTaper cluster0)))

    paymentReference : String

open LiteralPhaseJointMarginPayment public

compileLiteralPhaseMarginToCanonicalMargin :
  forall {S transport targets model input} ->
  LiteralPhaseJointMarginPayment
    {S = S} {transport = transport}
    targets model input ->
  Margin.literalComplementStrictBelowMargin input
compileLiteralPhaseMarginToCanonicalMargin
  {S = S} {transport = transport} {targets = targets}
  {model = model} {input = input} payment
  with Literal.finalNearResponseIsLiteralFiniteNear model
... | refl = literalPhaseStrictBelowMargin payment

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LiteralPhaseJointMarginBoundary : Set where
  constructor literal-phase-joint-margin-boundary
  field
    analyticTheoremMayBeStatedOnLiteralPhaseSum : Bool
    analyticTheoremMayBeStatedOnLiteralPhaseSumIsTrue :
      analyticTheoremMayBeStatedOnLiteralPhaseSum ≡ true

    secondNearEnvelopeRequired : Bool
    secondNearEnvelopeRequiredIsFalse :
      secondNearEnvelopeRequired ≡ false

    rewritingLiteralSumToFinalNearCreatesNewAnalysis : Bool
    rewritingLiteralSumToFinalNearCreatesNewAnalysisIsFalse :
      rewritingLiteralSumToFinalNearCreatesNewAnalysis ≡ false

    literalPhasePaymentCompilesCanonicalOneLeafMargin : Bool
    literalPhasePaymentCompilesCanonicalOneLeafMarginIsTrue :
      literalPhasePaymentCompilesCanonicalOneLeafMargin ≡ true

    literalPhasePaymentInhabitedHere : Bool
    literalPhasePaymentInhabitedHereIsFalse :
      literalPhasePaymentInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLiteralPhaseJointMarginBoundary :
  LiteralPhaseJointMarginBoundary
canonicalLiteralPhaseJointMarginBoundary =
  literal-phase-joint-margin-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "After the final near observer is proof-relevantly identified with its literal reflection-paired phase sum, state the remaining high theorem directly as literalFiniteNearValue + transported far budget + literal Gamma response < quantitative cluster margin on the exact universal pole-quotient carrier. The exact final-near equality rewrites this into the canonical direct one-leaf margin; no second near envelope or additional harmonic theorem is introduced. The literal phase inequality itself remains unproved here, so RH is not derived."
