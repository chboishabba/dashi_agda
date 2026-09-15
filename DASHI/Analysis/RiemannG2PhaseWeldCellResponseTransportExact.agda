module DASHI.Analysis.RiemannG2PhaseWeldCellResponseTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2ProofRelevantTargetTranslationModulationExact as Phase
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as Weld

------------------------------------------------------------------------
-- PHASE WELD -> LITERAL CELL -> FINITE NEAR RESPONSE
--
-- The same-object phase weld supplies a pointwise equality between the even
-- modulation projection and the literal cosine factor.  The remaining step is
-- not another phase theorem: the literal aggregation operators must transport
-- pointwise equality.
--
-- We therefore expose exactly two congruence obligations:
--   * integrate respects pointwise equality of integrands;
--   * finiteNearSum respects pointwise equality of cell families.
--
-- Given those laws and an inhabited same-object phase weld, the equality can be
-- compiled through cellResponse, literalFiniteNearValue and finally the exact
-- nearResponseAt(chosen J) already owned by FinalPoleNearLiteralModel.
------------------------------------------------------------------------

record LiteralAggregationCongruence
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    (model : Literal.FinalPoleNearLiteralModel offInput) : Set₁ where
  private
    Scalar = NearFar.Scalar S
  field
    integrateCongruence :
      (f g : Scalar → Scalar) →
      ((u : Scalar) → f u ≡ g u) →
      Literal.integrate model f ≡ Literal.integrate model g

    finiteNearSumCongruence :
      (f g : Literal.ZeroIndex model → Scalar) →
      ((sigma : Literal.ZeroIndex model) → f sigma ≡ g sigma) →
      Literal.finiteNearSum model f ≡ Literal.finiteNearSum model g

open LiteralAggregationCongruence public

phaseProjectedScalar :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  NearFar.Scalar S →
  Literal.ZeroIndex model →
  NearFar.Scalar S
phaseProjectedScalar {H = H} weld u sigma =
  Weld.phaseToLiteralScalar weld
    (Phase.evenProjection H
      (Phase.modulation H
        (Weld.frequencyFromLiteralScalar weld u)
        (Weld.ordinateFromLiteralScalar weld
          (Literal.targetRelativeGap _ sigma))))

phaseRealizedIntegrand :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  Literal.ZeroIndex model →
  NearFar.Scalar S →
  NearFar.Scalar S
phaseRealizedIntegrand {model = model} weld sigma u =
  Literal.mul model
    (Literal.mul model
      (Literal.mul model
        (Literal.four model)
        (Literal.poleTaperValue model u))
      (Literal.mul model
        (Literal.multiplicity model sigma)
        (Literal.cosh model
          (Literal.mul model
            (Literal.horizontalDisplacement model sigma) u))))
    (phaseProjectedScalar weld u sigma)

literalCosineIntegrand :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport} →
  (model : Literal.FinalPoleNearLiteralModel offInput) →
  Literal.ZeroIndex model →
  NearFar.Scalar S →
  NearFar.Scalar S
literalCosineIntegrand model sigma u =
  Literal.mul model
    (Literal.mul model
      (Literal.mul model
        (Literal.four model)
        (Literal.poleTaperValue model u))
      (Literal.mul model
        (Literal.multiplicity model sigma)
        (Literal.cosh model
          (Literal.mul model
            (Literal.horizontalDisplacement model sigma) u))))
    (Literal.cos model
      (Literal.mul model (Literal.targetRelativeGap model sigma) u))

phaseIntegrandEqualsLiteralCosineIntegrand :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  (sigma : Literal.ZeroIndex model) →
  (u : NearFar.Scalar S) →
  phaseRealizedIntegrand weld sigma u
  ≡ literalCosineIntegrand model sigma u
phaseIntegrandEqualsLiteralCosineIntegrand {model = model} weld sigma u =
  cong
    (λ phaseValue →
      Literal.mul model
        (Literal.mul model
          (Literal.mul model
            (Literal.four model)
            (Literal.poleTaperValue model u))
          (Literal.mul model
            (Literal.multiplicity model sigma)
            (Literal.cosh model
              (Literal.mul model
                (Literal.horizontalDisplacement model sigma) u))))
        phaseValue)
    (Weld.literalEvenPhasePaid weld u sigma)

phaseRealizedCellResponse :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  Literal.ZeroIndex model →
  NearFar.Scalar S
phaseRealizedCellResponse {model = model} weld sigma =
  Literal.integrate model (phaseRealizedIntegrand weld sigma)

cellResponseEqualsPhaseRealizedCell :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  LiteralAggregationCongruence model →
  (sigma : Literal.ZeroIndex model) →
  Literal.cellResponse model sigma ≡ phaseRealizedCellResponse weld sigma
cellResponseEqualsPhaseRealizedCell {model = model} weld congruence sigma =
  trans
    (Literal.cellResponseIsLiteralReflectionPair model sigma)
    (sym
      (integrateCongruence congruence
        (phaseRealizedIntegrand weld sigma)
        (literalCosineIntegrand model sigma)
        (phaseIntegrandEqualsLiteralCosineIntegrand weld sigma)))

phaseRealizedFiniteNearValue :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  NearFar.Scalar S
phaseRealizedFiniteNearValue {model = model} weld =
  Literal.finiteNearSum model (phaseRealizedCellResponse weld)

literalFiniteNearEqualsPhaseRealizedFiniteNear :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  (congruence : LiteralAggregationCongruence model) →
  Literal.literalFiniteNearValue model ≡ phaseRealizedFiniteNearValue weld
literalFiniteNearEqualsPhaseRealizedFiniteNear {model = model} weld congruence =
  trans
    (Literal.literalFiniteNearValueIsSum model)
    (finiteNearSumCongruence congruence
      (Literal.cellResponse model)
      (phaseRealizedCellResponse weld)
      (cellResponseEqualsPhaseRealizedCell weld congruence))

finalNearResponseEqualsPhaseRealizedFiniteNear :
  ∀ {S transport}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {model : Literal.FinalPoleNearLiteralModel offInput}
    {H : Phase.ProofRelevantTargetTranslationModulation} →
  (weld : Weld.LiteralPhaseModulationWeld offInput model H) →
  (congruence : LiteralAggregationCongruence model) →
  Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  ≡ phaseRealizedFiniteNearValue weld
finalNearResponseEqualsPhaseRealizedFiniteNear {model = model} weld congruence =
  trans
    (Literal.finalNearResponseIsLiteralFiniteNear model)
    (literalFiniteNearEqualsPhaseRealizedFiniteNear weld congruence)

record PhaseWeldCellResponseTransportBoundary : Set where
  constructor phase-weld-cell-response-transport-boundary
  field
    sameObjectPhaseWeldStillRequired : Bool
    integrationCongruenceExposedExplicitly : Bool
    finiteNearSumCongruenceExposedExplicitly : Bool
    phaseEqualityTransportedThroughLiteralCellConditionally : Bool
    phaseEqualityTransportedThroughFiniteNearConditionally : Bool
    finalNearResponseEqualityCompiledConditionally : Bool
    aggregationCongruenceInhabitedHere : Bool
    universalPoleQuotientWeldInhabitedHere : Bool
    numericFiniteNearBudgetPaidHere : Bool
    strictRHMarginPaidHere : Bool
open PhaseWeldCellResponseTransportBoundary public

canonicalPhaseWeldCellResponseTransportBoundary : PhaseWeldCellResponseTransportBoundary
canonicalPhaseWeldCellResponseTransportBoundary =
  phase-weld-cell-response-transport-boundary
    true true true true true true false false false false

data PhaseWeldCellResponseTransportResidual : Set where
  inhabitUniversalPoleQuotientPhaseWeld : PhaseWeldCellResponseTransportResidual
  proveLiteralIntegrationCongruence : PhaseWeldCellResponseTransportResidual
  proveLiteralFiniteNearSumCongruence : PhaseWeldCellResponseTransportResidual
  deriveNumericFiniteNearBudget : PhaseWeldCellResponseTransportResidual
  combineWithOwnedFarShellAfterNearBudget : PhaseWeldCellResponseTransportResidual

firstPhaseWeldCellResponseTransportResidual : PhaseWeldCellResponseTransportResidual
firstPhaseWeldCellResponseTransportResidual = inhabitUniversalPoleQuotientPhaseWeld
