module DASHI.Reasoning.Trialectic369HistoricalMultiplicityAttachmentDescentBidiExact where

------------------------------------------------------------------------
-- HISTORICAL SAME-ACTION ATTACHMENT -> MINIMAL PROJECTION DESCENT
--
-- Reuse the older actual X6 x Fin90 evaluation intertwiner rather than
-- requiring a second action construction.
--
-- Important: the historical attachment has its OWN inertia carrier and a
-- map to the actual central inertia.  An action assertion on that carrier
-- is not automatically an assertion for ALL actual inertia elements.
--
-- This module:
--  * recovers the literal transported product action on attached elements;
--  * proves independence of X6 on that represented subgroup;
--  * proves the selected multiplicity action is zero-position evaluation;
--  * derives full projection descent exactly when source-inertia coverage is
--    provided.  No coverage or Monster-source recognition is asserted here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BActualMultiplicityEvaluationFromRecognitionExact as Eval
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Historical
import DASHI.Reasoning.Trialectic369MultiplicityProjectionDescentCompilerExact as Descent
import DASHI.Reasoning.Trialectic369MultiplicityProjectionPositionIndependenceExact as Position

historicalActionEqualsTransportedActualAction :
  ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source) →
    (i : Historical.MultiplicityInertia attachment) →
    (x : H.X6) →
    (m : Fin 90) →
    Descent.transportedActualProductAct
      source (Historical.actualInertia attachment i) (x , m)
    ≡
    ( Historical.heisenbergAct attachment i x
    , Historical.multiplicityAct attachment i m )
historicalActionEqualsTransportedActualAction
    {source} attachment i x m =
  trans
    (cong
      (Eval.actualEvaluationInverse (Action.recognition source))
      (sym
        (Historical.evaluationIntertwinesInertia
          attachment i x m)))
    (Eval.actualEvaluationLeftInverse
      (Action.recognition source)
      (Historical.heisenbergAct attachment i x ,
       Historical.multiplicityAct attachment i m))

historicalMultiplicityOutputIndependentOfPosition :
  ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source) →
    (i : Historical.MultiplicityInertia attachment) →
    (x : H.X6) →
    (m : Fin 90) →
    Position.multiplicityOutput
      source (Historical.actualInertia attachment i) x m
    ≡ Historical.multiplicityAct attachment i m
historicalMultiplicityOutputIndependentOfPosition attachment i x m =
  cong proj₂
    (historicalActionEqualsTransportedActualAction
      attachment i x m)

historicalActionIsCanonicalAtZero :
  ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source) →
    (i : Historical.MultiplicityInertia attachment) →
    (m : Fin 90) →
    Historical.multiplicityAct attachment i m
    ≡ Position.canonicalMultiplicityAct
        source (Historical.actualInertia attachment i) m
historicalActionIsCanonicalAtZero {source} attachment i m =
  sym (historicalMultiplicityOutputIndependentOfPosition
    attachment i Position.zeroPosition m)

historicalSourceHasPositionIndependence :
  ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source) →
    (i : Historical.MultiplicityInertia attachment) →
    (x : H.X6) →
    (m : Fin 90) →
    Position.multiplicityOutput
      source (Historical.actualInertia attachment i) x m
    ≡ Position.multiplicityOutput
        source (Historical.actualInertia attachment i)
        Position.zeroPosition m
historicalSourceHasPositionIndependence attachment i x m =
  trans
    (historicalMultiplicityOutputIndependentOfPosition
      attachment i x m)
    (sym
      (historicalMultiplicityOutputIndependentOfPosition
        attachment i Position.zeroPosition m))

record HistoricalInertiaCoverage
    ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source)
    : Set₁ where
  field
    coversActualInertia :
      (inertia : Descent.ActualInertia source) →
      Σ (Historical.MultiplicityInertia attachment)
        (λ i → Historical.actualInertia attachment i ≡ inertia)

open HistoricalInertiaCoverage public

positionIndependenceFromHistoricalCoverage :
  ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source) →
    HistoricalInertiaCoverage attachment →
    Position.MultiplicityPositionIndependence source
positionIndependenceFromHistoricalCoverage {source} attachment coverage =
  record
    { independentOfPosition = λ inertia x m →
        let represented = coversActualInertia coverage inertia
            i = proj₁ represented
            eq = proj₂ represented
        in
        trans
          (sym
            (cong (λ j → Position.multiplicityOutput source j x m) eq))
          (trans
            (historicalSourceHasPositionIndependence attachment i x m)
            (cong
              (λ j → Position.multiplicityOutput
                source j Position.zeroPosition m)
              eq))
    }

descentFromHistoricalCoverage :
  ∀ {source}
    (attachment : Historical.ActualMultiplicityInertiaAttachment source) →
    HistoricalInertiaCoverage attachment →
    Descent.MultiplicityProjectionDescent source
descentFromHistoricalCoverage {source} attachment coverage =
  Position.descentFromPositionIndependence source
    (positionIndependenceFromHistoricalCoverage attachment coverage)

record HistoricalAttachmentReuseBoundary : Set where
  constructor historical-attachment-reuse-boundary
  field
    existingSameActionEvaluationReused : Bool
    transportedProductActionRecovered : Bool
    multiplicityProjectionIndependentOnAttachedInertia : Bool
    attachedActionEqualsCanonicalZeroPositionEvaluation : Bool
    fullDescentCompiledFromExplicitCoverage : Bool
    historicalInertiaAutomaticallyCoversActualInertia : Bool
    actualMonsterAttachmentInhabitedHere : Bool
    extraIndependentX6ActionDemanded : Bool

canonicalHistoricalAttachmentReuseBoundary : HistoricalAttachmentReuseBoundary
canonicalHistoricalAttachmentReuseBoundary =
  historical-attachment-reuse-boundary
    true true true true true false false false
