module DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact where

------------------------------------------------------------------------
-- SAME-ACTION BIDI: ACTUAL ZETA ACTION -> MULTIPLICITY ACTION -> 12 + 78
--
-- Once the actual zeta-sector recognition is supplied, the repository already
-- owns a literal evaluation isomorphism
--
--   X6 x Fin 90 <-> W_zeta.
--
-- The next scientific datum is therefore not a fresh 90-dimensional carrier.
-- It is the action induced on the literal Fin 90 multiplicity coordinate by
-- the same actual inertia action on W_zeta.  Only after that same-object weld
-- may the existing 12 + 78 block-recognition interface be applied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BActualMultiplicityEvaluationFromRecognitionExact as Eval
import DASHI.Moonshine.Monster3BActualZetaPromotionPipelineExact as Pipeline
import DASHI.Moonshine.Monster3BMultiplicityTwelveSeventyEightRecognitionExact as Split
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action

------------------------------------------------------------------------
-- 1. Attach the same actual inertia action to the literal X6 x Fin 90 chart.
------------------------------------------------------------------------

record ActualMultiplicityInertiaAttachment
    (source : Action.ActualMonster3BActionRecognition) : Set₁ where
  field
    MultiplicityInertia : Set

    actualInertia :
      MultiplicityInertia →
      Inertia.CentralInertia (Action.normalizerAction source)

    heisenbergAct : MultiplicityInertia → H.X6 → H.X6
    multiplicityAct : MultiplicityInertia → Fin 90 → Fin 90

    evaluationIntertwinesInertia :
      (inertia : MultiplicityInertia) →
      (position : H.X6) →
      (multiplicity : Fin 90) →
      Eval.actualEvaluationMap
        (Action.recognition source)
        (heisenbergAct inertia position , multiplicityAct inertia multiplicity)
      ≡ Pipeline.chosenInertiaAction
          (Action.actualPromotionPipeline source)
          (actualInertia inertia)
          (Eval.actualEvaluationMap
            (Action.recognition source)
            (position , multiplicity))

open ActualMultiplicityInertiaAttachment public

------------------------------------------------------------------------
-- 2. The existing 12 + 78 recognition must use that exact multiplicity action.
------------------------------------------------------------------------

record ActualMultiplicityTwelveSeventyEightAttachment
    (source : Action.ActualMonster3BActionRecognition) : Set₁ where
  field
    inertiaAttachment : ActualMultiplicityInertiaAttachment source

  open ActualMultiplicityInertiaAttachment inertiaAttachment public

  field
    TwelveCarrier SeventyEightCarrier : Set

    blockRecognition :
      Split.TwelveSeventyEightRecognition
        (Fin 90)
        MultiplicityInertia
        TwelveCarrier
        SeventyEightCarrier

    blockActionIsActualMultiplicityAction :
      (inertia : MultiplicityInertia) →
      (multiplicity : Fin 90) →
      Split.multiplicityAct blockRecognition inertia multiplicity
      ≡ multiplicityAct inertia multiplicity

open ActualMultiplicityTwelveSeventyEightAttachment public

------------------------------------------------------------------------
-- 3. Stability is now about the actual multiplicity action, not a parallel one.
------------------------------------------------------------------------

twelveBlockStableForActualMultiplicity :
  ∀ {source}
    (attachment : ActualMultiplicityTwelveSeventyEightAttachment source) →
    (inertia : MultiplicityInertia attachment) →
    (state : TwelveCarrier attachment) →
    Split.toSum (blockRecognition attachment)
      (multiplicityAct attachment inertia
        (Split.fromSum (blockRecognition attachment) (inj₁ state)))
    ≡ inj₁ (Split.twelveAct (blockRecognition attachment) inertia state)
twelveBlockStableForActualMultiplicity attachment inertia state =
  trans
    (cong (Split.toSum (blockRecognition attachment))
      (sym
        (blockActionIsActualMultiplicityAction attachment inertia
          (Split.fromSum (blockRecognition attachment) (inj₁ state)))))
    (Split.twelveBlockStable (blockRecognition attachment) inertia state)

seventyEightBlockStableForActualMultiplicity :
  ∀ {source}
    (attachment : ActualMultiplicityTwelveSeventyEightAttachment source) →
    (inertia : MultiplicityInertia attachment) →
    (state : SeventyEightCarrier attachment) →
    Split.toSum (blockRecognition attachment)
      (multiplicityAct attachment inertia
        (Split.fromSum (blockRecognition attachment) (inj₂ state)))
    ≡ inj₂ (Split.seventyEightAct (blockRecognition attachment) inertia state)
seventyEightBlockStableForActualMultiplicity attachment inertia state =
  trans
    (cong (Split.toSum (blockRecognition attachment))
      (sym
        (blockActionIsActualMultiplicityAction attachment inertia
          (Split.fromSum (blockRecognition attachment) (inj₂ state)))))
    (Split.seventyEightBlockStable (blockRecognition attachment) inertia state)

------------------------------------------------------------------------
-- 4. The actual-sector action on an evaluated tensor is already the attached
--    inertia action; no second representation carrier is introduced.
------------------------------------------------------------------------

actualSectorInertiaOnEvaluation :
  ∀ {source}
    (attachment : ActualMultiplicityTwelveSeventyEightAttachment source) →
    (inertia : MultiplicityInertia attachment) →
    (position : H.X6) →
    (multiplicity : Fin 90) →
    Eval.actualEvaluationMap
      (Action.recognition source)
      (heisenbergAct attachment inertia position ,
       multiplicityAct attachment inertia multiplicity)
    ≡ Pipeline.chosenInertiaAction
        (Action.actualPromotionPipeline source)
        (actualInertia attachment inertia)
        (Eval.actualEvaluationMap
          (Action.recognition source)
          (position , multiplicity))
actualSectorInertiaOnEvaluation attachment =
  evaluationIntertwinesInertia attachment

------------------------------------------------------------------------
-- 5. Boundary: arithmetic and generic cocycle algebra are not reopened.
------------------------------------------------------------------------

record MultiplicityInertiaTwelveSeventyEightBoundary : Set where
  constructor multiplicity-inertia-twelve-seventy-eight-boundary
  field
    literalFin90CoordinateAlreadyOwned : Bool
    sameActualInertiaActionRequired : Bool
    twelvePlusSeventyEightArithmeticIsNotScientificLeaf : Bool
    blockStabilityGeneratedAfterSameActionWeld : Bool
    freshParallelMultiplicityRepresentationIntroduced : Bool
    actualSameActionAttachmentInhabitedHere : Bool

canonicalMultiplicityInertiaTwelveSeventyEightBoundary :
  MultiplicityInertiaTwelveSeventyEightBoundary
canonicalMultiplicityInertiaTwelveSeventyEightBoundary =
  multiplicity-inertia-twelve-seventy-eight-boundary
    true true true true false false
