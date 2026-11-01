module DASHI.Reasoning.Trialectic369MultiplicityNormalizerTranslationDescentExact where

------------------------------------------------------------------------
-- NORMALIZER TRANSLATION EQUIVARIANCE -> MULTIPLICITY DESCENT
--
-- DASHI CONTRIBUTION
--
-- The repo already proves:
--
--   six unit-generator invariances
--     <-> multiplicity projection independence of X6
--     <-> multiplicity projection descent.
--
-- The actual Monster normalizer need not commute with each X6 translation.
-- Conjugation may send an axis translation to another transformation on the
-- OUTPUT X6 coordinate.  This module isolates exactly the more natural
-- sufficient datum:
--
--   A(g, translate_i x, m)
--       = (kappa(g,i, pi_X A(g,x,m)), pi_90 A(g,x,m)).
--
-- The output X6 coordinate may move nontrivially.  The equality only
-- requires the multiplicity projection to stay fixed under the generator.
--
-- This is a conditional compiler: no source-native Monster action,
-- conjugation law or representation-level multiplicity claim is manufactured.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Reasoning.Trialectic369MultiplicityProjectionDescentCompilerExact as Descent
import DASHI.Reasoning.Trialectic369MultiplicityProjectionPositionIndependenceExact as Position

------------------------------------------------------------------------
-- 1. A source-side conjugacy/equivariance-shaped certificate.
------------------------------------------------------------------------

record OutputTranslationEquivariance
    (source : Action.ActualMonster3BActionRecognition) : Set₁ where
  field
    outputPositionTransport :
      Descent.ActualInertia source →
      H.Axis6 →
      H.X6 →
      H.X6

    transportedNormalizerActionOnTranslatedInput :
      (inertia : Descent.ActualInertia source) →
      (axis : H.Axis6) →
      (position : H.X6) →
      (multiplicity : Fin 90) →
      Descent.transportedActualProductAct source inertia
        (H.translate axis position , multiplicity)
      ≡
      ( outputPositionTransport inertia axis
          (proj₁
            (Descent.transportedActualProductAct
              source inertia (position , multiplicity)))
      , proj₂
          (Descent.transportedActualProductAct
            source inertia (position , multiplicity)) )

open OutputTranslationEquivariance public

------------------------------------------------------------------------
-- 2. Compile the existing generator-invariance owner, not a new action.
------------------------------------------------------------------------

generatorInvarianceFromOutputEquivariance :
  (source : Action.ActualMonster3BActionRecognition) →
  OutputTranslationEquivariance source →
  Position.MultiplicityGeneratorInvariant source
generatorInvarianceFromOutputEquivariance source equivariance =
  record
    { unitTranslationPreservesMultiplicityOutput =
        λ inertia axis position multiplicity →
          cong proj₂
            (transportedNormalizerActionOnTranslatedInput
              equivariance inertia axis position multiplicity)
    }

positionIndependenceFromOutputEquivariance :
  (source : Action.ActualMonster3BActionRecognition) →
  OutputTranslationEquivariance source →
  Position.MultiplicityPositionIndependence source
positionIndependenceFromOutputEquivariance source equivariance =
  Position.positionIndependenceFromGenerators source
    (generatorInvarianceFromOutputEquivariance source equivariance)

multiplicityDescentFromOutputEquivariance :
  (source : Action.ActualMonster3BActionRecognition) →
  OutputTranslationEquivariance source →
  Descent.MultiplicityProjectionDescent source
multiplicityDescentFromOutputEquivariance source equivariance =
  Position.descentFromGeneratorInvariance source
    (generatorInvarianceFromOutputEquivariance source equivariance)

compiledMultiplicityActIsZeroPositionEvaluation :
  (source : Action.ActualMonster3BActionRecognition) →
  (equivariance : OutputTranslationEquivariance source) →
  (inertia : Descent.ActualInertia source) →
  (multiplicity : Fin 90) →
  Descent.multiplicityAct
    (multiplicityDescentFromOutputEquivariance source equivariance)
    inertia multiplicity
  ≡ Position.canonicalMultiplicityAct source inertia multiplicity
compiledMultiplicityActIsZeroPositionEvaluation
  source equivariance inertia multiplicity = refl

------------------------------------------------------------------------
-- 3. The outgoing 10 x 9 carrier/action is now a compiler consequence.
------------------------------------------------------------------------

compiledTenByNineFromOutputEquivariance :
  (source : Action.ActualMonster3BActionRecognition) →
  OutputTranslationEquivariance source →
  Descent.ActualInertia source →
  Descent.TenByNineSurface →
  Descent.TenByNineSurface
compiledTenByNineFromOutputEquivariance source equivariance =
  Descent.compiledTenByNineAct
    source
    (multiplicityDescentFromOutputEquivariance source equivariance)

------------------------------------------------------------------------
-- 4. Explicit authority boundary.
------------------------------------------------------------------------

record TranslationDescentBoundary : Set where
  constructor translation-descent-boundary
  field
    existingSixGeneratorCriterionReused : Bool
    normalizerMayMoveOutputPosition : Bool
    translationEquivarianceCompilesPositionIndependence : Bool
    translationEquivarianceCompilesMultiplicityDescent : Bool
    resultingActionUsesCanonicalZeroPositionEvaluation : Bool
    tenByNineCompilerReused : Bool
    actualMonsterTranslationEquivarianceInhabitedHere : Bool
    linearSuzukiMultiplicitiesIdentifiedWithFin90Here : Bool

canonicalTranslationDescentBoundary : TranslationDescentBoundary
canonicalTranslationDescentBoundary =
  translation-descent-boundary
    true true true true true true false false
