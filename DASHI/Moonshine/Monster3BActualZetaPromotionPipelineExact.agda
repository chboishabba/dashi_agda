module DASHI.Moonshine.Monster3BActualZetaPromotionPipelineExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- State the exact minimal promotion pipeline left by Rounds 3--4.  A chosen
-- zeta eigensector must first be separated from the fused normalizer carrier;
-- that sector must then be recognized as the concrete 729 x 90 Weyl model.
-- From these two proof-bearing inputs the inertia subgroup acts internally on
-- the chosen sector and the complete model projector/Weyl structure becomes
-- available without any additional compatibility premises.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

------------------------------------------------------------------------
-- Combined actual-sector promotion object.
------------------------------------------------------------------------

record ActualZetaPromotionPipeline : Set₁ where
  field
    phaseResolved : Inertia.ActualMonster3BPhaseResolvedSector

  open Inertia.ActualMonster3BPhaseResolvedSector phaseResolved public

  field
    modelRecognition :
      Multiplicity.ActualZetaSectorRecognition chosenZetaSector

open ActualZetaPromotionPipeline public

------------------------------------------------------------------------
-- The inertia action on the sigma eigenspace transports to the chosen actual
-- sector through the supplied two-sided phase-resolution equivalence.
------------------------------------------------------------------------

chosenInertiaAction :
  (pipeline : ActualZetaPromotionPipeline) →
  Inertia.CentralInertia
    (normalizerAction pipeline) →
  chosenZetaSector pipeline →
  chosenZetaSector pipeline
chosenInertiaAction pipeline inertia state =
  recoverChosenZeta pipeline
    (Inertia.inertiaPreservesZetaSector
      (normalizerAction pipeline)
      inertia
      (includeChosenZeta pipeline state))

chosenInertiaActionAgreesAfterInclusion :
  (pipeline : ActualZetaPromotionPipeline) →
  (inertia : Inertia.CentralInertia (normalizerAction pipeline)) →
  (state : chosenZetaSector pipeline) →
  includeChosenZeta pipeline (chosenInertiaAction pipeline inertia state)
  ≡ Inertia.inertiaPreservesZetaSector
      (normalizerAction pipeline)
      inertia
      (includeChosenZeta pipeline state)
chosenInertiaActionAgreesAfterInclusion pipeline inertia state =
  includeAfterRecover pipeline
    (Inertia.inertiaPreservesZetaSector
      (normalizerAction pipeline)
      inertia
      (includeChosenZeta pipeline state))

------------------------------------------------------------------------
-- All existing model-derived structure is now available on the phase-resolved
-- sector from the one recognition object.
------------------------------------------------------------------------

chosenWeightPosition :
  (pipeline : ActualZetaPromotionPipeline) →
  chosenZetaSector pipeline → H.X6
chosenWeightPosition pipeline =
  Multiplicity.actualWeightPosition (modelRecognition pipeline)

chosenMultiplicityCoordinate :
  (pipeline : ActualZetaPromotionPipeline) →
  chosenZetaSector pipeline → Agda.Builtin.Nat.Nat
chosenMultiplicityCoordinate pipeline state =
  Agda.Builtin.Fin.toℕ
    (Multiplicity.actualMultiplicityCoordinate
      (modelRecognition pipeline) state)

chosenOwnWeightProjectorCoefficient :
  (pipeline : ActualZetaPromotionPipeline) →
  (state : chosenZetaSector pipeline) →
  Multiplicity.actualWeightProjectorCoefficient
    (modelRecognition pipeline)
    (chosenWeightPosition pipeline state)
    state
  ≡ 1
chosenOwnWeightProjectorCoefficient pipeline =
  Multiplicity.actualOwnWeightProjectorCoefficient
    (modelRecognition pipeline)

chosenWeylExponent :
  (pipeline : ActualZetaPromotionPipeline) →
  (dual translationAxis : H.Axis6) →
  (state : chosenZetaSector pipeline) →
  Multiplicity.actualModulationExponent
    (modelRecognition pipeline)
    dual
    (Multiplicity.actualTranslate
      (modelRecognition pipeline)
      translationAxis state)
  ≡ H._+3_
      (H.kronecker dual translationAxis)
      (Multiplicity.actualModulationExponent
        (modelRecognition pipeline) dual state)
chosenWeylExponent pipeline =
  Multiplicity.actualGeneratorWeylExponent
    (modelRecognition pipeline)

------------------------------------------------------------------------
-- The remaining actual input is isolated in one record.
------------------------------------------------------------------------

record ActualZetaPromotionBoundary : Set where
  constructor actual-zeta-promotion-boundary
  field
    inertiaActionDerivableFromPipeline : Bool
    inertiaActionDerivableFromPipelineIsTrue :
      inertiaActionDerivableFromPipeline ≡ true
    fullWeylSurfaceDerivableFromPipeline : Bool
    fullWeylSurfaceDerivableFromPipelineIsTrue :
      fullWeylSurfaceDerivableFromPipeline ≡ true
    actualPipelineInhabited : Bool
    actualPipelineInhabitedIsFalse : actualPipelineInhabited ≡ false
    actualMultiplicityCharacterComputed : Bool
    actualMultiplicityCharacterComputedIsFalse :
      actualMultiplicityCharacterComputed ≡ false

canonicalActualZetaPromotionBoundary : ActualZetaPromotionBoundary
canonicalActualZetaPromotionBoundary =
  actual-zeta-promotion-boundary true refl true refl false refl false refl
