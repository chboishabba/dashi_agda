module DASHI.Culture.KimmererNarrativeMetaphorCalibrationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorSourceRegistryExact as Sources

------------------------------------------------------------------------
-- KIMMERER NARRATIVE / METAPHOR CALIBRATION BOUNDARY
--
-- This is an interpretive DASHI bridge, not a claim that Braiding Sweetgrass
-- contains a formal learning algorithm.  The finite witness captures only the
-- following methodological reading:
--
--   repeated situated stories can teach a reader which features of the braid
--   frame are salient for the book's relational interpretation, so that
--   'braid' later functions as a compact representation carrying more than
--   mere multiplicity.
--
-- The source is Robin Wall Kimmerer, Braiding Sweetgrass (2013), ISBN
-- 9781571313560.  No braid-group, factorisation, cognitive-neuroscience, or
-- quantitative learning theorem is attributed to Kimmerer.
------------------------------------------------------------------------

data BraidFeature : Set where
  multipleStrands retainedDifference reciprocity heldTension relationalCoherence
  : BraidFeature

data CalibrationStage : Set where
  initialBraidFrame relationallyCalibratedBraidFrame : CalibrationStage

data Salience : Set where
  backgroundFeature salientFeature : Salience

featureSalience : CalibrationStage → BraidFeature → Salience
featureSalience initialBraidFrame multipleStrands = salientFeature
featureSalience initialBraidFrame retainedDifference = backgroundFeature
featureSalience initialBraidFrame reciprocity = backgroundFeature
featureSalience initialBraidFrame heldTension = backgroundFeature
featureSalience initialBraidFrame relationalCoherence = backgroundFeature
featureSalience relationallyCalibratedBraidFrame multipleStrands = salientFeature
featureSalience relationallyCalibratedBraidFrame retainedDifference = salientFeature
featureSalience relationallyCalibratedBraidFrame reciprocity = salientFeature
featureSalience relationallyCalibratedBraidFrame heldTension = salientFeature
featureSalience relationallyCalibratedBraidFrame relationalCoherence = salientFeature

reciprocityBecomesSalient :
  featureSalience relationallyCalibratedBraidFrame reciprocity ≡ salientFeature
reciprocityBecomesSalient = refl

heldTensionBecomesSalient :
  featureSalience relationallyCalibratedBraidFrame heldTension ≡ salientFeature
heldTensionBecomesSalient = refl

------------------------------------------------------------------------
-- Calibration gains discrimination.
--
-- The initial coarse frame sees only 'more than one strand'.  The calibrated
-- frame can distinguish a merely juxtaposed collection from a reciprocal,
-- tension-held relation.  This is a finite observer-refinement witness only;
-- it is not asserted as a psychological measurement model of readers.
------------------------------------------------------------------------

data ToyBraidSituation : Set where
  merelyJuxtaposed reciprocallyHeld : ToyBraidSituation

data InitialBraidReading : Set where
  severalStrands : InitialBraidReading

data CalibratedBraidReading : Set where
  juxtapositionReading reciprocalTensionReading : CalibratedBraidReading

initialReading : ToyBraidSituation → InitialBraidReading
initialReading _ = severalStrands

calibratedReading : ToyBraidSituation → CalibratedBraidReading
calibratedReading merelyJuxtaposed = juxtapositionReading
calibratedReading reciprocallyHeld = reciprocalTensionReading

calibratedMeaningDoesNotDescendThroughInitialReading :
  NonFactor.FactorsThrough initialReading calibratedReading → ⊥
calibratedMeaningDoesNotDescendThroughInitialReading =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      merelyJuxtaposed
      reciprocallyHeld
      refl
      (λ ()))

------------------------------------------------------------------------
-- Interpretive reading and source boundary.
------------------------------------------------------------------------

kimmererSource : Sources.SourceReference
kimmererSource = Sources.kimmerer2013

narrativeCalibrationReading : String
narrativeCalibrationReading =
  "DASHI interpretation: the surrounding stories can calibrate which relational features of the braid frame the reader should carry forward, allowing the braid to become a compact reusable representation rather than a bare picture of several strands."

record KimmererNarrativeCalibrationBoundary : Set where
  constructor kimmererNarrativeCalibrationBoundary
  field
    storiesAreLiteralMachineLearningTrainingData : Bool
    storiesAreLiteralMachineLearningTrainingDataIsFalse :
      storiesAreLiteralMachineLearningTrainingData ≡ false

    kimmererStatesFormalFeatureSalienceFunction : Bool
    kimmererStatesFormalFeatureSalienceFunctionIsFalse :
      kimmererStatesFormalFeatureSalienceFunction ≡ false

    kimmererProvesObserverRefinement : Bool
    kimmererProvesObserverRefinementIsFalse :
      kimmererProvesObserverRefinement ≡ false

    braidMeansAllSourcePredicatesTransfer : Bool
    braidMeansAllSourcePredicatesTransferIsFalse :
      braidMeansAllSourcePredicatesTransfer ≡ false

    dashiCalibrationModelIsInterpretiveExtension : Bool
    dashiCalibrationModelIsInterpretiveExtensionIsTrue :
      dashiCalibrationModelIsInterpretiveExtension ≡ true

canonicalKimmererNarrativeCalibrationBoundary :
  KimmererNarrativeCalibrationBoundary
canonicalKimmererNarrativeCalibrationBoundary =
  kimmererNarrativeCalibrationBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
