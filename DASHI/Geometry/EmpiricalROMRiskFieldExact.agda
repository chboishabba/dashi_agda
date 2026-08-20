module DASHI.Geometry.EmpiricalROMRiskFieldExact where

------------------------------------------------------------------------
-- FINITE EMPIRICAL ROM RISK FIELDS
--
-- The supplied ROM note explicitly corrects an earlier overreach: the current
-- formal layer should begin with a finite sampled pose family, not invent a
-- probability measure over motion.  AdaptiveWearableCompilerExact already owns
-- exact max and total fields.  This module adds finite exceedance counts and an
-- optional weighted empirical layer whose interpretation is carried by an
-- explicit weight-authority witness.
--
-- Garment-motion calibration:
-- Katja Wolff, Philipp Herholz, Verena Ziegler, Frauke Link, Nico Bruegel,
-- Olga Sorkine-Hornung, "Designing Personalized Garments with Body Movement",
-- Computer Graphics Forum 42(1), 2023. DOI: 10.1111/cgf.14728.
--
-- No CVaR, probability measure, or population-frequency semantics are asserted
-- by this file.  Those require a separately justified weighting model.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.AdaptiveWearableCompilerExact as Wearable

------------------------------------------------------------------------
-- Generic finite count over sampled poses.  The caller supplies the exact
-- threshold predicate so the theorem layer does not force floating-point order.
------------------------------------------------------------------------

countWhere :
  ∀ {Pose Site : Set} →
  (Pose → Site → Bool) → List Pose → Site → Nat
countWhere predicate [] site = zero
countWhere predicate (pose ∷ rest) site with predicate pose site
... | false = countWhere predicate rest site
... | true = suc (countWhere predicate rest site)

romExceedanceCount :
  ∀ {Pose Site : Set} →
  Wearable.EmpiricalROMField Pose Site →
  (Pose → Site → Bool) →
  Site → Nat
romExceedanceCount field exceeds =
  countWhere exceeds (Wearable.poses field)

------------------------------------------------------------------------
-- Explicit empirical weighting.  A list of weights is not automatically a
-- probability distribution.  `WeightAuthority` records the external/domain
-- reason the weights may be interpreted for the declared consumer.
------------------------------------------------------------------------

record WeightedPose (Pose : Set) : Set where
  constructor weightedPose
  field
    pose : Pose
    weight : Nat

open WeightedPose public

record WeightAuthority : Set where
  constructor weightAuthority
  field
    weightingReference : String
    interpretation : String
    consumerScope : String
    normalizedOrPopulationMeaningJustified : Bool

open WeightAuthority public

weightedSumOver :
  ∀ {Pose Site : Set} →
  (Pose → Site → Nat) →
  List (WeightedPose Pose) →
  Site → Nat
weightedSumOver field [] site = zero
weightedSumOver field (sample ∷ rest) site =
  weight sample * field (pose sample) site
  + weightedSumOver field rest site

weightedIndicatorSum :
  ∀ {Pose Site : Set} →
  (Pose → Site → Bool) →
  List (WeightedPose Pose) →
  Site → Nat
weightedIndicatorSum predicate [] site = zero
weightedIndicatorSum predicate (sample ∷ rest) site with predicate (pose sample) site
... | false = weightedIndicatorSum predicate rest site
... | true = weight sample + weightedIndicatorSum predicate rest site

record WeightedEmpiricalROMField (Pose Site : Set) : Set₁ where
  constructor weightedEmpiricalROMField
  field
    samples : List (WeightedPose Pose)
    value : Pose → Site → Nat
    authority : WeightAuthority
    fieldName : String
    provenance : List String

open WeightedEmpiricalROMField public

weightedROMTotal :
  ∀ {Pose Site : Set} →
  WeightedEmpiricalROMField Pose Site → Site → Nat
weightedROMTotal field =
  weightedSumOver (value field) (samples field)

weightedROMExceedanceMass :
  ∀ {Pose Site : Set} →
  WeightedEmpiricalROMField Pose Site →
  (Pose → Site → Bool) →
  Site → Nat
weightedROMExceedanceMass field exceeds =
  weightedIndicatorSum exceeds (samples field)

------------------------------------------------------------------------
-- Exact boundary: weighted mass is available before probability semantics.
-- Normalization/division and tail-risk functionals belong in a later layer only
-- once the runtime supplies a justified scalar/probability model.
------------------------------------------------------------------------

record EmpiricalROMRiskBoundary : Set where
  constructor empiricalROMRiskBoundary
  field
    finiteMaxAndTotalNeedNoPoseProbability : Bool
    exceedanceCountNeedsOnlyFinitePoseSet : Bool
    weightedMassNeedsWeightAuthority : Bool
    probabilityRequiresNormalizedInterpretation : Bool
    cvarRequiresAdditionalTailRiskSemantics : Bool

canonicalEmpiricalROMRiskBoundary : EmpiricalROMRiskBoundary
canonicalEmpiricalROMRiskBoundary =
  empiricalROMRiskBoundary true true true true true
