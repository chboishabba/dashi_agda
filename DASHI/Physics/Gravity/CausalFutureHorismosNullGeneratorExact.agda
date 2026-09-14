module DASHI.Physics.Gravity.CausalFutureHorismosNullGeneratorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact as Focusing

------------------------------------------------------------------------
-- Thin causal-boundary carrier for the Penrose proof architecture.
--
-- This records the standard continuum objects and composition rules but does
-- not reprove Lorentzian causality in Agda.
------------------------------------------------------------------------

record CausalFutureHorismosBoundary : Set where
  field
    chronologicalFutureIPlus : String
    causalFutureJPlus : String
    futureHorismosEPlus : String

    horismosEqualsCausalMinusChronologicalFuture : Bool
    horismosEqualsCausalMinusChronologicalFutureIsTrue :
      horismosEqualsCausalMinusChronologicalFuture ≡ true

    futureHorismosIsAchronalBoundary : Bool
    futureHorismosIsAchronalBoundaryIsTrue :
      futureHorismosIsAchronalBoundary ≡ true

    futureHorismosGeneratedByNullGeodesics : Bool
    futureHorismosGeneratedByNullGeodesicsIsTrue :
      futureHorismosGeneratedByNullGeodesics ≡ true

    conjugatePointForcesGeneratorIntoChronologicalFuture : Bool
    conjugatePointForcesGeneratorIntoChronologicalFutureIsTrue :
      conjugatePointForcesGeneratorIntoChronologicalFuture ≡ true

    generatorAfterConjugatePointLeavesHorismos : Bool
    generatorAfterConjugatePointLeavesHorismosIsTrue :
      generatorAfterConjugatePointLeavesHorismos ≡ true

    causalBoundaryOwnerInternallyReprovesContinuumCausality : Bool
    causalBoundaryOwnerInternallyReprovesContinuumCausalityIsFalse :
      causalBoundaryOwnerInternallyReprovesContinuumCausality ≡ false

open CausalFutureHorismosBoundary public

canonicalCausalFutureHorismosBoundary : CausalFutureHorismosBoundary
canonicalCausalFutureHorismosBoundary = record
  { chronologicalFutureIPlus =
      "I+(S): events reachable from S by future-directed timelike curves"
  ; causalFutureJPlus =
      "J+(S): events reachable from S by future-directed causal curves"
  ; futureHorismosEPlus =
      "E+(S) = J+(S) minus I+(S), the future horismos / causal boundary of S under the declared continuum hypotheses"
  ; horismosEqualsCausalMinusChronologicalFuture = true
  ; horismosEqualsCausalMinusChronologicalFutureIsTrue = refl
  ; futureHorismosIsAchronalBoundary = true
  ; futureHorismosIsAchronalBoundaryIsTrue = refl
  ; futureHorismosGeneratedByNullGeodesics = true
  ; futureHorismosGeneratedByNullGeodesicsIsTrue = refl
  ; conjugatePointForcesGeneratorIntoChronologicalFuture = true
  ; conjugatePointForcesGeneratorIntoChronologicalFutureIsTrue = refl
  ; generatorAfterConjugatePointLeavesHorismos = true
  ; generatorAfterConjugatePointLeavesHorismosIsTrue = refl
  ; causalBoundaryOwnerInternallyReprovesContinuumCausality = false
  ; causalBoundaryOwnerInternallyReprovesContinuumCausalityIsFalse = refl
  }

record CausalFutureInterpretationBoundary : Set where
  field
    causalFutureIsNotChronologicalFuture : Bool
    causalFutureIsNotChronologicalFutureIsTrue :
      causalFutureIsNotChronologicalFuture ≡ true
    horismosIsNotEventHorizon : Bool
    horismosIsNotEventHorizonIsTrue :
      horismosIsNotEventHorizon ≡ true
    nullGeneratorIsNotArbitraryNullCurve : Bool
    nullGeneratorIsNotArbitraryNullCurveIsTrue :
      nullGeneratorIsNotArbitraryNullCurve ≡ true
    conjugatePointDoesNotMeanGeodesicTerminates : Bool
    conjugatePointDoesNotMeanGeodesicTerminatesIsTrue :
      conjugatePointDoesNotMeanGeodesicTerminates ≡ true

open CausalFutureInterpretationBoundary public

canonicalCausalFutureInterpretationBoundary : CausalFutureInterpretationBoundary
canonicalCausalFutureInterpretationBoundary = record
  { causalFutureIsNotChronologicalFuture = true
  ; causalFutureIsNotChronologicalFutureIsTrue = refl
  ; horismosIsNotEventHorizon = true
  ; horismosIsNotEventHorizonIsTrue = refl
  ; nullGeneratorIsNotArbitraryNullCurve = true
  ; nullGeneratorIsNotArbitraryNullCurveIsTrue = refl
  ; conjugatePointDoesNotMeanGeodesicTerminates = true
  ; conjugatePointDoesNotMeanGeodesicTerminatesIsTrue = refl
  }

focusingConsumer : Set
focusingConsumer = Focusing.NullOpticalFocusingBoundary
