module DASHI.Physics.Chemistry.AmmoniaMonster3BRefinedStateLiftCompilerExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3

------------------------------------------------------------------------
-- MINIMAL REFINEMENT OF THE EXACT C3 QUOTIENT
--
-- The non-factorability owner proves that phase alone cannot recover either
-- fine Monster-zeta coordinate.  The existing model says exactly what is
-- missing: one F3^6 Heisenberg/Base369 weight and one Fin 90 multiplicity.
-- This module proves that those two coordinates are sufficient on the model
-- side, then compiles them through any already-paid ActualZetaSectorRecognition.
--
-- No physical meaning for an NH3 -> F3^6 or NH3 -> Fin90 assignment is invented.
------------------------------------------------------------------------

ModelBasis : Set
ModelBasis = Model.ZetaModelBasis

record ZetaRefinedCoordinate : Set where
  constructor zetaRefinedCoordinate
  field
    weight : H.X6
    multiplicity : Fin 90

open ZetaRefinedCoordinate public

refinedToModel : ZetaRefinedCoordinate → ModelBasis
refinedToModel c = Model.zetaBasis (weight c) (multiplicity c)

modelToRefined : ModelBasis → ZetaRefinedCoordinate
modelToRefined b =
  zetaRefinedCoordinate (Model.weightPosition b) (Model.multiplicityCoordinate b)

refinedModelRoundTrip :
  (c : ZetaRefinedCoordinate) → modelToRefined (refinedToModel c) ≡ c
refinedModelRoundTrip (zetaRefinedCoordinate w m) = refl

modelRefinedRoundTrip :
  (b : ModelBasis) → refinedToModel (modelToRefined b) ≡ b
modelRefinedRoundTrip (Model.zetaBasis w m) = refl

------------------------------------------------------------------------
-- An NH3 refinement input.  `allZeta` deliberately scopes this compiler to a
-- selected NH3 zeta-sector carrier; invariant and zeta^2 states use their own
-- phase fibres rather than being silently coerced into W_zeta.
------------------------------------------------------------------------

record NH3ZetaRefinement : Set₁ where
  constructor nh3ZetaRefinement
  field
    State : Set
    phaseOf : State → NH3.ElectronicC3Phase
    allZeta : (s : State) → phaseOf s ≡ NH3.zeta
    base369Weight : State → H.X6
    multiplicityCoordinate : State → Fin 90
    physicalWeightIdentification : Set
    physicalMultiplicityIdentification : Set

open NH3ZetaRefinement public

toRefinedCoordinate :
  (r : NH3ZetaRefinement) → State r → ZetaRefinedCoordinate
toRefinedCoordinate r s =
  zetaRefinedCoordinate (base369Weight r s) (multiplicityCoordinate r s)

toModelState :
  (r : NH3ZetaRefinement) → State r → ModelBasis
toModelState r s = refinedToModel (toRefinedCoordinate r s)

modelWeightRecoversAssignedWeight :
  (r : NH3ZetaRefinement) → (s : State r) →
  Model.weightPosition (toModelState r s) ≡ base369Weight r s
modelWeightRecoversAssignedWeight r s = refl

modelMultiplicityRecoversAssignedMultiplicity :
  (r : NH3ZetaRefinement) → (s : State r) →
  Model.multiplicityCoordinate (toModelState r s)
  ≡ multiplicityCoordinate r s
modelMultiplicityRecoversAssignedMultiplicity r s = refl

------------------------------------------------------------------------
-- Existing Base369 chart: once refined, the same model point has an exact
-- Base369 multiplicity coordinate representation.
------------------------------------------------------------------------

toBase369Coordinate :
  (r : NH3ZetaRefinement) → State r → Base369.Base369MultiplicityBasis
toBase369Coordinate r s = Base369.modelToBase369 (toModelState r s)

base369CoordinateReturnsSameModel :
  (r : NH3ZetaRefinement) → (s : State r) →
  Base369.base369ToModel (toBase369Coordinate r s) ≡ toModelState r s
base369CoordinateReturnsSameModel r s =
  Base369.modelBase369RoundTrip (toModelState r s)

------------------------------------------------------------------------
-- Conditional literal-sector compiler.
--
-- This is stronger than a phase map but still correctly conditional on an
-- ActualZetaSectorRecognition.  If recognition is supplied, `fromModel` turns
-- the refined chemistry coordinate into a state of that literal recognized
-- sector, and `toModel` recovers the exact selected model point.
------------------------------------------------------------------------

toActualZetaState :
  ∀ {ActualSector : Set} →
  Actual.ActualZetaSectorRecognition ActualSector →
  (r : NH3ZetaRefinement) →
  State r → ActualSector
toActualZetaState recognition r s =
  Actual.fromModel recognition (toModelState r s)

actualLiftRecoversModelCoordinate :
  ∀ {ActualSector : Set}
    (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
    (r : NH3ZetaRefinement) →
    (s : State r) →
  Actual.toModel recognition (toActualZetaState recognition r s)
  ≡ toModelState r s
actualLiftRecoversModelCoordinate recognition r s =
  Actual.toAfterFrom recognition (toModelState r s)

actualLiftRecoversBase369Coordinate :
  ∀ {ActualSector : Set}
    (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
    (r : NH3ZetaRefinement) →
    (s : State r) →
  Base369.toBase369 (Base369.composeActualRecognitionWithBase369 recognition)
    (toActualZetaState recognition r s)
  ≡ toBase369Coordinate r s
actualLiftRecoversBase369Coordinate recognition r s =
  cong Base369.modelToBase369
    (actualLiftRecoversModelCoordinate recognition r s)

------------------------------------------------------------------------
-- Consumer contract: this is now a compiler problem, not a dimension guess.
------------------------------------------------------------------------

record RefinedStateLiftBoundary : Set where
  constructor refinedStateLiftBoundary
  field
    exactModelRefinementRoundTripPaid : Bool
    exactModelRefinementRoundTripPaidIsTrue :
      exactModelRefinementRoundTripPaid ≡ true
    base369CoordinateCompilerPaid : Bool
    base369CoordinateCompilerPaidIsTrue : base369CoordinateCompilerPaid ≡ true
    refinedCoordinateToMonsterModelCompilerPaid : Bool
    refinedCoordinateToMonsterModelCompilerPaidIsTrue :
      refinedCoordinateToMonsterModelCompilerPaid ≡ true
    actualRecognitionLiftCompilerPaid : Bool
    actualRecognitionLiftCompilerPaidIsTrue :
      actualRecognitionLiftCompilerPaid ≡ true
    physicalNH3Base369WeightIdentificationPaid : Bool
    physicalNH3Base369WeightIdentificationPaidIsFalse :
      physicalNH3Base369WeightIdentificationPaid ≡ false
    physicalNH3MultiplicityIdentificationPaid : Bool
    physicalNH3MultiplicityIdentificationPaidIsFalse :
      physicalNH3MultiplicityIdentificationPaid ≡ false
    literalActualMonsterStateLiftInhabitedHere : Bool
    literalActualMonsterStateLiftInhabitedHereIsFalse :
      literalActualMonsterStateLiftInhabitedHere ≡ false
    dimensionOrPhaseAloneCreatesRefinement : Bool
    dimensionOrPhaseAloneCreatesRefinementIsFalse :
      dimensionOrPhaseAloneCreatesRefinement ≡ false
    nextPayment : String

open RefinedStateLiftBoundary public

canonicalRefinedStateLiftBoundary : RefinedStateLiftBoundary
canonicalRefinedStateLiftBoundary =
  refinedStateLiftBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "identify physically meaningful NH3-state -> F3^6/Base369 weight and NH3-state -> Fin90 multiplicity maps on a selected zeta-sector carrier, then attach an actual recognized Monster zeta sector and prove any additional action equivariance required by the downstream physical consumer"
