module DASHI.Physics.Chemistry.AmmoniaMonster3BRefinedStateLiftCompilerExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as Basis
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3

------------------------------------------------------------------------
-- MINIMAL REFINEMENT OF THE EXACT C3 QUOTIENT
--
-- Phase alone cannot recover a finite Monster-zeta basis label.  The finite
-- model says exactly what is missing: one F3^6/Base369 weight and one Fin90
-- multiplicity coordinate.  Those coordinates reconstruct a MODEL BASIS LABEL.
--
-- Correct representation-native promotion then uses an
-- `ActualZetaBasisRecognition` to identify that model coordinate with an
-- actual basis label included in the literal linear W_zeta carrier.  No finite
-- coordinate is promoted to an arbitrary W_zeta vector.
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

record NH3ZetaRefinement : Set₁ where
  constructor nh3ZetaRefinement
  field
    State : Set
    phaseOf : State → NH3.ElectronicC3Phase
    allZeta : (s : State) → phaseOf s ≡ NH3.zeta
    base369Weight : State → H.X6
    multiplicityCoordinate : State → Fin 90
    PhysicalWeightIdentification : Set
    physicalWeightIdentificationWitness : PhysicalWeightIdentification
    PhysicalMultiplicityIdentification : Set
    physicalMultiplicityIdentificationWitness : PhysicalMultiplicityIdentification
open NH3ZetaRefinement public

toRefinedCoordinate :
  (r : NH3ZetaRefinement) → State r → ZetaRefinedCoordinate
toRefinedCoordinate r s =
  zetaRefinedCoordinate (base369Weight r s) (multiplicityCoordinate r s)

toModelBasis :
  (r : NH3ZetaRefinement) → State r → ModelBasis
toModelBasis r s = refinedToModel (toRefinedCoordinate r s)

modelWeightRecoversAssignedWeight :
  (r : NH3ZetaRefinement) → (s : State r) →
  Model.weightPosition (toModelBasis r s) ≡ base369Weight r s
modelWeightRecoversAssignedWeight r s = refl

modelMultiplicityRecoversAssignedMultiplicity :
  (r : NH3ZetaRefinement) → (s : State r) →
  Model.multiplicityCoordinate (toModelBasis r s)
  ≡ multiplicityCoordinate r s
modelMultiplicityRecoversAssignedMultiplicity r s = refl

toBase369Coordinate :
  (r : NH3ZetaRefinement) → State r → Base369.Base369MultiplicityBasis
toBase369Coordinate r s = Base369.modelToBase369 (toModelBasis r s)

base369CoordinateReturnsSameModel :
  (r : NH3ZetaRefinement) → (s : State r) →
  Base369.base369ToModel (toBase369Coordinate r s) ≡ toModelBasis r s
base369CoordinateReturnsSameModel r s =
  Base369.modelBase369RoundTrip (toModelBasis r s)

------------------------------------------------------------------------
-- Representation-native basis compiler.
------------------------------------------------------------------------

toActualZetaBasisLabel :
  ∀ {LiteralZetaSector : Set} →
  (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
  (r : NH3ZetaRefinement) →
  State r → Basis.ActualBasisLabel recognition
toActualZetaBasisLabel recognition r s =
  Basis.fromModelBasis recognition (toModelBasis r s)

actualBasisLiftRecoversModelCoordinate :
  ∀ {LiteralZetaSector : Set}
    (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
    (r : NH3ZetaRefinement) →
    (s : State r) →
  Basis.toModelBasis recognition (toActualZetaBasisLabel recognition r s)
  ≡ toModelBasis r s
actualBasisLiftRecoversModelCoordinate recognition r s =
  Basis.toAfterFrom recognition (toModelBasis r s)

includedActualZetaBasisVector :
  ∀ {LiteralZetaSector : Set} →
  (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
  (r : NH3ZetaRefinement) →
  State r → LiteralZetaSector
includedActualZetaBasisVector recognition r s =
  Basis.includeBasis recognition (toActualZetaBasisLabel recognition r s)

------------------------------------------------------------------------
-- Wrong-type firewalls.
------------------------------------------------------------------------

data BasisLabelCompilerCreatesArbitraryWZetaState : Set where
data PhaseOrDimensionCreatesPhysicalRefinement : Set where

basisLabelCompilerDoesNotCreateArbitraryWZetaState :
  BasisLabelCompilerCreatesArbitraryWZetaState → ⊥
basisLabelCompilerDoesNotCreateArbitraryWZetaState ()

phaseOrDimensionDoesNotCreatePhysicalRefinement :
  PhaseOrDimensionCreatesPhysicalRefinement → ⊥
phaseOrDimensionDoesNotCreatePhysicalRefinement ()

record RefinedStateLiftBoundary : Set where
  constructor refinedStateLiftBoundary
  field
    exactModelRefinementRoundTripPaid : Bool
    exactModelRefinementRoundTripPaidIsTrue :
      exactModelRefinementRoundTripPaid ≡ true
    base369CoordinateCompilerPaid : Bool
    base369CoordinateCompilerPaidIsTrue : base369CoordinateCompilerPaid ≡ true
    refinedCoordinateToMonsterModelBasisCompilerPaid : Bool
    refinedCoordinateToMonsterModelBasisCompilerPaidIsTrue :
      refinedCoordinateToMonsterModelBasisCompilerPaid ≡ true
    actualBasisRecognitionLiftCompilerPaid : Bool
    actualBasisRecognitionLiftCompilerPaidIsTrue :
      actualBasisRecognitionLiftCompilerPaid ≡ true
    wholeLiteralSectorFiniteLiftCompilerPaid : Bool
    wholeLiteralSectorFiniteLiftCompilerPaidIsFalse :
      wholeLiteralSectorFiniteLiftCompilerPaid ≡ false
    physicalNH3Base369WeightIdentificationPaid : Bool
    physicalNH3Base369WeightIdentificationPaidIsFalse :
      physicalNH3Base369WeightIdentificationPaid ≡ false
    physicalNH3MultiplicityIdentificationPaid : Bool
    physicalNH3MultiplicityIdentificationPaidIsFalse :
      physicalNH3MultiplicityIdentificationPaid ≡ false
    literalMonsterBasisAttachmentInhabitedHere : Bool
    literalMonsterBasisAttachmentInhabitedHereIsFalse :
      literalMonsterBasisAttachmentInhabitedHere ≡ false
    linearWZetaSameObjectRecognitionPaidHere : Bool
    linearWZetaSameObjectRecognitionPaidHereIsFalse :
      linearWZetaSameObjectRecognitionPaidHere ≡ false
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
    false refl
    false refl
    "supply source-backed NH3-state -> F3^6/Base369 weight and NH3-state -> Fin90 multiplicity assignments, then an actual proof-relevant Monster zeta BASIS recognition and action equivariance. Promotion from included basis vectors to the full linear W_zeta state space additionally requires the independent H_zeta x S_zeta <-> W_zeta same-object representation route."
