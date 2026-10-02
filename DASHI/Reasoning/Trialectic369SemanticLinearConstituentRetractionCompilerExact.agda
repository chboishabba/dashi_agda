module DASHI.Reasoning.Trialectic369SemanticLinearConstituentRetractionCompilerExact where

------------------------------------------------------------------------
-- SEMANTIC 196883 COORDINATES -> LINEAR CONSTITUENT BASIS FRAME
--
-- WRONGTYPE CORRECTION
--
-- SemanticMonsterConstituent196883 is a finite 196883-coordinate / basis-label
-- carrier.  Linear.Vector constituentLinearCarrier is the FULL carrier of a
-- 196883-dimensional vector space.  These are not the same type of object:
-- dimension 196883 does not mean the vector carrier has 196883 elements.
--
-- Therefore the correct bridge is a basis/frame interface:
--
--   semantic coordinate -> linear constituent vector
--
-- together with independence/completeness receipts supplied at the linear
-- representation level.
--
-- Such a basis frame may help CONSTRUCT a projection/retraction, but it does
-- not itself manufacture the direct-summand projection.  The actual
-- ConstituentRetraction remains a separate linear source payment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Nested
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as Retraction

------------------------------------------------------------------------
-- 1. Correct semantic-coordinate / linear-basis interface.
------------------------------------------------------------------------

record SemanticLinearConstituentBasisFrame
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    basisVector :
      Nested.SemanticMonsterConstituent196883 →
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))

    basisInjective :
      ∀ {left right : Nested.SemanticMonsterConstituent196883} →
      basisVector left ≡ basisVector right →
      left ≡ right

    -- Deliberately proof-bearing but abstract: the minimal HilbertLift API does
    -- not carry finite sums / coefficients / basis expansion primitives.
    basisLinearlyIndependent : Set
    basisSpansConstituent : Set

open SemanticLinearConstituentBasisFrame public

------------------------------------------------------------------------
-- 2. A basis frame is NOT a carrier equivalence.
------------------------------------------------------------------------

data SemanticCoordinateCarrierEqualsLinearVectorCarrier : Set where
data Dimension196883MeansExactly196883Vectors : Set where
data BasisFrameCreatesDirectSummandProjection : Set where
data CoordinateRetractionCreatesLinearRetraction : Set where

semanticCoordinatesDoNotEqualAllVectors :
  SemanticCoordinateCarrierEqualsLinearVectorCarrier → ⊥
semanticCoordinatesDoNotEqualAllVectors ()

dimensionDoesNotFixVectorCarrierCardinality :
  Dimension196883MeansExactly196883Vectors → ⊥
dimensionDoesNotFixVectorCarrierCardinality ()

basisFrameDoesNotCreateProjection :
  BasisFrameCreatesDirectSummandProjection → ⊥
basisFrameDoesNotCreateProjection ()

coordinateRetractionDoesNotCreateLinearRetraction :
  CoordinateRetractionCreatesLinearRetraction → ⊥
coordinateRetractionDoesNotCreateLinearRetraction ()

------------------------------------------------------------------------
-- 3. Correct downstream target remains the genuine linear retraction.
------------------------------------------------------------------------

record BasisFramePlusLinearRetraction
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    basisFrame : SemanticLinearConstituentBasisFrame core
    linearRetraction : Retraction.ConstituentRetraction core

open BasisFramePlusLinearRetraction public

------------------------------------------------------------------------
-- 4. Machine-readable corrected frontier.
------------------------------------------------------------------------

record Trialectic369SemanticLinearRetractionCompilerBoundary : Set where
  constructor trialectic-369-semantic-linear-retraction-compiler-boundary
  field
    semanticCarrierIsFiniteCoordinateCarrier : Bool
    linearConstituentIsVectorCarrier : Bool
    semanticLinearCarrierEqualityRejected : Bool
    basisFrameIsCorrectBridgeType : Bool
    basisIndependenceAndSpanningRequired : Bool
    basisFrameAloneCompilesRetraction : Bool
    actualSemanticLinearBasisFrameInhabitedHere : Bool
    actualLinearRetractionInhabitedHere : Bool
    coordinateRetractionPaysLinearRetraction : Bool

canonicalTrialectic369SemanticLinearRetractionCompilerBoundary :
  Trialectic369SemanticLinearRetractionCompilerBoundary
canonicalTrialectic369SemanticLinearRetractionCompilerBoundary =
  trialectic-369-semantic-linear-retraction-compiler-boundary
    true true true true true
    false false false false
