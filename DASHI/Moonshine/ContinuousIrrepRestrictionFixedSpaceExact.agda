module DASHI.Moonshine.ContinuousIrrepRestrictionFixedSpaceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Introduce the generic producer lane requested by the Ogg/SSP reduction
-- programme:
--
--   ContinuousIrrep -> FiniteRestriction -> BranchingSpectrum
--                    -> FixedSpaceSpectrum.
--
-- The carrier is intentionally representation-agnostic.  A restriction must
-- provide its own multiplicity data and dimension conservation proof; a fixed
-- space must provide its own character-average/fixed-dimension witness.  This
-- file therefore does not encode the Ogg list, nonary addresses, S2/S3 labels,
-- or a preferred finite subgroup.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Continuous carrier.
------------------------------------------------------------------------

record ContinuousIrrep : Set₁ where
  field
    Label : Set
    label : Label
    dimension : Nat
    sourceGroup : String

open ContinuousIrrep public

------------------------------------------------------------------------
-- Finite restriction and irreducible branching data.
------------------------------------------------------------------------

record FiniteRestriction (ambient : ContinuousIrrep) : Set₁ where
  field
    FiniteIrrep : Set
    subgroupName : String
    irrepDimension : FiniteIrrep → Nat
    multiplicity : FiniteIrrep → Nat
    finiteIrreps : List FiniteIrrep
    branchingDimension : Nat
    branchingDimensionIsAmbient : branchingDimension ≡ dimension ambient

open FiniteRestriction public

record BranchingPiece
  {ambient : ContinuousIrrep}
  (restriction : FiniteRestriction ambient) : Set where
  constructor branchingPiece
  field
    finiteIrrep : FiniteIrrep restriction
    pieceDimension : Nat
    multiplicityValue : Nat
    pieceDimensionIsCorrect :
      pieceDimension ≡ irrepDimension restriction finiteIrrep
    multiplicityIsCorrect :
      multiplicityValue ≡ multiplicity restriction finiteIrrep

open BranchingPiece public

record BranchingSpectrum
  {ambient : ContinuousIrrep}
  (restriction : FiniteRestriction ambient) : Set₁ where
  field
    pieces : List (BranchingPiece restriction)
    totalDimension : Nat
    totalDimensionIsAmbient : totalDimension ≡ dimension ambient

open BranchingSpectrum public

------------------------------------------------------------------------
-- Fixed-space spectrum.
--
-- In ordinary finite-group character theory one has
--
--   dim V^H = (1 / |H|) * sum_{h in H} chi_V(h).
--
-- The generic layer records the resulting exact natural number and leaves the
-- actual character computation to a concrete producer.
------------------------------------------------------------------------

record FixedSpaceDatum : Set where
  constructor fixedSpaceDatum
  field
    stabilizerName : String
    stabilizerOrder : Nat
    fixedDimension : Nat

open FixedSpaceDatum public

record FixedSpaceSpectrum
  (ambient : ContinuousIrrep) : Set₁ where
  field
    fixedSpaces : List FixedSpaceDatum
    allFixedDimensionsBoundedByAmbient : Bool
    allFixedDimensionsBoundedByAmbientIsTrue :
      allFixedDimensionsBoundedByAmbient ≡ true

open FixedSpaceSpectrum public

------------------------------------------------------------------------
-- Complete producer package.
------------------------------------------------------------------------

record RepresentationReductionProducer : Set₁ where
  field
    ambient : ContinuousIrrep
    restriction : FiniteRestriction ambient
    branching : BranchingSpectrum restriction
    fixedSpaceSpectrum : FixedSpaceSpectrum ambient

open RepresentationReductionProducer public

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record RepresentationReductionBoundary : Set where
  constructor representationReductionBoundary
  field
    genericLaneConstructed : Bool
    genericLaneConstructedIsTrue : genericLaneConstructed ≡ true
    oggSetEncodedAsPremise : Bool
    oggSetEncodedAsPremiseIsFalse : oggSetEncodedAsPremise ≡ false
    nonaryAddressEncodedAsPremise : Bool
    nonaryAddressEncodedAsPremiseIsFalse :
      nonaryAddressEncodedAsPremise ≡ false
    modularExceptionalLocusDerivedHere : Bool
    modularExceptionalLocusDerivedHereIsFalse :
      modularExceptionalLocusDerivedHere ≡ false

canonicalRepresentationReductionBoundary : RepresentationReductionBoundary
canonicalRepresentationReductionBoundary =
  representationReductionBoundary
    true refl
    false refl
    false refl
    false refl
