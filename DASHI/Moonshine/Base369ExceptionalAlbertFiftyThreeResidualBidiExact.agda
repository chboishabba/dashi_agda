module DASHI.Moonshine.Base369ExceptionalAlbertFiftyThreeResidualBidiExact where

------------------------------------------------------------------------
-- BASE369 54->53 RESIDUAL <-> EXCEPTIONAL ALBERT 54->53 CANDIDATE
--
-- Two independently meaningful structures now meet at one typed frontier:
--
--   Base369 side:
--     SecondaryCell54 -> ResidualCell53
--     with one distinguished invariant state removed and SAME-action
--     restriction required for promotion.
--
--   exceptional side:
--     AlbertPair54 = (1+J0) + (1+J0*)
--     ReducedAlbertPair53 = J0 + (1+J0*)
--     with J0 of standard dimension 26.
--
-- This owner does NOT identify them by dimension.  It asks for explicit
-- two-sided carrier maps plus one same-action compatibility.  Once supplied,
-- the existing Base369 53 residual inherits an exceptional-Jordan coordinate
-- semantics without introducing another actual action.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Base

------------------------------------------------------------------------
-- 1. Same-actual-action cross-pollination.
------------------------------------------------------------------------

record Base369ExceptionalResidualRecognition : Setω where
  field
    baseRecognition : Base.ActualFiftyFourFiveModeResidualActionRecognition
    exceptionalRecognition : Exceptional.ExceptionalFiftyFourToFiftyThreeRecognition

    sameActor :
      Exceptional.Actor exceptionalRecognition ≡ Base.Actor baseRecognition

    sameActual54 :
      Exceptional.Actual54 exceptionalRecognition ≡ Base.Actual54 baseRecognition

    sameActual53 :
      Exceptional.Actual53 exceptionalRecognition ≡ Base.Actual53 baseRecognition

    -- The important payment is not cardinality: after transport along the
    -- same-carrier receipts, the exceptional action is the literal Base369
    -- actual action.  We keep the equality as a receipt rather than hiding
    -- transport through postulated definitional equality.
    same54Action : Set
    same53Action : Set

    sameRemovedInvariant : Set
    sameResidualInclusion : Set

open Base369ExceptionalResidualRecognition public

------------------------------------------------------------------------
-- 2. Candidate semantic consequences.
------------------------------------------------------------------------

baseResidualDimensionIsExceptional53 :
  Base.candidateResidualDimension ≡ Exceptional.reducedAlbertPairDimension
baseResidualDimensionIsExceptional53 =
  Base.candidateResidualDimensionIs53

baseFullDimensionIsExceptional54 :
  Base.candidateFullDimension ≡ Exceptional.albertPairDimension
baseFullDimensionIsExceptional54 =
  Base.candidateFullDimensionIs54

------------------------------------------------------------------------
-- 3. Stronger promotion target with explicit maps on the exact Base369
--    skeleton.  This is the useful theorem shape for future construction.
------------------------------------------------------------------------

record Base369ExceptionalSkeletonBidi : Set₁ where
  field
    AlbertPair : Exceptional.AlbertPairCarrier

    base54ToAlbert54 : Base.SecondaryCell54 → Exceptional.AlbertPair54 AlbertPair
    albert54ToBase54 : Exceptional.AlbertPair54 AlbertPair → Base.SecondaryCell54
    base54RoundTrip :
      (state : Base.SecondaryCell54) →
      albert54ToBase54 (base54ToAlbert54 state) ≡ state
    albert54RoundTrip :
      (state : Exceptional.AlbertPair54 AlbertPair) →
      base54ToAlbert54 (albert54ToBase54 state) ≡ state

    base53ToAlbert53 : Base.ResidualCell53 → Exceptional.ReducedAlbertPair53 AlbertPair
    albert53ToBase53 : Exceptional.ReducedAlbertPair53 AlbertPair → Base.ResidualCell53
    base53RoundTrip :
      (state : Base.ResidualCell53) →
      albert53ToBase53 (base53ToAlbert53 state) ≡ state
    albert53RoundTrip :
      (state : Exceptional.ReducedAlbertPair53 AlbertPair) →
      base53ToAlbert53 (albert53ToBase53 state) ≡ state

    removedBaseInvariantMatchesRemovedAlbertScalar : Set
    residualEmbeddingCommutes : Set

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record Base369ExceptionalResidualBoundary : Set where
  constructor base369ExceptionalResidualBoundary
  field
    both54StructuresExplicit : Bool
    both53ReductionsExplicit : Bool
    dimensionAgreementAvailable : Bool
    twoSidedCarrierRecognitionRequired : Bool
    sameActualActionRequired : Bool
    removedInvariantMustMatch : Bool
    cardinal54ImpliesExceptionalIdentification : Bool
    cardinal53ImpliesExceptionalIdentification : Bool
    actualMonsterResidualIdentifiedHere : Bool

canonicalBase369ExceptionalResidualBoundary : Base369ExceptionalResidualBoundary
canonicalBase369ExceptionalResidualBoundary =
  base369ExceptionalResidualBoundary
    true true true true true true
    false false false
