module DASHI.Philosophy.BreadthProfile where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Breadth is multi-axis.  Search breadth, processing breadth, communication,
-- tolerance, legitimacy, and accessibility must not be collapsed into one
-- geometric width.

data BreadthAxis : Set where
  searchBreadth :
    BreadthAxis

  processingBreadth :
    BreadthAxis

  communicationBreadth :
    BreadthAxis

  toleranceBreadth :
    BreadthAxis

  legitimateBreadth :
    BreadthAxis

  accessibleBreadth :
    BreadthAxis

canonicalBreadthAxes :
  List BreadthAxis
canonicalBreadthAxes =
  searchBreadth
  ∷ processingBreadth
  ∷ communicationBreadth
  ∷ toleranceBreadth
  ∷ legitimateBreadth
  ∷ accessibleBreadth
  ∷ []

record BreadthProfile (Measure : Set) : Set₁ where
  field
    search :
      Measure

    processing :
      Measure

    communication :
      Measure

    tolerance :
      Measure

    legitimate :
      Measure

    accessible :
      Measure

    axesRemainDistinct :
      Set

open BreadthProfile public

record BroadMindednessBoundary : Set where
  constructor mkBroadMindednessBoundary
  field
    manyOptionsAloneSuffice :
      Bool

    selfRevisionMatters :
      Bool

    residualTrackingMatters :
      Bool

    principledRefusalCompatible :
      Bool

    infiniteOpennessRequired :
      Bool

open BroadMindednessBoundary public

canonicalBroadMindednessBoundary :
  BroadMindednessBoundary
canonicalBroadMindednessBoundary =
  mkBroadMindednessBoundary
    false
    true
    true
    true
    false

canonicalManyOptionsNotEnough :
  manyOptionsAloneSuffice canonicalBroadMindednessBoundary
  ≡
  false
canonicalManyOptionsNotEnough =
  refl
