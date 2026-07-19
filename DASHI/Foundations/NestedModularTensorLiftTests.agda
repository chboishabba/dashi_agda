module DASHI.Foundations.NestedModularTensorLiftTests where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high
  ; HexTruth ; hex-0 ; hex-5
  ; NonaryTruth ; non-0 ; non-4 ; non-8
  )
open import DASHI.Foundations.NestedModularTensorLift

------------------------------------------------------------------------
-- Nonary lifting preserves the already-fixed lower ternary digit.
------------------------------------------------------------------------

lowLift0 : nonaryToTri (liftTriToNonary tri-low lift-0) ≡ tri-low
lowLift0 = refl

midLift1 : nonaryToTri (liftTriToNonary tri-mid lift-1) ≡ tri-mid
midLift1 = refl

highLift2 : nonaryToTri (liftTriToNonary tri-high lift-2) ≡ tri-high
highLift2 = refl

lowLiftValue : liftTriToNonary tri-low lift-0 ≡ non-0
lowLiftValue = refl

midLiftValue : liftTriToNonary tri-mid lift-1 ≡ non-4
midLiftValue = refl

highLiftValue : liftTriToNonary tri-high lift-2 ≡ non-8
highLiftValue = refl

------------------------------------------------------------------------
-- The six-lane carrier reconstructs exactly from parity × ternary data.
------------------------------------------------------------------------

hexZeroRoundTrip : hexReconstructCRT (hexObserveCRT hex-0) ≡ hex-0
hexZeroRoundTrip = refl

hexFiveRoundTrip : hexReconstructCRT (hexObserveCRT hex-5) ≡ hex-5
hexFiveRoundTrip = refl

------------------------------------------------------------------------
-- The stage labels state successor frames, not nontrivial mod-1 facts.
------------------------------------------------------------------------

fourIsOverThree : previousFrame stage-4 ≡ stage-3
fourIsOverThree = refl

tenIsOverNine : previousFrame stage-10 ≡ stage-9
tenIsOverNine = refl

elevenIsOverTen : previousFrame stage-11 ≡ stage-10
elevenIsOverTen = refl

------------------------------------------------------------------------
-- A local sheet may be retained verbatim while becoming a node in a
-- recursively larger tensor carrier.
------------------------------------------------------------------------

exampleSheet : Sheet369
exampleSheet (slot lens-3 past)   = non-0
exampleSheet (slot lens-3 now)    = non-4
exampleSheet (slot lens-3 future) = non-8
exampleSheet (slot lens-6 past)   = non-4
exampleSheet (slot lens-6 now)    = non-8
exampleSheet (slot lens-6 future) = non-0
exampleSheet (slot lens-9 past)   = non-8
exampleSheet (slot lens-9 now)    = non-0
exampleSheet (slot lens-9 future) = non-4

exampleTree : TensorTree
exampleTree = nestedSheet exampleSheet (localSheet exampleSheet ∷ [])

rootPreserved : rootSheet exampleTree ≡ exampleSheet
rootPreserved = refl
