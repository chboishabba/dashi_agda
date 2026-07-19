module DASHI.Foundations.NestedModularTensorLift where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high
  ; HexTruth ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; NonaryTruth ; non-0 ; non-1 ; non-2 ; non-3 ; non-4
  ; non-5 ; non-6 ; non-7 ; non-8
  )

------------------------------------------------------------------------
-- Exact lower observations
--
-- A nonary state is a one-trit refinement of a ternary state.  The
-- projection forgets the high trit and therefore preserves the already
-- fixed coarse polarity.
------------------------------------------------------------------------

nonaryToTri : NonaryTruth → TriTruth
nonaryToTri non-0 = tri-low
nonaryToTri non-1 = tri-mid
nonaryToTri non-2 = tri-high
nonaryToTri non-3 = tri-low
nonaryToTri non-4 = tri-mid
nonaryToTri non-5 = tri-high
nonaryToTri non-6 = tri-low
nonaryToTri non-7 = tri-mid
nonaryToTri non-8 = tri-high

data LiftDigit : Set where
  lift-0 lift-1 lift-2 : LiftDigit

liftTriToNonary : TriTruth → LiftDigit → NonaryTruth
liftTriToNonary tri-low  lift-0 = non-0
liftTriToNonary tri-mid  lift-0 = non-1
liftTriToNonary tri-high lift-0 = non-2
liftTriToNonary tri-low  lift-1 = non-3
liftTriToNonary tri-mid  lift-1 = non-4
liftTriToNonary tri-high lift-1 = non-5
liftTriToNonary tri-low  lift-2 = non-6
liftTriToNonary tri-mid  lift-2 = non-7
liftTriToNonary tri-high lift-2 = non-8

nonaryLiftPreservesCoarsePolarity :
  (coarse : TriTruth) (digit : LiftDigit) →
  nonaryToTri (liftTriToNonary coarse digit) ≡ coarse
nonaryLiftPreservesCoarsePolarity tri-low  lift-0 = refl
nonaryLiftPreservesCoarsePolarity tri-mid  lift-0 = refl
nonaryLiftPreservesCoarsePolarity tri-high lift-0 = refl
nonaryLiftPreservesCoarsePolarity tri-low  lift-1 = refl
nonaryLiftPreservesCoarsePolarity tri-mid  lift-1 = refl
nonaryLiftPreservesCoarsePolarity tri-high lift-1 = refl
nonaryLiftPreservesCoarsePolarity tri-low  lift-2 = refl
nonaryLiftPreservesCoarsePolarity tri-mid  lift-2 = refl
nonaryLiftPreservesCoarsePolarity tri-high lift-2 = refl

record NonaryRefinement (coarse : TriTruth) : Set where
  constructor refine
  field
    digit : LiftDigit

  value : NonaryTruth
  value = liftTriToNonary coarse digit

  preserves : nonaryToTri value ≡ coarse
  preserves = nonaryLiftPreservesCoarsePolarity coarse digit

------------------------------------------------------------------------
-- Six is not another 3-adic precision step.
--
-- Z/6 separates into its parity observation and ternary observation.
-- This is the finite, constructive CRT boundary between the pairwise
-- coprime 2-part and 3-part.
------------------------------------------------------------------------

data Bit : Set where
  even odd : Bit

record HexCRT : Set where
  constructor _,_
  field
    parity  : Bit
    ternary : TriTruth

hexObserveCRT : HexTruth → HexCRT
hexObserveCRT hex-0 = even , tri-low
hexObserveCRT hex-1 = odd  , tri-mid
hexObserveCRT hex-2 = even , tri-high
hexObserveCRT hex-3 = odd  , tri-low
hexObserveCRT hex-4 = even , tri-mid
hexObserveCRT hex-5 = odd  , tri-high

hexReconstructCRT : HexCRT → HexTruth
hexReconstructCRT (even , tri-low)  = hex-0
hexReconstructCRT (odd  , tri-low)  = hex-3
hexReconstructCRT (even , tri-mid)  = hex-4
hexReconstructCRT (odd  , tri-mid)  = hex-1
hexReconstructCRT (even , tri-high) = hex-2
hexReconstructCRT (odd  , tri-high) = hex-5

hexCRT-reconstruct-observe :
  (h : HexTruth) → hexReconstructCRT (hexObserveCRT h) ≡ h
hexCRT-reconstruct-observe hex-0 = refl
hexCRT-reconstruct-observe hex-1 = refl
hexCRT-reconstruct-observe hex-2 = refl
hexCRT-reconstruct-observe hex-3 = refl
hexCRT-reconstruct-observe hex-4 = refl
hexCRT-reconstruct-observe hex-5 = refl

hexCRT-observe-reconstruct :
  (p : HexCRT) → hexObserveCRT (hexReconstructCRT p) ≡ p
hexCRT-observe-reconstruct (even , tri-low)  = refl
hexCRT-observe-reconstruct (odd  , tri-low)  = refl
hexCRT-observe-reconstruct (even , tri-mid)  = refl
hexCRT-observe-reconstruct (odd  , tri-mid)  = refl
hexCRT-observe-reconstruct (even , tri-high) = refl
hexCRT-observe-reconstruct (odd  , tri-high) = refl

------------------------------------------------------------------------
-- The 3 × 3 nonary sheet is one local chart, not the global state space.
------------------------------------------------------------------------

data Lens369 : Set where
  lens-3 lens-6 lens-9 : Lens369

data Time3 : Set where
  past now future : Time3

record Slot : Set where
  constructor slot
  field
    lens : Lens369
    time : Time3

Sheet369 : Set
Sheet369 = Slot → NonaryTruth

coarseSheet : Sheet369 → Slot → TriTruth
coarseSheet sheet coordinate = nonaryToTri (sheet coordinate)

------------------------------------------------------------------------
-- Recursive state carrier.
--
-- Each local 3 × 3 sheet may become one node in a larger tensor tree.
-- This avoids identifying the 19,683 possible ternary-valued sheets with
-- the total recursively nested state space.
------------------------------------------------------------------------

data TensorTree : Set where
  localSheet : Sheet369 → TensorTree
  nestedSheet : Sheet369 → List TensorTree → TensorTree

rootSheet : TensorTree → Sheet369
rootSheet (localSheet sheet) = sheet
rootSheet (nestedSheet sheet children) = sheet

------------------------------------------------------------------------
-- Stage indexing and the tensor-order jump.
--
-- “10 over 9” and “11 over 10” are successor-frame relations.  They are
-- deliberately not stated as informative congruences modulo 1, because
-- every natural number has the same residue modulo 1.
------------------------------------------------------------------------

data Stage : Set where
  stage-0 stage-1 stage-2 stage-3 stage-4 stage-5 : Stage
  stage-6 stage-7 stage-8 stage-9 stage-10 stage-11 : Stage

previousFrame : Stage → Stage
previousFrame stage-0  = stage-0
previousFrame stage-1  = stage-0
previousFrame stage-2  = stage-1
previousFrame stage-3  = stage-2
previousFrame stage-4  = stage-3
previousFrame stage-5  = stage-4
previousFrame stage-6  = stage-5
previousFrame stage-7  = stage-6
previousFrame stage-8  = stage-7
previousFrame stage-9  = stage-8
previousFrame stage-10 = stage-9
previousFrame stage-11 = stage-10

stage4Over3 : previousFrame stage-4 ≡ stage-3
stage4Over3 = refl

stage10Over9 : previousFrame stage-10 ≡ stage-9
stage10Over9 = refl

stage11Over10 : previousFrame stage-11 ≡ stage-10
stage11Over10 = refl

record TensorOrderJump : Set where
  constructor jump
  field
    currentSheet : Sheet369
    mod3Shadow   : Slot → TriTruth
    mod6Shadow   : Slot → HexCRT
    mod9Detail   : Slot → NonaryTruth
    nested       : List TensorTree

    mod9PreservesMod3 :
      (coordinate : Slot) →
      nonaryToTri (mod9Detail coordinate) ≡ mod3Shadow coordinate

------------------------------------------------------------------------
-- Aperture is explicit metadata, not inferred from an invalid mixed-base
-- digit string.  It records how many refinement constraints are retained.
------------------------------------------------------------------------

record ApertureState : Set where
  constructor aperture
  field
    resolvedDepth : Nat
    carrier       : TensorTree
