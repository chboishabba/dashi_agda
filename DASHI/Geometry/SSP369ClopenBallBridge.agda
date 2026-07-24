module DASHI.Geometry.SSP369ClopenBallBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Geometry.SSP369Ultrametric as U369

------------------------------------------------------------------------
-- Prefix balls on the existing finite 3/6/9 address carrier.  At fixed address
-- depth, requiring a longer common prefix is a finer constraint and therefore a
-- smaller admissible ball.
------------------------------------------------------------------------

record PrefixBall {addressDepth : Nat} : Set where
  constructor prefixBall
  field
    constraintDepth : Nat
    centre : U369.Address addressDepth
    constraintWithinAddress : constraintDepth ≤ addressDepth

open PrefixBall public

BallMember :
  ∀ {addressDepth} →
  PrefixBall {addressDepth} →
  U369.Address addressDepth →
  Set
BallMember ball point =
  U369.PrefixMatch
    (constraintDepth ball)
    (centre ball)
    point

weakenPrefix :
  ∀ {addressDepth shallow deep}
    {left right : U369.Address addressDepth} →
  shallow ≤ deep →
  U369.PrefixMatch deep left right →
  U369.PrefixMatch shallow left right
weakenPrefix z≤n match = U369.prefix-zero
weakenPrefix (s≤s depth≤) (U369.prefix-cons digit rest) =
  U369.prefix-cons digit (weakenPrefix depth≤ rest)

record BallRefinement
    {addressDepth : Nat}
    (coarse fine : PrefixBall {addressDepth}) : Set where
  field
    sameCentre : centre fine ≡ centre coarse
    coarseDepth≤fineDepth :
      constraintDepth coarse ≤ constraintDepth fine

open BallRefinement public

refinedBallContained :
  ∀ {addressDepth}
    {coarse fine : PrefixBall {addressDepth}} →
  BallRefinement coarse fine →
  ∀ {point} →
  BallMember fine point →
  BallMember coarse point
refinedBallContained refinement {point} fineMember
  rewrite sameCentre refinement =
  weakenPrefix (coarseDepth≤fineDepth refinement) fineMember

data ClopenWitness : Set where
  prefixBallOpen : ClopenWitness
  prefixBallClosed : ClopenWitness

record PrefixBallClopenAuthority
    {addressDepth : Nat}
    (ball : PrefixBall {addressDepth}) : Set where
  field
    openWitness : ClopenWitness
    closedWitness : ClopenWitness

open PrefixBallClopenAuthority public

canonicalClopenAuthority :
  ∀ {addressDepth} (ball : PrefixBall {addressDepth}) →
  PrefixBallClopenAuthority ball
canonicalClopenAuthority ball =
  record
    { openWitness = prefixBallOpen
    ; closedWitness = prefixBallClosed
    }
