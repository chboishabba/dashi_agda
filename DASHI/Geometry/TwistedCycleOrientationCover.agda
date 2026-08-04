module DASHI.Geometry.TwistedCycleOrientationCover where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A finite combinatorial non-orientability witness.
--
-- The two-edge base cycle has identity transport on one edge and a flip on
-- the other.  Full-loop holonomy is therefore the nontrivial automorphism of
-- the two-element orientation fibre, and no fixed global orientation exists.
------------------------------------------------------------------------

data OrientationSign : Set where
  plus minus : OrientationSign

flipSign : OrientationSign → OrientationSign
flipSign plus = minus
flipSign minus = plus

flipSignInvolutive : ∀ sign → flipSign (flipSign sign) ≡ sign
flipSignInvolutive plus = refl
flipSignInvolutive minus = refl

flipSignHasNoFixedPoint : ∀ sign → ¬ (flipSign sign ≡ sign)
flipSignHasNoFixedPoint plus ()
flipSignHasNoFixedPoint minus ()

data CycleEdge : Set where
  untwistedEdge twistedEdge : CycleEdge

edgeTransport : CycleEdge → OrientationSign → OrientationSign
edgeTransport untwistedEdge sign = sign
edgeTransport twistedEdge sign = flipSign sign

loopHolonomy : OrientationSign → OrientationSign
loopHolonomy sign =
  edgeTransport twistedEdge (edgeTransport untwistedEdge sign)

loopHolonomyIsFlip : ∀ sign → loopHolonomy sign ≡ flipSign sign
loopHolonomyIsFlip plus = refl
loopHolonomyIsFlip minus = refl

loopHolonomyHasNoFixedPoint :
  ∀ sign → ¬ (loopHolonomy sign ≡ sign)
loopHolonomyHasNoFixedPoint sign equality =
  flipSignHasNoFixedPoint sign
    (trans (sym (loopHolonomyIsFlip sign)) equality)

record GlobalOrientationSection : Set where
  field
    chosenOrientation : OrientationSign
    compatibleWithFullLoop :
      loopHolonomy chosenOrientation ≡ chosenOrientation

noGlobalOrientationSection : ¬ GlobalOrientationSection
noGlobalOrientationSection section =
  loopHolonomyHasNoFixedPoint
    (GlobalOrientationSection.chosenOrientation section)
    (GlobalOrientationSection.compatibleWithFullLoop section)

record TwistedCycleReceipt : Set where
  field
    transport : CycleEdge → OrientationSign → OrientationSign
    holonomy : OrientationSign → OrientationSign
    holonomyIsNontrivialFlip :
      ∀ sign → holonomy sign ≡ flipSign sign
    noCompatibleGlobalOrientation :
      ¬ GlobalOrientationSection

canonicalTwistedCycleReceipt : TwistedCycleReceipt
canonicalTwistedCycleReceipt = record
  { transport = edgeTransport
  ; holonomy = loopHolonomy
  ; holonomyIsNontrivialFlip = loopHolonomyIsFlip
  ; noCompatibleGlobalOrientation = noGlobalOrientationSection
  }

record TwistedCycleAuthorityBoundary : Set where
  field
    finiteHolonomyTheoremProved : Bool
    fullContinuousMobiusStripConstructed : Bool
    semanticNegationAutomaticallyFollows : Bool
    everyIdeologyTraversesTwistedLoopClaimed : Bool
    scopeNote : String

canonicalTwistedCycleAuthorityBoundary :
  TwistedCycleAuthorityBoundary
canonicalTwistedCycleAuthorityBoundary = record
  { finiteHolonomyTheoremProved = true
  ; fullContinuousMobiusStripConstructed = false
  ; semanticNegationAutomaticallyFollows = false
  ; everyIdeologyTraversesTwistedLoopClaimed = false
  ; scopeNote =
      "The checked theorem is a finite orientation-cover obstruction; semantic and empirical parallax require additional labelling and trajectory witnesses."
  }
