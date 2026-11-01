module DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- DASHI CONTRIBUTION
--
-- Round 46 proved exact width one for the concrete dyadic-hat support.  This
-- module gives the physical Com lane its smallest NON-CIRCULAR active theorem.
-- Start from a support skeleton containing only the literal pair product,
-- support Bool, distance, nonnegativity and off-support annihilation.  Then:
--
--   same-object hat identification
-- + same-shell analytic bound
-- + forward/reverse adjacent-shell analytic bounds
--
-- construct the Round-45 `PhysicalOddPQBooleanSupportInput` itself.
--
-- Exact six-three targets:
--
--   g_6,3(0) = 17/64,
--   g_6,3(1) = 65/512.
--
-- No generic q,r active inequality is assumed as input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComBooleanSupportActiveReductionRound45Exact as BoolSupport
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth
import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

sameShellTarget adjacentShellTarget : ℚ
sameShellTarget = Int.+ 17 / 64
adjacentShellTarget = Int.+ 65 / 512

sixThreeSameShellExact :
  SixThree.twoBranchSquaredGap zero ≡ sameShellTarget
sixThreeSameShellExact = solve []

sixThreeAdjacentShellExact :
  SixThree.twoBranchSquaredGap (suc zero) ≡ adjacentShellTarget
sixThreeAdjacentShellExact = solve []

record PhysicalOddPQSupportSkeleton : Set where
  field
    physicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat
    supportActive : Nat → Nat → Bool

    pairProductNonnegative : ∀ q r →
      0ℚ ≤ physicalPairProduct q r

    inactiveSupportAnnihilatesPairProduct : ∀ q r →
      supportActive q r ≡ false →
      physicalPairProduct q r ≡ 0ℚ

open PhysicalOddPQSupportSkeleton public

record PhysicalOddPQHatIdentification
    (skeleton : PhysicalOddPQSupportSkeleton) : Set₁ where
  field
    commonHatSupport : Nat → Nat → Hat.DyadicHatSupport
    leftActiveInCommonHat : ∀ q r →
      supportActive skeleton q r ≡ true →
      q HatWidth.∈ Hat.activeShells (commonHatSupport q r)
    rightActiveInCommonHat : ∀ q r →
      supportActive skeleton q r ≡ true →
      r HatWidth.∈ Hat.activeShells (commonHatSupport q r)

open PhysicalOddPQHatIdentification public

activePairWithinOne :
  ∀ {skeleton}
    (identification : PhysicalOddPQHatIdentification skeleton) q r →
  supportActive skeleton q r ≡ true →
  HatWidth.WithinOne q r
activePairWithinOne identification q r active =
  HatWidth.activeShellPairWithinOne
    (commonHatSupport identification q r)
    q r
    (leftActiveInCommonHat identification q r active)
    (rightActiveInCommonHat identification q r active)

record SameAdjacentPhysicalComBounds
    (skeleton : PhysicalOddPQSupportSkeleton)
    (identification : PhysicalOddPQHatIdentification skeleton) : Set where
  field
    sameShellDistance : ∀ q → shellDistance skeleton q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      shellDistance skeleton q (suc q) ≡ suc zero
    backwardAdjacentDistance : ∀ q →
      shellDistance skeleton (suc q) q ≡ suc zero

    physicalComSameShellActiveBound : ∀ q →
      supportActive skeleton q q ≡ true →
      physicalPairProduct skeleton q q ≤ sameShellTarget

    physicalComAdjacentShellActiveBound : ∀ q →
      supportActive skeleton q (suc q) ≡ true →
      physicalPairProduct skeleton q (suc q) ≤ adjacentShellTarget

    physicalComReverseAdjacentShellActiveBound : ∀ q →
      supportActive skeleton (suc q) q ≡ true →
      physicalPairProduct skeleton (suc q) q ≤ adjacentShellTarget

open SameAdjacentPhysicalComBounds public

sameShellBoundHitsSixThree :
  ∀ {skeleton identification}
    (bounds : SameAdjacentPhysicalComBounds skeleton identification) q →
  supportActive skeleton q q ≡ true →
  physicalPairProduct skeleton q q
  ≤ SixThree.twoBranchSquaredGap (shellDistance skeleton q q)
sameShellBoundHitsSixThree bounds q active
  rewrite sameShellDistance bounds q
        | sixThreeSameShellExact =
  physicalComSameShellActiveBound bounds q active

forwardAdjacentBoundHitsSixThree :
  ∀ {skeleton identification}
    (bounds : SameAdjacentPhysicalComBounds skeleton identification) q →
  supportActive skeleton q (suc q) ≡ true →
  physicalPairProduct skeleton q (suc q)
  ≤ SixThree.twoBranchSquaredGap (shellDistance skeleton q (suc q))
forwardAdjacentBoundHitsSixThree bounds q active
  rewrite forwardAdjacentDistance bounds q
        | sixThreeAdjacentShellExact =
  physicalComAdjacentShellActiveBound bounds q active

backwardAdjacentBoundHitsSixThree :
  ∀ {skeleton identification}
    (bounds : SameAdjacentPhysicalComBounds skeleton identification) q →
  supportActive skeleton (suc q) q ≡ true →
  physicalPairProduct skeleton (suc q) q
  ≤ SixThree.twoBranchSquaredGap (shellDistance skeleton (suc q) q)
backwardAdjacentBoundHitsSixThree bounds q active
  rewrite backwardAdjacentDistance bounds q
        | sixThreeAdjacentShellExact =
  physicalComReverseAdjacentShellActiveBound bounds q active

physicalComActiveBoundFromSameAdjacent :
  ∀ {skeleton}
    (identification : PhysicalOddPQHatIdentification skeleton)
    (bounds : SameAdjacentPhysicalComBounds skeleton identification)
    q r →
  supportActive skeleton q r ≡ true →
  physicalPairProduct skeleton q r
  ≤ SixThree.twoBranchSquaredGap (shellDistance skeleton q r)
physicalComActiveBoundFromSameAdjacent identification bounds q r active
  with activePairWithinOne identification q r active
... | HatWidth.same q = sameShellBoundHitsSixThree bounds q active
... | HatWidth.next q = forwardAdjacentBoundHitsSixThree bounds q active
... | HatWidth.previous q = backwardAdjacentBoundHitsSixThree bounds q active

physicalBooleanSupportInputFromSameAdjacent :
  ∀ {skeleton}
    (identification : PhysicalOddPQHatIdentification skeleton) →
  SameAdjacentPhysicalComBounds skeleton identification →
  BoolSupport.PhysicalOddPQBooleanSupportInput
physicalBooleanSupportInputFromSameAdjacent {skeleton} identification bounds = record
  { physicalPairProduct = physicalPairProduct skeleton
  ; shellDistance = shellDistance skeleton
  ; supportActive = supportActive skeleton
  ; pairProductNonnegative = pairProductNonnegative skeleton
  ; inactiveSupportAnnihilatesPairProduct =
      inactiveSupportAnnihilatesPairProduct skeleton
  ; activeSupportPairProductBelowSixThree =
      physicalComActiveBoundFromSameAdjacent identification bounds
  }

physicalComEnvelopeFromSameAdjacent :
  ∀ {skeleton}
    (identification : PhysicalOddPQHatIdentification skeleton) →
  SameAdjacentPhysicalComBounds skeleton identification →
  Support.PhysicalComSupportOverlapEnvelope
physicalComEnvelopeFromSameAdjacent identification bounds =
  BoolSupport.physicalComBooleanSupportEnvelope
    (physicalBooleanSupportInputFromSameAdjacent identification bounds)

comActiveAnalysisReducedToSameAndAdjacent : Bool
comActiveAnalysisReducedToSameAndAdjacent = true

physicalSameAdjacentBoundsConstructed : Bool
physicalSameAdjacentBoundsConstructed = false

comActiveAnalysisReducedToSameAndAdjacentIsTrue :
  comActiveAnalysisReducedToSameAndAdjacent ≡ true
comActiveAnalysisReducedToSameAndAdjacentIsTrue = refl
