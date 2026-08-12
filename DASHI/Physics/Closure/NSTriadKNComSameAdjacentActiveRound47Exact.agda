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
-- module gives the physical Com lane its smallest falsifiable active theorem:
-- after same-object identification with that support, only
--
--   d=0 : P(q,q)
--   d=1 : P(q,q+1), P(q+1,q)
--
-- need analytic bounds.  The exact six-three targets are also computed:
--
--   g_6,3(0) = 17/64,
--   g_6,3(1) = 65/512.
--
-- Same-shell and adjacent-shell estimates remain separate hypotheses; no
-- generic q,r inequality is postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComBooleanSupportActiveReductionRound45Exact as BoolSupport
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

record PhysicalOddPQHatIdentification
    (physical : BoolSupport.PhysicalOddPQBooleanSupportInput) : Set₁ where
  field
    commonHatSupport : Nat → Nat → Hat.DyadicHatSupport
    leftActiveInCommonHat : ∀ q r →
      BoolSupport.supportActive physical q r ≡ true →
      q HatWidth.∈ Hat.activeShells (commonHatSupport q r)
    rightActiveInCommonHat : ∀ q r →
      BoolSupport.supportActive physical q r ≡ true →
      r HatWidth.∈ Hat.activeShells (commonHatSupport q r)

open PhysicalOddPQHatIdentification public

activePairWithinOne :
  ∀ {physical}
    (identification : PhysicalOddPQHatIdentification physical) q r →
  BoolSupport.supportActive physical q r ≡ true →
  HatWidth.WithinOne q r
activePairWithinOne identification q r active =
  HatWidth.activeShellPairWithinOne
    (commonHatSupport identification q r)
    q r
    (leftActiveInCommonHat identification q r active)
    (rightActiveInCommonHat identification q r active)

record SameAdjacentPhysicalComBounds
    (physical : BoolSupport.PhysicalOddPQBooleanSupportInput)
    (identification : PhysicalOddPQHatIdentification physical) : Set where
  field
    sameShellDistance : ∀ q →
      BoolSupport.shellDistance physical q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      BoolSupport.shellDistance physical q (suc q) ≡ suc zero
    backwardAdjacentDistance : ∀ q →
      BoolSupport.shellDistance physical (suc q) q ≡ suc zero

    physicalComSameShellActiveBound : ∀ q →
      BoolSupport.supportActive physical q q ≡ true →
      BoolSupport.physicalPairProduct physical q q ≤ sameShellTarget

    physicalComAdjacentShellActiveBound : ∀ q →
      BoolSupport.supportActive physical q (suc q) ≡ true →
      BoolSupport.physicalPairProduct physical q (suc q)
      ≤ adjacentShellTarget

    physicalComReverseAdjacentShellActiveBound : ∀ q →
      BoolSupport.supportActive physical (suc q) q ≡ true →
      BoolSupport.physicalPairProduct physical (suc q) q
      ≤ adjacentShellTarget

open SameAdjacentPhysicalComBounds public

sameShellBoundHitsSixThree :
  ∀ {physical identification}
    (bounds : SameAdjacentPhysicalComBounds physical identification) q →
  BoolSupport.supportActive physical q q ≡ true →
  BoolSupport.physicalPairProduct physical q q
  ≤ SixThree.twoBranchSquaredGap
      (BoolSupport.shellDistance physical q q)
sameShellBoundHitsSixThree bounds q active
  rewrite sameShellDistance bounds q
        | sixThreeSameShellExact =
  physicalComSameShellActiveBound bounds q active

forwardAdjacentBoundHitsSixThree :
  ∀ {physical identification}
    (bounds : SameAdjacentPhysicalComBounds physical identification) q →
  BoolSupport.supportActive physical q (suc q) ≡ true →
  BoolSupport.physicalPairProduct physical q (suc q)
  ≤ SixThree.twoBranchSquaredGap
      (BoolSupport.shellDistance physical q (suc q))
forwardAdjacentBoundHitsSixThree bounds q active
  rewrite forwardAdjacentDistance bounds q
        | sixThreeAdjacentShellExact =
  physicalComAdjacentShellActiveBound bounds q active

backwardAdjacentBoundHitsSixThree :
  ∀ {physical identification}
    (bounds : SameAdjacentPhysicalComBounds physical identification) q →
  BoolSupport.supportActive physical (suc q) q ≡ true →
  BoolSupport.physicalPairProduct physical (suc q) q
  ≤ SixThree.twoBranchSquaredGap
      (BoolSupport.shellDistance physical (suc q) q)
backwardAdjacentBoundHitsSixThree bounds q active
  rewrite backwardAdjacentDistance bounds q
        | sixThreeAdjacentShellExact =
  physicalComReverseAdjacentShellActiveBound bounds q active

physicalComActiveBoundFromSameAdjacent :
  ∀ {physical}
    (identification : PhysicalOddPQHatIdentification physical)
    (bounds : SameAdjacentPhysicalComBounds physical identification)
    q r →
  BoolSupport.supportActive physical q r ≡ true →
  BoolSupport.physicalPairProduct physical q r
  ≤ SixThree.twoBranchSquaredGap (BoolSupport.shellDistance physical q r)
physicalComActiveBoundFromSameAdjacent identification bounds q r active
  with activePairWithinOne identification q r active
... | HatWidth.same q = sameShellBoundHitsSixThree bounds q active
... | HatWidth.next q = forwardAdjacentBoundHitsSixThree bounds q active
... | HatWidth.previous q = backwardAdjacentBoundHitsSixThree bounds q active

comActiveAnalysisReducedToSameAndAdjacent : Bool
comActiveAnalysisReducedToSameAndAdjacent = true

physicalSameAdjacentBoundsConstructed : Bool
physicalSameAdjacentBoundsConstructed = false

comActiveAnalysisReducedToSameAndAdjacentIsTrue :
  comActiveAnalysisReducedToSameAndAdjacent ≡ true
comActiveAnalysisReducedToSameAndAdjacentIsTrue = refl
