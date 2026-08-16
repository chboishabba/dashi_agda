module DASHI.Physics.Closure.NSTriadKNComSimpleAnnularCommonHatNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 63 B0 FALSIFIER
--
-- Round63 constructs the literal shell difference
--
--       Delta_s = P_{<=s} - P_{<=s-1}
--
-- and the corresponding annular commutator collision vector.  That
-- construction is correct, but it is NOT YET the common width-one hat needed
-- by the six-three Schur argument.
--
-- Reuse the Round62 far transport entry
--
--       input shell  = 0,
--       output shell = 3.
--
-- The simple annular centered mask is active at shell 0 (input endpoint) AND
-- shell 3 (output endpoint).  No width-one `DyadicHatSupport` can contain both.
--
-- Therefore B0 needs a genuinely Bony/dominant-frequency localization of the
-- TRANSPORT INTERACTION after annularizing the projector.  Merely replacing
-- nested P_{<=s} by Delta_s does not prove common-hat support.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact as Far
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat

_xor_ : Bool → Bool → Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false

annularCenteredActive : Nat → Z3.FourierMode → Z3.FourierMode → Bool
annularCenteredActive shell input output =
  Output.natEqual (Shell.shellIndex output) shell
  xor Output.natEqual (Shell.shellIndex input) shell

farSimpleAnnulusActiveAtZero :
  annularCenteredActive zero Far.farInput Far.farOutput ≡ true
farSimpleAnnulusActiveAtZero
  rewrite Far.farInputShellIsZero
        | Far.farOutputShellIsThree = refl

farSimpleAnnulusActiveAtThree :
  annularCenteredActive (suc (suc (suc zero)))
    Far.farInput Far.farOutput ≡ true
farSimpleAnnulusActiveAtThree
  rewrite Far.farInputShellIsZero
        | Far.farOutputShellIsThree = refl

zeroAndThreeNotWithinOne :
  ¬ Width.WithinOne zero (suc (suc (suc zero)))
zeroAndThreeNotWithinOne ()

noCommonHatContainsZeroAndThree :
  (support : Hat.DyadicHatSupport) →
  zero Width.∈ Hat.activeShells support →
  suc (suc (suc zero)) Width.∈ Hat.activeShells support →
  ⊥
noCommonHatContainsZeroAndThree support zeroActive threeActive =
  zeroAndThreeNotWithinOne
    (Width.activeShellPairWithinOne support
      zero (suc (suc (suc zero))) zeroActive threeActive)

record SimpleAnnularCommonHatClaim : Set where
  field
    commonHat : Hat.DyadicHatSupport
    shellZeroInHat : zero Width.∈ Hat.activeShells commonHat
    shellThreeInHat : suc (suc (suc zero)) Width.∈ Hat.activeShells commonHat

open SimpleAnnularCommonHatClaim public

simpleAnnularCommonHatClaimImpossible : SimpleAnnularCommonHatClaim → ⊥
simpleAnnularCommonHatClaimImpossible claim =
  noCommonHatContainsZeroAndThree
    (commonHat claim) (shellZeroInHat claim) (shellThreeInHat claim)

round63SimpleProjectorAnnularizationStillTooWide : Bool
round63SimpleProjectorAnnularizationStillTooWide = true

round63B0RequiresInteractionHatBeyondProjectorDifference : Bool
round63B0RequiresInteractionHatBeyondProjectorDifference = true

round63SimpleProjectorAnnularizationStillTooWideIsTrue :
  round63SimpleProjectorAnnularizationStillTooWide ≡ true
round63SimpleProjectorAnnularizationStillTooWideIsTrue = refl

round63B0RequiresInteractionHatBeyondProjectorDifferenceIsTrue :
  round63B0RequiresInteractionHatBeyondProjectorDifference ≡ true
round63B0RequiresInteractionHatBeyondProjectorDifferenceIsTrue = refl
