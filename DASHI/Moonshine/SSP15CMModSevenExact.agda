module DASHI.Moonshine.SSP15CMModSevenExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Jürgen Neukirch,
-- "Algebraic Number Theory",
-- Grundlehren der mathematischen Wissenschaften 322, Springer, 1999.
-- DOI: 10.1007/978-3-662-03983-0.
--
-- STANDARD NUMBER-THEORETIC CONTEXT
--
-- For a quadratic field of discriminant D, unramified prime splitting is
-- determined by the quadratic/Kronecker character chi_D.  For D = -7 the
-- odd-prime character reduces, by quadratic reciprocity, to the quadratic
-- residue character modulo 7: residues 1,2,4 split and residues 3,5,6 are
-- inert; residue 0 is ramified.  Since -7 is 1 mod 8, p=2 also splits, which
-- is consistent with the same finite residue table at residue 2.
--
-- DASHI CONTRIBUTION
--
-- Connect the repository's existing literal Q(sqrt(-7)) SSP15 splitting
-- table to that mod-7 character and use it to explain the +42 affine edges.
-- The theorem surface is finite and exact on all fifteen canonical SSP lanes;
-- it does not claim to reprove quadratic reciprocity generically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_%_)

import DASHI.Moonshine.SSP15AffineC3TranslationExact as SSP
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

cmClassFromModSeven : Nat → CM.CMPrimeSplittingClass
cmClassFromModSeven 0 = CM.ramified
cmClassFromModSeven 1 = CM.split
cmClassFromModSeven 2 = CM.split
cmClassFromModSeven 3 = CM.inert
cmClassFromModSeven 4 = CM.split
cmClassFromModSeven 5 = CM.inert
cmClassFromModSeven 6 = CM.inert
cmClassFromModSeven _ = CM.inert

sspCMClassAgreesWithModSevenCharacter :
  (prime : Lane.MonsterPrimeLane) →
  SSP.cmClass prime
  ≡ cmClassFromModSeven (Lane.monsterPrimeLaneToNat prime % 7)
sspCMClassAgreesWithModSevenCharacter Lane.p2 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p3 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p5 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p7 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p11 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p13 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p17 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p19 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p23 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p29 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p31 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p41 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p47 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p59 = refl
sspCMClassAgreesWithModSevenCharacter Lane.p71 = refl

fortyTwoModSevenIsZero : 42 % 7 ≡ 0
fortyTwoModSevenIsZero = refl

fiveAndFortySevenShareModSevenResidue : 5 % 7 ≡ 47 % 7
fiveAndFortySevenShareModSevenResidue = refl

seventeenAndFiftyNineShareModSevenResidue : 17 % 7 ≡ 59 % 7
seventeenAndFiftyNineShareModSevenResidue = refl

twentyNineAndSeventyOneShareModSevenResidue : 29 % 7 ≡ 71 % 7
twentyNineAndSeventyOneShareModSevenResidue = refl

fiveFortySevenResidueIsFive : 5 % 7 ≡ 5
fiveFortySevenResidueIsFive = refl

seventeenFiftyNineResidueIsThree : 17 % 7 ≡ 3
seventeenFiftyNineResidueIsThree = refl

twentyNineSeventyOneResidueIsOne : 29 % 7 ≡ 1
twentyNineSeventyOneResidueIsOne = refl

verticalFiveFortySevenCMFromResidue :
  cmClassFromModSeven (5 % 7) ≡ cmClassFromModSeven (47 % 7)
verticalFiveFortySevenCMFromResidue = refl

verticalSeventeenFiftyNineCMFromResidue :
  cmClassFromModSeven (17 % 7) ≡ cmClassFromModSeven (59 % 7)
verticalSeventeenFiftyNineCMFromResidue = refl

verticalTwentyNineSeventyOneCMFromResidue :
  cmClassFromModSeven (29 % 7) ≡ cmClassFromModSeven (71 % 7)
verticalTwentyNineSeventyOneCMFromResidue = refl
