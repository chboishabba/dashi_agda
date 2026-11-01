module DASHI.Foundations.BishopMachinQuarterAngleBranchExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- John Machin's 1706 identity has no modern DOI.  The exact rational tangent
-- algebra used here is constructed in BishopMachinRationalTangentAlgebraExact.
--
-- DASHI CONTRIBUTION
--
-- Separate branch control from the remaining analytic trig semantics.
-- Define the actual Bishop quarter-Machin angle
--
--   theta_M = 4 atan_B(1/5) - atan_B(1/239).
--
-- Then bishopMachinPi = 4 theta_M definitionally/algebraically, and the already
-- proved constructive window 3 < bishopMachinPi < 22/7 gives
--
--   3/4 < theta_M < 11/14.
--
-- Thus once the concrete Bishop tangent/addition theorem is proved, the exact
-- rational tangent computation tan(theta_M)=1 has no remaining quadrant/branch
-- ambiguity.  This file does not assume that tangent theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; _*_; *≡*)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Foundations.BishopMachinRationalTangentAlgebraExact as Tangent
import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieProofLevel

embed = Bishop._⋆

fourth : Bishop.ℝ
fourth = embed (+ 1 / 4)

threeFourths : Bishop.ℝ
threeFourths = embed (+ 3 / 4)

elevenFourteenths : Bishop.ℝ
elevenFourteenths = embed (+ 11 / 14)

machinQuarterAngle : Bishop.ℝ
machinQuarterAngle =
  Bishop._-_
    (Bishop._*_ (embed (+ 4 / 1))
      (Machin.bishopAtanHalfBall Machin.bishopOneFifth Machin.oneFifthInsideHalf))
    (Machin.bishopAtanHalfBall
      Machin.bishopOneTwoHundredThirtyNinth
      Machin.oneTwoHundredThirtyNinthInsideHalf)

fourTimesQuarterIsMachinPi :
  Bishop._≃_
    (Bishop._*_ (embed (+ 4 / 1)) machinQuarterAngle)
    Machin.bishopMachinPi
fourTimesQuarterIsMachinPi =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ a b →
      Κ (+ 4 / 1) ⊗ ((Κ (+ 4 / 1) ⊗ a) ⊖ b)
      ⊜
      (Κ (+ 16 / 1) ⊗ a) ⊖ (Κ (+ 4 / 1) ⊗ b))
    BishopP.≃-refl
    (Machin.bishopAtanHalfBall Machin.bishopOneFifth Machin.oneFifthInsideHalf)
    (Machin.bishopAtanHalfBall
      Machin.bishopOneTwoHundredThirtyNinth
      Machin.oneTwoHundredThirtyNinthInsideHalf)

quarterIsFourthOfMachinPi :
  Bishop._≃_
    machinQuarterAngle
    (Bishop._*_ fourth Machin.bishopMachinPi)
quarterIsFourthOfMachinPi =
  let open BishopP.ℝ-Solver
  in BishopP.≃-trans
    (BishopP.≃-symm
      (solve 1
        (λ q → q ⊜ Κ (+ 1 / 4) ⊗ (Κ (+ 4 / 1) ⊗ q))
        BishopP.≃-refl
        machinQuarterAngle))
    (BishopP.*-congʳ fourTimesQuarterIsMachinPi)


-- The source bounds 3<pi_M<22/7 must first be scaled by the
-- STRICTLY POSITIVE quarter. Comparing 3/4 to 3/4 (or 11/14 to
-- 11/14) would be an invalid strict-order "proof".
fourthPositive : Bishop.Positive fourth
fourthPositive = BishopP.0<x⇒posx Machin.quarterPositive

quarterTimesThreeEquivalentThreeFourths :
  Bishop._≃_
    (Bishop._*_ fourth (embed (+ 3 / 1)))
    threeFourths
quarterTimesThreeEquivalentThreeFourths =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.⋆-distrib-* (+ 1 / 4) (+ 3 / 1)))
    (BishopP.⋆-cong (Q.*≡* refl))

quarterTimesTwentyTwoSeventhsEquivalentElevenFourteenths :
  Bishop._≃_
    (Bishop._*_ fourth (embed (+ 22 / 7)))
    elevenFourteenths
quarterTimesTwentyTwoSeventhsEquivalentElevenFourteenths =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.⋆-distrib-* (+ 1 / 4) (+ 22 / 7)))
    (BishopP.⋆-cong (Q.*≡* refl))

threeFourthsBelowQuarter : Bishop._<_ threeFourths machinQuarterAngle
threeFourthsBelowQuarter =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm quarterIsFourthOfMachinPi)
    (BishopP.<-respˡ-≃
      quarterTimesThreeEquivalentThreeFourths
      (BishopP.*-monoʳ-<-pos
        fourthPositive
        Window.threeBelowMachinPi))

quarterBelowElevenFourteenths :
  Bishop._<_ machinQuarterAngle elevenFourteenths
quarterBelowElevenFourteenths =
  BishopP.<-respʳ-≃
    quarterTimesTwentyTwoSeventhsEquivalentElevenFourteenths
    (BishopP.<-respˡ-≃
      quarterIsFourthOfMachinPi
      (BishopP.*-monoʳ-<-pos
        fourthPositive
        Window.machinPiBelowTwentyTwoSevenths))

-- Algebraic target already computed independently: the rational tangent
-- parameter obtained by four doublings from 1/5 followed by subtraction of
-- 1/239 is exactly 1.
formalMachinQuarterTangentIsOne :
  Tangent.machinTangentParameter ≡ Tangent.one
formalMachinQuarterTangentIsOne = Tangent.machinTangentParameterIsOne

bishopMachinQuarterBranchLevel : ProofLevel
bishopMachinQuarterBranchLevel = machineChecked

-- The sole remaining semantic bridge is analytic: identify the rational
-- tangent operations above with the tangent induced by the same concrete Bishop
-- sine/cosine series at machinQuarterAngle.
bishopMachinQuarterConcreteTrigIdentificationLevel : ProofLevel
bishopMachinQuarterConcreteTrigIdentificationLevel = conditional
