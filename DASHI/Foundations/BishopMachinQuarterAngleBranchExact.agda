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

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

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

threeFourthsBelowQuarter : Bishop._<_ threeFourths machinQuarterAngle
threeFourthsBelowQuarter =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm quarterIsFourthOfMachinPi)
    (BishopP.p<q⇒p⋆<q⋆
      (+ 3 / 4)
      (+ 1 / 4 * (+ 3 / 1))
      (λ ()))

quarterBelowElevenFourteenths :
  Bishop._<_ machinQuarterAngle elevenFourteenths
quarterBelowElevenFourteenths =
  BishopP.<-respˡ-≃
    quarterIsFourthOfMachinPi
    (BishopP.p<q⇒p⋆<q⋆
      (+ 1 / 4 * (+ 22 / 7))
      (+ 11 / 14)
      (λ ()))

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
