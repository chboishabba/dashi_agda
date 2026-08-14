module DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterNewtonBudgetExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushMaximalQuarterInvariantBallExact as Ball

threeSixteenths : ℚ
threeSixteenths = + 3 / 16

referenceResidualTarget : ℚ
referenceResidualTarget = (+ 3 / 4) * Ball.maximalReferenceCorrection

fourThirdsTimesThreeSixteenthsIsQuarter :
  Reopen.fourThirds * threeSixteenths ≡ Ball.quarter
fourThirdsTimesThreeSixteenthsIsQuarter = ℚRing.solve []

fourThirdsTimesReferenceResidualIsReferenceCorrection :
  Reopen.fourThirds * referenceResidualTarget ≡ Ball.maximalReferenceCorrection
fourThirdsTimesReferenceResidualIsReferenceCorrection = ℚRing.solve []
