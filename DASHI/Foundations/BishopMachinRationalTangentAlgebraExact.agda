module DASHI.Foundations.BishopMachinRationalTangentAlgebraExact where

------------------------------------------------------------------------
-- HISTORICAL / MATHEMATICAL SOURCE
--
-- John Machin (1706), classical identity
--
--      pi/4 = 4 atan(1/5) - atan(1/239).
--
-- No DOI was assigned to the historical source.  For a modern account see
-- Jonathan M. Borwein and Peter B. Borwein, "Pi and the AGM", Wiley, 1987
-- (book; no DOI assigned to the original edition).
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022, arXiv:2205.08354.
-- No DOI assigned.  Murray/Bishop supplies the constructive-real completion
-- that will host the arctangent series; this file is the exact rational angle
-- algebra needed before that analytic bridge.
--
-- DASHI CONTRIBUTION
--
-- Do not postulate Machin's formula as a statement about pi.  First prove the
-- entire tangent arithmetic exactly over Q:
--
--   tan a = 1/5
--   tan 2a = 5/12
--   tan 4a = 120/119
--   tan b = 1/239
--   tan(4a-b) = 1.
--
-- The future Bishop arctan/sine/cosine characterization then needs only the
-- tangent addition/subtraction theorem and constructive branch control to
-- identify 4a-b with pi/4.  Thus the numerical content of Machin's identity is
-- already machine algebra and no trig semantics is smuggled into the pi lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneFifth fiveTwelfths oneHundredTwentyOverOneHundredNineteen
  oneOverTwoHundredThirtyNine : ℚ
oneFifth = + 1 / 5
fiveTwelfths = + 5 / 12
oneHundredTwentyOverOneHundredNineteen = + 120 / 119
oneOverTwoHundredThirtyNine = + 1 / 239

-- Division-free tangent doubling relation:
-- y(1-x^2)=2x.  The equations below prove the exact selected rational roots.
tangentDoubleRelation : ℚ → ℚ → ℚ
tangentDoubleRelation x y = y * (1ℚ - x * x) - (x + x)

oneFifthDoublesToFiveTwelfths :
  tangentDoubleRelation oneFifth fiveTwelfths ≡ + 0 / 1
oneFifthDoublesToFiveTwelfths = ℚRing.solve-∀

fiveTwelfthsDoublesToOneHundredTwentyOverOneHundredNineteen :
  tangentDoubleRelation
    fiveTwelfths oneHundredTwentyOverOneHundredNineteen
  ≡ + 0 / 1
fiveTwelfthsDoublesToOneHundredTwentyOverOneHundredNineteen =
  ℚRing.solve-∀

-- Division-free tangent subtraction relation:
-- z(1+xy)=x-y.  For x=tan(4a), y=tan b, z=1.
tangentSubtractRelation : ℚ → ℚ → ℚ → ℚ
tangentSubtractRelation x y z = z * (1ℚ + x * y) - (x - y)

machinTangentSubtractionIsOne :
  tangentSubtractRelation
    oneHundredTwentyOverOneHundredNineteen
    oneOverTwoHundredThirtyNine
    1ℚ
  ≡ + 0 / 1
machinTangentSubtractionIsOne = ℚRing.solve-∀

-- Strong cross-multiplied identity used by a constructive tangent theorem.
machinCrossProductIdentity :
  oneHundredTwentyOverOneHundredNineteen
    - oneOverTwoHundredThirtyNine
  ≡ 1ℚ
    + oneHundredTwentyOverOneHundredNineteen
      * oneOverTwoHundredThirtyNine
machinCrossProductIdentity = ℚRing.solve-∀

machinRationalTangentAlgebraLevel : ProofLevel
machinRationalTangentAlgebraLevel = machineChecked

-- Remaining analytic foundation lane:
--   construct atan_B(1/5), atan_B(1/239) from their alternating series;
--   prove tangent addition/subtraction for those series;
--   use branch control to characterize the resulting Machin real as pi.
bishopArctangentSeriesConstructionLevel : ProofLevel
bishopArctangentSeriesConstructionLevel = conditional

bishopMachinTrigCharacterizationLevel : ProofLevel
bishopMachinTrigCharacterizationLevel = conditional
