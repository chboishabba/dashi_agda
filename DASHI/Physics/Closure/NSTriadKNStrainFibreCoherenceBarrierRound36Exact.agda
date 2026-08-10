module DASHI.Physics.Closure.NSTriadKNStrainFibreCoherenceBarrierRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the Round-36 orthogonal-mode counterexample into a whole exact
-- rational one-parameter family.  Put
--
--   k = e1,
--   l = (c,s,0),      c^2+s^2 = 1,
--
-- and choose the natural transverse bases
--
--   omega_t = e2,         eta_t = (-s,c,0),
--   omega_n = eta_n = e3.
--
-- For the normalized strain embeddings U_k = sqrt(2) S_k, the two diagonal
-- cross-fibre channels are exactly
--
--   <U_k omega_t, U_l eta_t> = c,
--   <U_k omega_n, U_l eta_n> = c^2-s^2,
--
-- while the mixed channels vanish.  More importantly their squared aggregate
-- has the exact completion-of-squares identity
--
--   c^2 + (c^2-s^2)^2
--     = 7/16 + (2(c^2-3/8))^2
--     >= 7/16.
--
-- Thus even after choosing adapted transverse bases, wave-vector angle alone
-- cannot make all cross-fibre strain channels small: this two-channel Gram
-- energy has a uniform positive floor.  The missing HH-good mechanism must
-- use spatial/PV/increment/vorticity-direction structure beyond mode angle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact as Strain
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainGramRound35Exact as Gram

threeEighths sevenSixteenths : ℚ
threeEighths = Int.+ 3 / 8
sevenSixteenths = Int.+ 7 / 16

record RationalUnitAngle : Set where
  constructor rational-unit-angle
  field
    cosine sine : ℚ
    unitCircle : cosine * cosine + sine * sine ≡ 1ℚ

open RationalUnitAngle public

leftMode : V.ProjectionMode
leftMode =
  V.projection-mode
    (V.v3 1ℚ 0ℚ 0ℚ)
    1ℚ
    (solve [])

rightMode : RationalUnitAngle → V.ProjectionMode
rightMode angle =
  V.projection-mode
    (V.v3 (cosine angle) (sine angle) 0ℚ)
    1ℚ
    inverseLaw
  where
  inverseLaw :
    1ℚ * V.normSquared (V.v3 (cosine angle) (sine angle) 0ℚ) ≡ 1ℚ
  inverseLaw =
    trans
      (solve (cosine angle ∷ sine angle ∷ []))
      (unitCircle angle)

leftTangent leftNormal : V.Vector3
leftTangent = V.v3 0ℚ 1ℚ 0ℚ
leftNormal = V.v3 0ℚ 0ℚ 1ℚ

rightTangent : RationalUnitAngle → V.Vector3
rightTangent angle =
  V.v3 (- sine angle) (cosine angle) 0ℚ

rightNormal : RationalUnitAngle → V.Vector3
rightNormal angle = V.v3 0ℚ 0ℚ 1ℚ

tangentChannel : RationalUnitAngle → ℚ
tangentChannel angle =
  Strain.two
  * Gram.frobeniusInner
      (Strain.fourierStrain leftMode leftTangent)
      (Strain.fourierStrain (rightMode angle) (rightTangent angle))

normalChannel : RationalUnitAngle → ℚ
normalChannel angle =
  Strain.two
  * Gram.frobeniusInner
      (Strain.fourierStrain leftMode leftNormal)
      (Strain.fourierStrain (rightMode angle) (rightNormal angle))

leftTangentRightNormalChannel : RationalUnitAngle → ℚ
leftTangentRightNormalChannel angle =
  Strain.two
  * Gram.frobeniusInner
      (Strain.fourierStrain leftMode leftTangent)
      (Strain.fourierStrain (rightMode angle) (rightNormal angle))

leftNormalRightTangentChannel : RationalUnitAngle → ℚ
leftNormalRightTangentChannel angle =
  Strain.two
  * Gram.frobeniusInner
      (Strain.fourierStrain leftMode leftNormal)
      (Strain.fourierStrain (rightMode angle) (rightTangent angle))

tangentChannelExact :
  ∀ angle → tangentChannel angle ≡ cosine angle
tangentChannelExact angle =
  trans
    (cong (Strain.two *_)
      (Gram.fourierStrainCrossFibreGramExact
        leftMode (rightMode angle) leftTangent (rightTangent angle)))
    (solve (cosine angle ∷ sine angle ∷ []))

normalChannelExact :
  ∀ angle →
  normalChannel angle
  ≡ cosine angle * cosine angle - sine angle * sine angle
normalChannelExact angle =
  trans
    (cong (Strain.two *_)
      (Gram.fourierStrainCrossFibreGramExact
        leftMode (rightMode angle) leftNormal (rightNormal angle)))
    (solve (cosine angle ∷ sine angle ∷ []))

leftTangentRightNormalChannelZero :
  ∀ angle → leftTangentRightNormalChannel angle ≡ 0ℚ
leftTangentRightNormalChannelZero angle =
  trans
    (cong (Strain.two *_)
      (Gram.fourierStrainCrossFibreGramExact
        leftMode (rightMode angle) leftTangent (rightNormal angle)))
    (solve (cosine angle ∷ sine angle ∷ []))

leftNormalRightTangentChannelZero :
  ∀ angle → leftNormalRightTangentChannel angle ≡ 0ℚ
leftNormalRightTangentChannelZero angle =
  trans
    (cong (Strain.two *_)
      (Gram.fourierStrainCrossFibreGramExact
        leftMode (rightMode angle) leftNormal (rightTangent angle)))
    (solve (cosine angle ∷ sine angle ∷ []))

sineSquareFromUnitCircle :
  ∀ angle →
  sine angle * sine angle ≡ 1ℚ - cosine angle * cosine angle
sineSquareFromUnitCircle angle =
  trans
    (solve (cosine angle ∷ sine angle ∷ []))
    (cong
      (λ total → total - cosine angle * cosine angle)
      (unitCircle angle))

channelEnergy : RationalUnitAngle → ℚ
channelEnergy angle =
  L2.square (tangentChannel angle) + L2.square (normalChannel angle)

channelEnergyExact :
  ∀ angle →
  channelEnergy angle
  ≡
  sevenSixteenths
  + L2.square
      (Strain.two
        * (cosine angle * cosine angle - threeEighths))
channelEnergyExact angle =
  trans
    (cong₂ _+_
      (cong L2.square (tangentChannelExact angle))
      (cong L2.square (normalChannelExact angle)))
    (trans
      (cong
        (λ sineSquare →
          L2.square (cosine angle)
          + L2.square
              (cosine angle * cosine angle - sineSquare))
        (sineSquareFromUnitCircle angle))
      (solve (cosine angle ∷ [])))

channelEnergyUniformFloor :
  ∀ angle → sevenSixteenths ≤ channelEnergy angle
channelEnergyUniformFloor angle =
  let
    defect =
      Strain.two * (cosine angle * cosine angle - threeEighths)

    defectSquareNN : 0ℚ ≤ L2.square defect
    defectSquareNN = L2.squareNonnegative defect

    lowerToCompletedSquare :
      sevenSixteenths
      ≤ sevenSixteenths + L2.square defect
    lowerToCompletedSquare =
      subst
        (λ lower → lower ≤ sevenSixteenths + L2.square defect)
        (ℚP.+-identityʳ sevenSixteenths)
        (ℚP.+-mono-≤ ℚP.≤-refl defectSquareNN)
  in
  subst
    (λ upper → sevenSixteenths ≤ upper)
    (sym (channelEnergyExact angle))
    lowerToCompletedSquare

strainFibreTwoChannelBarrierClosed : Bool
strainFibreTwoChannelBarrierClosed = true

modeAngleOnlyHHGoodMechanismRefuted : Bool
modeAngleOnlyHHGoodMechanismRefuted = true

strainFibreTwoChannelBarrierClosedIsTrue :
  strainFibreTwoChannelBarrierClosed ≡ true
strainFibreTwoChannelBarrierClosedIsTrue = refl

modeAngleOnlyHHGoodMechanismRefutedIsTrue :
  modeAngleOnlyHHGoodMechanismRefuted ≡ true
modeAngleOnlyHHGoodMechanismRefutedIsTrue = refl
