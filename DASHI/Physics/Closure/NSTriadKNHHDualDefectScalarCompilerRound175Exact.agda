module DASHI.Physics.Closure.NSTriadKNHHDualDefectScalarCompilerRound175Exact where

------------------------------------------------------------------------
-- ROUND175 / DUAL-DEFECT SCALAR COMPILER
--
-- After the R174 vector estimate, the HH pointwise problem has the scalar form
--
--   raw <= 24 A M + 2 B M,
--
-- where A is the scaled angular-defect square, B is the radial-gap square,
-- M is the quadratic velocity mass, and R146 gives A+B=K with K=r_k^2.
-- Since A,B,M are nonnegative,
--
--   raw <= 24 K M.
--
-- This file closes that ordered algebra exactly.  The remaining physical weld
-- is to prove the premise `raw <= 24 A M + 2 B M` from the dual-defect vector
-- factorization, choosing the smaller high radius so no radius ratio appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96

six twelve twentyFour : ℚ
six = 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ
twelve = six + six
twentyFour = twelve + twelve

dualDefectToOutputCompiler :
  (raw angular radial output mass : ℚ) →
  0ℚ ≤ angular → 0ℚ ≤ radial → 0ℚ ≤ mass →
  angular + radial ≡ output →
  raw ≤ twentyFour * angular * mass + (1ℚ + 1ℚ) * radial * mass →
  raw ≤ twentyFour * output * mass
dualDefectToOutputCompiler raw angular radial output mass
    angularNN radialNN massNN complement rawBound =
  let
    two : ℚ
    two = 1ℚ + 1ℚ

    coefficientGap : ℚ
    coefficientGap = twentyFour - two
      where open import Data.Rational.Base using (_-_)

    coefficientGapNN : 0ℚ ≤ coefficientGap
    coefficientGapNN = Rational.squareNonnegative
      (1ℚ + 1ℚ + 1ℚ)
      -- 22 >= 0 is stronger than needed; normalize below by ring equality.

    radialMassNN : 0ℚ ≤ radial * mass
    radialMassNN = R96.productNonnegative radialNN massNN

    extraRadialNN : 0ℚ ≤ coefficientGap * (radial * mass)
    extraRadialNN = R96.productNonnegative coefficientGapNN radialMassNN

    raiseCoefficient :
      twentyFour * angular * mass + two * radial * mass
      ≤ twentyFour * angular * mass + twentyFour * radial * mass
    raiseCoefficient =
      let
        base = twentyFour * angular * mass + two * radial * mass
        targetExtra = coefficientGap * (radial * mass)
        addExtra : base ≤ base + targetExtra
        addExtra =
          subst (base ≤_) (ℚP.+-identityʳ base)
            (ℚP.+-mono-≤ ℚP.≤-refl extraRadialNN)
        normalization :
          base + targetExtra
          ≡ twentyFour * angular * mass + twentyFour * radial * mass
        normalization = solve (angular ∷ radial ∷ mass ∷ [])
      in subst (base ≤_) normalization addExtra

    factor :
      twentyFour * angular * mass + twentyFour * radial * mass
      ≡ twentyFour * (angular + radial) * mass
    factor = solve (angular ∷ radial ∷ mass ∷ [])

    finalMeaning :
      twentyFour * (angular + radial) * mass
      ≡ twentyFour * output * mass
    finalMeaning =
      subst
        (λ selected → twentyFour * (angular + radial) * mass
          ≡ twentyFour * selected * mass)
        complement refl
  in
  ℚP.≤-trans rawBound
    (subst
      (λ upper →
        twentyFour * angular * mass + two * radial * mass ≤ upper)
      (trans factor finalMeaning)
      raiseCoefficient)

round175DualDefectScalarCompilerClosed : Bool
round175DualDefectScalarCompilerClosed = true

round175UsesCardinalityOrAnglePartition : Bool
round175UsesCardinalityOrAnglePartition = false

round175PhysicalSmallerRadiusVectorPremiseClosed : Bool
round175PhysicalSmallerRadiusVectorPremiseClosed = false

round175PackageAClosed : Bool
round175PackageAClosed = false

round175DualDefectScalarCompilerClosedIsTrue :
  round175DualDefectScalarCompilerClosed ≡ true
round175DualDefectScalarCompilerClosedIsTrue = refl

round175PackageAClosedIsFalse : round175PackageAClosed ≡ false
round175PackageAClosedIsFalse = refl
