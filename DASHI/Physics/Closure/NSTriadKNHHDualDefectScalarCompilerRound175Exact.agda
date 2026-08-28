module DASHI.Physics.Closure.NSTriadKNHHDualDefectScalarCompilerRound175Exact where

------------------------------------------------------------------------
-- ROUND175 / DUAL-DEFECT SCALAR COMPILER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

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

    coefficientGapNN : 0ℚ ≤ coefficientGap
    coefficientGapNN = toWitness {a? = 0ℚ ℚP.≤? coefficientGap} _

    radialMassNN : 0ℚ ≤ radial * mass
    radialMassNN = R96.productNonnegative radialNN massNN

    extraRadialNN : 0ℚ ≤ coefficientGap * (radial * mass)
    extraRadialNN = R96.productNonnegative coefficientGapNN radialMassNN

    base = twentyFour * angular * mass + two * radial * mass
    raised = twentyFour * angular * mass + twentyFour * radial * mass

    addExtra : base ≤ base + coefficientGap * (radial * mass)
    addExtra =
      let
        zeroToExtra = extraRadialNN
        shifted = ℚP.+-monoʳ-≤ base zeroToExtra
      in subst (base ≤_) (ℚP.+-identityʳ base) shifted

    normalization :
      base + coefficientGap * (radial * mass) ≡ raised
    normalization = solve (angular ∷ radial ∷ mass ∷ [])

    raiseCoefficient : base ≤ raised
    raiseCoefficient = subst (base ≤_) normalization addExtra

    factor : raised ≡ twentyFour * (angular + radial) * mass
    factor = solve (angular ∷ radial ∷ mass ∷ [])

    finalMeaning :
      twentyFour * (angular + radial) * mass
      ≡ twentyFour * output * mass
    finalMeaning =
      subst
        (λ selected → twentyFour * (angular + radial) * mass
          ≡ twentyFour * selected * mass)
        complement refl

    raisedToFinal : raised ≡ twentyFour * output * mass
    raisedToFinal = trans factor finalMeaning
  in
  ℚP.≤-trans rawBound
    (subst (base ≤_) raisedToFinal raiseCoefficient)

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
