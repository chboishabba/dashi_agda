module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B4 / QUARTER-MARGIN ROW PRODUCER
--
-- The literal critical-touching row operator is already the exact B4 carrier.
-- This owner isolates one useful analytic route suggested by the existing
-- Gate-2A quarter-margin programme:
--
--   rowSum = principal + defect,
--   principal <= (1/6) * Mcore + cP * ED,
--   defect    <= (1/12) * Mcore + cD * ED.
--
-- Then, on the SAME literal carrier,
--
--   rowSum <= (1/4) * Mcore + (cP+cD) * ED,
--
-- and 1/4 < 1 supplies the strict B4 margin automatically.
--
-- This file proves only that compiler.  The principal/defect estimates and the
-- physical decomposition of the literal row sum remain the genuine NS input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP using (_≤?_; _<?_; +-mono-≤)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRowOperatorMaxCutExact as RowOperator

F : C3.RealField _
F = Rational.rationalRealField

oneSixth oneTwelfth oneQuarter one : ℚ
oneSixth = Int.+ 1 / 6
oneTwelfth = Int.+ 1 / 12
oneQuarter = Int.+ 1 / 4
one = Int.+ 1 / 1

quarterArithmetic : oneSixth + oneTwelfth ≡ oneQuarter
quarterArithmetic = solve []

quarterNN : Int.+ 0 / 1 ≤ oneQuarter
quarterNN = toWitness {a? = (Int.+ 0 / 1) ℚP.≤? oneQuarter} _

quarterStrictlyBelowOne : oneQuarter < one
quarterStrictlyBelowOne = toWitness {a? = oneQuarter ℚP.<? one} _

module QuarterMargin
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module O = RowOperator.LiteralRowOperator physicalSystem S output

  record QuarterMarginRowData : Set where
    constructor quarter-margin-row-data
    field
      principal defect coreCompanionMass localED : ℚ
      principalEDCoefficient defectEDCoefficient : ℚ

      rowDecomposition : O.R.rowSum ≡ principal + defect

      principalBound :
        principal
        ≤ oneSixth * coreCompanionMass
          + principalEDCoefficient * localED

      defectBound :
        defect
        ≤ oneTwelfth * coreCompanionMass
          + defectEDCoefficient * localED

  open QuarterMarginRowData public

  combinedEDCoefficient : QuarterMarginRowData → ℚ
  combinedEDCoefficient D =
    principalEDCoefficient D + defectEDCoefficient D

  quarterMarginRowBound :
    (D : QuarterMarginRowData) →
    O.R.rowSum
    ≤ oneQuarter * coreCompanionMass D
      + combinedEDCoefficient D * localED D
  quarterMarginRowBound D =
    let
      added :
        principal D + defect D
        ≤
        (oneSixth * coreCompanionMass D
          + principalEDCoefficient D * localED D)
        +
        (oneTwelfth * coreCompanionMass D
          + defectEDCoefficient D * localED D)
      added = ℚP.+-mono-≤ (principalBound D) (defectBound D)

      endpoint :
        (oneSixth * coreCompanionMass D
          + principalEDCoefficient D * localED D)
        +
        (oneTwelfth * coreCompanionMass D
          + defectEDCoefficient D * localED D)
        ≡
        oneQuarter * coreCompanionMass D
          + combinedEDCoefficient D * localED D
      endpoint =
        solve
          ( coreCompanionMass D
          ∷ principalEDCoefficient D
          ∷ defectEDCoefficient D
          ∷ localED D
          ∷ [])

      paidOnDecomposition :
        principal D + defect D
        ≤ oneQuarter * coreCompanionMass D
          + combinedEDCoefficient D * localED D
      paidOnDecomposition =
        subst
          ((principal D + defect D) ≤_)
          endpoint
          added
    in
    subst
      (λ lower →
        lower ≤ oneQuarter * coreCompanionMass D
          + combinedEDCoefficient D * localED D)
      (sym (rowDecomposition D))
      paidOnDecomposition

  quarterMarginBuildsLiteralRowCertificate :
    (D : QuarterMarginRowData) →
    O.LiteralRowStrictCriticalTouchingCertificate
  quarterMarginBuildsLiteralRowCertificate D = record
    { O.theta = oneQuarter
    ; O.coreCompanionMass = coreCompanionMass D
    ; O.coreEDBudget = combinedEDCoefficient D * localED D
    ; O.thetaNN = quarterNN
    ; O.thetaStrictlyBelowOne = quarterStrictlyBelowOne
    ; O.literalRowOperatorBound = quarterMarginRowBound D
    }

------------------------------------------------------------------------
-- Status / exact research seam.
------------------------------------------------------------------------

b4QuarterMarginCompilerClosed : Bool
b4QuarterMarginCompilerClosed = true

b4QuarterThetaStrictlyBelowOne : Bool
b4QuarterThetaStrictlyBelowOne = true

b4QuarterMarginPhysicalAttachmentClosedHere : Bool
b4QuarterMarginPhysicalAttachmentClosedHere = false

b4QuarterMarginIntroducesEstimate : Bool
b4QuarterMarginIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b4QuarterMarginCompilerClosedIsTrue :
  b4QuarterMarginCompilerClosed ≡ true
b4QuarterMarginCompilerClosedIsTrue = refl

b4QuarterThetaStrictlyBelowOneIsTrue :
  b4QuarterThetaStrictlyBelowOne ≡ true
b4QuarterThetaStrictlyBelowOneIsTrue = refl

b4QuarterMarginPhysicalAttachmentClosedHereIsFalse :
  b4QuarterMarginPhysicalAttachmentClosedHere ≡ false
b4QuarterMarginPhysicalAttachmentClosedHereIsFalse = refl
