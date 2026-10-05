module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingQuarterMarginMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B4 / OPTIONAL QUARTER-MARGIN PRODUCER
--
-- The canonical B4 compiler is now the generic strict split:
--
--   rowSum = principal + defect,
--   principal <= thetaP * Mcore + cP * ED,
--   defect    <= thetaD * Mcore + cD * ED,
--   thetaP + thetaD < 1.
--
-- This file keeps the older Gate-2A-inspired choice
--
--   thetaP = 1/6, thetaD = 1/12,
--
-- as one optional concrete producer.  Since 1/6 + 1/12 = 1/4 < 1, it feeds
-- the generic strict-split compiler directly.  No NS attachment is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutExact as Strict

F : C3.RealField _
F = Rational.rationalRealField

oneSixth oneTwelfth oneQuarter one : ℚ
oneSixth = Int.+ 1 / 6
oneTwelfth = Int.+ 1 / 12
oneQuarter = Int.+ 1 / 4
one = Int.+ 1 / 1

quarterArithmetic : oneSixth + oneTwelfth ≡ oneQuarter
quarterArithmetic = solve []

sixthNN : Int.+ 0 / 1 ≤ oneSixth
sixthNN = toWitness {a? = (Int.+ 0 / 1) ℚP.≤? oneSixth} _

twelfthNN : Int.+ 0 / 1 ≤ oneTwelfth
twelfthNN = toWitness {a? = (Int.+ 0 / 1) ℚP.≤? oneTwelfth} _

quarterStrictlyBelowOne : oneSixth + oneTwelfth < one
quarterStrictlyBelowOne =
  toWitness {a? = (oneSixth + oneTwelfth) ℚP.<? one} _

module QuarterMargin
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module G = Strict.StrictSplit physicalSystem S output

  record QuarterMarginRowData : Set where
    constructor quarter-margin-row-data
    field
      principal defect coreCompanionMass localED : ℚ
      principalEDCoefficient defectEDCoefficient : ℚ

      rowDecomposition : G.O.R.rowSum ≡ principal + defect

      principalBound :
        principal
        ≤ oneSixth * coreCompanionMass
          + principalEDCoefficient * localED

      defectBound :
        defect
        ≤ oneTwelfth * coreCompanionMass
          + defectEDCoefficient * localED

  open QuarterMarginRowData public

  quarterMarginBuildsStrictSplitData :
    QuarterMarginRowData → G.StrictSplitRowData
  quarterMarginBuildsStrictSplitData D = record
    { G.principal = principal D
    ; G.defect = defect D
    ; G.coreCompanionMass = coreCompanionMass D
    ; G.localED = localED D
    ; G.thetaPrincipal = oneSixth
    ; G.thetaDefect = oneTwelfth
    ; G.principalEDCoefficient = principalEDCoefficient D
    ; G.defectEDCoefficient = defectEDCoefficient D
    ; G.thetaPrincipalNN = sixthNN
    ; G.thetaDefectNN = twelfthNN
    ; G.combinedThetaStrictlyBelowOne = quarterStrictlyBelowOne
    ; G.rowDecomposition = rowDecomposition D
    ; G.principalBound = principalBound D
    ; G.defectBound = defectBound D
    }

  quarterMarginBuildsLiteralRowCertificate :
    (D : QuarterMarginRowData) →
    G.O.LiteralRowStrictCriticalTouchingCertificate
  quarterMarginBuildsLiteralRowCertificate D =
    G.strictSplitBuildsLiteralRowCertificate
      (quarterMarginBuildsStrictSplitData D)

------------------------------------------------------------------------
-- Status / exact research seam.
------------------------------------------------------------------------

b4QuarterMarginCompilerClosed : Bool
b4QuarterMarginCompilerClosed = true

b4QuarterThetaStrictlyBelowOne : Bool
b4QuarterThetaStrictlyBelowOne = true

b4QuarterMarginUsesGenericStrictSplit : Bool
b4QuarterMarginUsesGenericStrictSplit = true

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

b4QuarterMarginUsesGenericStrictSplitIsTrue :
  b4QuarterMarginUsesGenericStrictSplit ≡ true
b4QuarterMarginUsesGenericStrictSplitIsTrue = refl

b4QuarterMarginPhysicalAttachmentClosedHereIsFalse :
  b4QuarterMarginPhysicalAttachmentClosedHere ≡ false
b4QuarterMarginPhysicalAttachmentClosedHereIsFalse = refl
