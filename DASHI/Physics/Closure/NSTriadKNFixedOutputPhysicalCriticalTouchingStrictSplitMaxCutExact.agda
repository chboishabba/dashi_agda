module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingStrictSplitMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B4 / GENERIC STRICT SPLIT PRODUCER
--
-- B4 needs only one common retained fraction theta < 1.  A fixed quarter
-- margin is therefore unnecessarily strong.  The literal critical-touching
-- row fold may instead be split into any two analytic pieces
--
--   rowSum = principal + defect
--
-- with relative estimates
--
--   principal <= thetaP * Mcore + cP * ED,
--   defect    <= thetaD * Mcore + cD * ED,
--
-- provided
--
--   0 <= thetaP, 0 <= thetaD, thetaP + thetaD < 1.
--
-- Then B4 closes with theta = thetaP + thetaD and ED coefficient cP+cD.
-- This is the weakest two-piece strict-margin compiler.  The Gate-2A
-- 1/6 + 1/12 = 1/4 route is one optional producer, not a prerequisite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRowOperatorMaxCutExact as RowOperator

F : C3.RealField _
F = Rational.rationalRealField

module StrictSplit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module O = RowOperator.LiteralRowOperator physicalSystem S output

  record StrictSplitRowData : Set where
    constructor strict-split-row-data
    field
      principal defect coreCompanionMass localED : ℚ
      thetaPrincipal thetaDefect : ℚ
      principalEDCoefficient defectEDCoefficient : ℚ

      thetaPrincipalNN : 0ℚ ≤ thetaPrincipal
      thetaDefectNN : 0ℚ ≤ thetaDefect
      combinedThetaStrictlyBelowOne : thetaPrincipal + thetaDefect < 1ℚ

      rowDecomposition : O.R.rowSum ≡ principal + defect

      principalBound :
        principal
        ≤ thetaPrincipal * coreCompanionMass
          + principalEDCoefficient * localED

      defectBound :
        defect
        ≤ thetaDefect * coreCompanionMass
          + defectEDCoefficient * localED

  open StrictSplitRowData public

  combinedTheta : StrictSplitRowData → ℚ
  combinedTheta D = thetaPrincipal D + thetaDefect D

  combinedEDCoefficient : StrictSplitRowData → ℚ
  combinedEDCoefficient D =
    principalEDCoefficient D + defectEDCoefficient D

  combinedThetaNN :
    (D : StrictSplitRowData) → 0ℚ ≤ combinedTheta D
  combinedThetaNN D =
    ℚP.+-mono-≤ (thetaPrincipalNN D) (thetaDefectNN D)

  strictSplitRowBound :
    (D : StrictSplitRowData) →
    O.R.rowSum
    ≤ combinedTheta D * coreCompanionMass D
      + combinedEDCoefficient D * localED D
  strictSplitRowBound D =
    let
      added :
        principal D + defect D
        ≤
        (thetaPrincipal D * coreCompanionMass D
          + principalEDCoefficient D * localED D)
        +
        (thetaDefect D * coreCompanionMass D
          + defectEDCoefficient D * localED D)
      added = ℚP.+-mono-≤ (principalBound D) (defectBound D)

      endpoint :
        (thetaPrincipal D * coreCompanionMass D
          + principalEDCoefficient D * localED D)
        +
        (thetaDefect D * coreCompanionMass D
          + defectEDCoefficient D * localED D)
        ≡
        combinedTheta D * coreCompanionMass D
          + combinedEDCoefficient D * localED D
      endpoint =
        solve
          ( thetaPrincipal D
          ∷ thetaDefect D
          ∷ coreCompanionMass D
          ∷ principalEDCoefficient D
          ∷ defectEDCoefficient D
          ∷ localED D
          ∷ [])

      paidOnDecomposition :
        principal D + defect D
        ≤ combinedTheta D * coreCompanionMass D
          + combinedEDCoefficient D * localED D
      paidOnDecomposition =
        subst
          ((principal D + defect D) ≤_)
          endpoint
          added
    in
    subst
      (λ lower →
        lower ≤ combinedTheta D * coreCompanionMass D
          + combinedEDCoefficient D * localED D)
      (sym (rowDecomposition D))
      paidOnDecomposition

  strictSplitBuildsLiteralRowCertificate :
    (D : StrictSplitRowData) →
    O.LiteralRowStrictCriticalTouchingCertificate
  strictSplitBuildsLiteralRowCertificate D = record
    { O.theta = combinedTheta D
    ; O.coreCompanionMass = coreCompanionMass D
    ; O.coreEDBudget = combinedEDCoefficient D * localED D
    ; O.thetaNN = combinedThetaNN D
    ; O.thetaStrictlyBelowOne = combinedThetaStrictlyBelowOne D
    ; O.literalRowOperatorBound = strictSplitRowBound D
    }

------------------------------------------------------------------------
-- Status / exact research seam.
------------------------------------------------------------------------

b4StrictSplitCompilerClosed : Bool
b4StrictSplitCompilerClosed = true

b4StrictSplitRequiresQuarterMargin : Bool
b4StrictSplitRequiresQuarterMargin = false

b4StrictSplitPhysicalAttachmentClosedHere : Bool
b4StrictSplitPhysicalAttachmentClosedHere = false

b4StrictSplitIntroducesEstimate : Bool
b4StrictSplitIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b4StrictSplitCompilerClosedIsTrue :
  b4StrictSplitCompilerClosed ≡ true
b4StrictSplitCompilerClosedIsTrue = refl

b4StrictSplitRequiresQuarterMarginIsFalse :
  b4StrictSplitRequiresQuarterMargin ≡ false
b4StrictSplitRequiresQuarterMarginIsFalse = refl

b4StrictSplitPhysicalAttachmentClosedHereIsFalse :
  b4StrictSplitPhysicalAttachmentClosedHere ≡ false
b4StrictSplitPhysicalAttachmentClosedHereIsFalse = refl
