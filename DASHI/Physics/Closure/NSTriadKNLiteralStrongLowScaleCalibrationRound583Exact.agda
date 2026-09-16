module DASHI.Physics.Closure.NSTriadKNLiteralStrongLowScaleCalibrationRound583Exact where

------------------------------------------------------------------------
-- ROUND583 / SAME-OBJECT REPAIR FOR THE R329 STRONG-LOW SCALE RECEIPT
--
-- R319 says its variables are dyadic shell exponents:
--
--   p = inner output / outer forcing shell,
--   M = inner high shell.
--
-- R321 stores those exponents as rationals, but R329 currently accepts an
-- arbitrary R321.StronglyLowInnerOutput with no equality tying the stored
-- values to the literal inner/outer Fourier modes.
--
-- This file defines the literal physical values using the canonical dyadic
-- Shell.shellIndex and a canonical Nat -> rational embedding.  The inner high
-- shell is the maximum of the two literal inner input shells.
--
-- A corrected R329 cell must carry a calibration receipt showing that the
-- stored R321 scales are exactly these physical values.  No new inequality is
-- assumed: when the physical 3 p <= 2 M theorem is supplied, the helper below
-- constructs the corresponding R321 receipt on the exact literal scales.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNInnerStrongLowOutputSubconeRound321Exact as R321
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

F : C3.RealField _
F = Rational.rationalRealField

natToRational583 : Nat → ℚ
natToRational583 zero = 0ℚ
natToRational583 (suc n) = natToRational583 n + 1ℚ

natMax583 : Nat → Nat → Nat
natMax583 zero n = n
natMax583 (suc m) zero = suc m
natMax583 (suc m) (suc n) = suc (natMax583 m n)

literalOuterForcingShell583 :
  Physical.PhysicalTriadIncidence → ℚ
literalOuterForcingShell583 outer =
  natToRational583 (Shell.shellIndex (Physical.p outer))

literalInnerHighShell583 :
  Physical.PhysicalTriadIncidence → ℚ
literalInnerHighShell583 inner =
  natToRational583
    (natMax583
      (Shell.shellIndex (Physical.p inner))
      (Shell.shellIndex (Physical.q inner)))

literalStrongLowReceipt583 :
  (inner outer : Physical.PhysicalTriadIncidence) →
  3 * literalOuterForcingShell583 outer
    ≤ 2 * literalInnerHighShell583 inner →
  R321.StronglyLowInnerOutput
literalStrongLowReceipt583 inner outer physicalStrongLow =
  R321.strongly-low-inner-output
    (literalOuterForcingShell583 outer)
    (literalInnerHighShell583 inner)
    physicalStrongLow

record LiteralStrongLowScaleCalibration583
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) : Set where
  constructor literal-strong-low-scale-calibration583
  field
    pScaleSameObject583 :
      R321.pShell (R329.strongLow C)
      ≡ literalOuterForcingShell583 (R329.outer C)
    innerHighScaleSameObject583 :
      R321.innerHighShell (R329.strongLow C)
      ≡ literalInnerHighShell583 (R329.inner C)

open LiteralStrongLowScaleCalibration583 public

-- The existing R329 record does not require this calibration.  Therefore it
-- must remain an explicit first residual for consumers that interpret R329's
-- strongLow field physically.

data LiteralStrongLowCalibrationResidual583 : Set where
  missingLiteralR329StrongLowScaleCalibration583 :
    LiteralStrongLowCalibrationResidual583
  missingPhysicalStrongLowInequality583 :
    LiteralStrongLowCalibrationResidual583

currentResidual583 : LiteralStrongLowCalibrationResidual583
currentResidual583 = missingLiteralR329StrongLowScaleCalibration583

round583R319ScaleSemanticsRecovered : Bool
round583R319ScaleSemanticsRecovered = true

round583CanonicalLiteralScaleFunctionsConstructed : Bool
round583CanonicalLiteralScaleFunctionsConstructed = true

round583SourceNativeStrongLowConstructorConstructed : Bool
round583SourceNativeStrongLowConstructorConstructed = true

round583ExistingR329StrongLowPhysicallyCalibrated : Bool
round583ExistingR329StrongLowPhysicallyCalibrated = false

round583PhysicalStrongLowInequalityClosedForAllR329Cells : Bool
round583PhysicalStrongLowInequalityClosedForAllR329Cells = false

round583LeafAClosed : Bool
round583LeafAClosed = false

round583ClayPromotion : Bool
round583ClayPromotion = false

round583R319ScaleSemanticsRecoveredIsTrue :
  round583R319ScaleSemanticsRecovered ≡ true
round583R319ScaleSemanticsRecoveredIsTrue = refl

round583CanonicalLiteralScaleFunctionsConstructedIsTrue :
  round583CanonicalLiteralScaleFunctionsConstructed ≡ true
round583CanonicalLiteralScaleFunctionsConstructedIsTrue = refl

round583SourceNativeStrongLowConstructorConstructedIsTrue :
  round583SourceNativeStrongLowConstructorConstructed ≡ true
round583SourceNativeStrongLowConstructorConstructedIsTrue = refl

round583ExistingR329StrongLowPhysicallyCalibratedIsFalse :
  round583ExistingR329StrongLowPhysicallyCalibrated ≡ false
round583ExistingR329StrongLowPhysicallyCalibratedIsFalse = refl

round583ClayPromotionIsFalse : round583ClayPromotion ≡ false
round583ClayPromotionIsFalse = refl
