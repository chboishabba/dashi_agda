{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440LiteralUniformTargetExact where

------------------------------------------------------------------------
-- CANONICAL B4 / LITERAL UNIFORM PHYSICAL R440 OPEN LEMMA
--
-- This is the next contraction after NSCanonicalB4PhysicalR440UniformTarget:
-- remove the abstract observable parameters themselves.
--
-- The three quantities in the inequality are now definitionally the existing
-- physical objects:
--
--   signedWork = literal Core-noncore defect, already welded to
--                -W(M , R440 residual),
--   coreMass   = literal Young companion on the actual Core-Core rows,
--   localED    = literal selected-pair modal E*D fold on the same output fibre.
--
-- The Boolean pair selector is ONE fixed parameter for the whole family.  This
-- matches the existing UniformFamily/R469/R219 compiler: the selector need not
-- be canonical, but it may not vary with state, cutoff, or output.
--
-- The only free quantitative data are therefore two rational constants
-- thetaD and cD.  The target requires
--
--   0 <= thetaD < 1/2,
--   0 <= cD,
--
-- and, for every physical finite Galerkin system with nonnegative viscosity,
-- every helical scalar package and every output mode,
--
--   defect_R440 <= thetaD * M_core + cD * localED.
--
-- Core-mass and local-ED nonnegativity are also explicit invariants.  No sign
-- condition is imposed on the defect itself: it is a signed covariance term.
--
-- No cutoff admissibility predicate is needed here: the cutoff is the literal
-- Audit.cutoff carried by PhysicalFiniteComplex3GalerkinSystem, and the local
-- ED/output-fibre definitions use that cutoff definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; _<_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact as R469
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Exact as Companion
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact as DefectR440

F : C3.RealField _
F = Rational.rationalRealField

oneHalf : ℚ
oneHalf = Int.+ 1 / 2

------------------------------------------------------------------------
-- Literal observables.
------------------------------------------------------------------------

literalSignedR440Work :
  Field30.PhysicalFiniteComplex3GalerkinSystem F →
  Helical.HelicalModeScalars F →
  Z3.FourierMode → ℚ
literalSignedR440Work physicalSystem S output =
  let module D = DefectR440.LiveDefectR440 physicalSystem S output
  in D.N.R.defect

literalSignedR440WorkIsNegativeR440Work :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (output : Z3.FourierMode) →
  let module D = DefectR440.LiveDefectR440 physicalSystem S output
  in literalSignedR440Work physicalSystem S output
     ≡ 0ℚ - Work.coherentWork (D.Live.mixed output) D.physicalResidual
literalSignedR440WorkIsNegativeR440Work physicalSystem S output =
  let module D = DefectR440.LiveDefectR440 physicalSystem S output
  in D.defectIsNegativePhysicalR440Work

literalCoreCompanionMass :
  Field30.PhysicalFiniteComplex3GalerkinSystem F →
  Helical.HelicalModeScalars F →
  Z3.FourierMode → ℚ
literalCoreCompanionMass physicalSystem S output =
  let module C = Companion.LiveLiteralCompanion physicalSystem S output
  in C.coreCompanionMass

literalSelectedPairLocalED :
  Field30.PhysicalFiniteComplex3GalerkinSystem F →
  (Z3.FourierMode → Z3.FourierMode → Bool) →
  Z3.FourierMode → ℚ
literalSelectedPairLocalED physicalSystem select output =
  let
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    system = Field30.finiteSystem physicalSystem
    velocity = Audit.velocity system
    cutoff = Audit.cutoff system
  in
  R38.foldPower
    (R469.selectedTriadValue
      (R219.physicalModalED E I velocity) select)
    (Output.physicalOutputFiber cutoff output)

------------------------------------------------------------------------
-- Exact typed AST for the remaining B4 theorem.
------------------------------------------------------------------------

record CanonicalB4PhysicalR440LiteralUniformTarget
    (select : Z3.FourierMode → Z3.FourierMode → Bool)
    (thetaD cD : ℚ) : Set₁ where
  field
    ----------------------------------------------------------------------
    -- GLOBAL CONSTANT BOUNDS.
    ----------------------------------------------------------------------

    thetaDNonnegative :
      0ℚ ≤ thetaD

    thetaDStrictlyBelowHalf :
      thetaD < oneHalf

    defectEDCoefficientNonnegative :
      0ℚ ≤ cD

    ----------------------------------------------------------------------
    -- NONNEGATIVITY OF THE TWO POSITIVE CURRENCIES.
    ----------------------------------------------------------------------

    literalCoreCompanionMassNonnegative :
      (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
      (S : Helical.HelicalModeScalars F) →
      (output : Z3.FourierMode) →
      0ℚ ≤ literalCoreCompanionMass physicalSystem S output

    literalSelectedPairLocalEDNonnegative :
      (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
      (output : Z3.FourierMode) →
      0ℚ ≤ literalSelectedPairLocalED physicalSystem select output

    ----------------------------------------------------------------------
    -- KEY OPEN LEMMA.
    --
    -- thetaD, cD and select occur outside the physical-system/S/output
    -- quantifiers, so state/cutoff/output uniformity is structural.
    -- Nonnegative viscosity is an explicit premise because the physical
    -- system record itself deliberately does not impose it.
    ----------------------------------------------------------------------

    uniformLiteralPhysicalR440DefectPayment :
      (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
      0ℚ ≤ Field30.viscosity physicalSystem →
      (S : Helical.HelicalModeScalars F) →
      (output : Z3.FourierMode) →
      literalSignedR440Work physicalSystem S output
      ≤ thetaD * literalCoreCompanionMass physicalSystem S output
        + cD * literalSelectedPairLocalED physicalSystem select output

open CanonicalB4PhysicalR440LiteralUniformTarget public

------------------------------------------------------------------------
-- Public theorem-name alias.
------------------------------------------------------------------------

B4LiteralPhysicalR440KeyOpenLemma :
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  (thetaD cD : ℚ) → Set₁
B4LiteralPhysicalR440KeyOpenLemma =
  CanonicalB4PhysicalR440LiteralUniformTarget

------------------------------------------------------------------------
-- Explicit invariant ledger.
------------------------------------------------------------------------

b4LiteralTargetFixesSignedR440Work : Bool
b4LiteralTargetFixesSignedR440Work = true

b4LiteralTargetFixesCoreCompanionMass : Bool
b4LiteralTargetFixesCoreCompanionMass = true

b4LiteralTargetFixesSelectedPairLocalED : Bool
b4LiteralTargetFixesSelectedPairLocalED = true

b4LiteralTargetUsesOneFixedSelectorPerFamily : Bool
b4LiteralTargetUsesOneFixedSelectorPerFamily = true

b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystems : Bool
b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystems = true

b4LiteralTargetRequiresNonnegativeViscosity : Bool
b4LiteralTargetRequiresNonnegativeViscosity = true

b4LiteralTargetRequiresCoreMassNonnegative : Bool
b4LiteralTargetRequiresCoreMassNonnegative = true

b4LiteralTargetRequiresLocalEDNonnegative : Bool
b4LiteralTargetRequiresLocalEDNonnegative = true

b4LiteralUniformPhysicalR440PaymentClosed : Bool
b4LiteralUniformPhysicalR440PaymentClosed = false

clayPromotion : Bool
clayPromotion = false

b4LiteralTargetFixesSignedR440WorkIsTrue :
  b4LiteralTargetFixesSignedR440Work ≡ true
b4LiteralTargetFixesSignedR440WorkIsTrue = refl

b4LiteralTargetFixesCoreCompanionMassIsTrue :
  b4LiteralTargetFixesCoreCompanionMass ≡ true
b4LiteralTargetFixesCoreCompanionMassIsTrue = refl

b4LiteralTargetFixesSelectedPairLocalEDIsTrue :
  b4LiteralTargetFixesSelectedPairLocalED ≡ true
b4LiteralTargetFixesSelectedPairLocalEDIsTrue = refl

b4LiteralTargetUsesOneFixedSelectorPerFamilyIsTrue :
  b4LiteralTargetUsesOneFixedSelectorPerFamily ≡ true
b4LiteralTargetUsesOneFixedSelectorPerFamilyIsTrue = refl

b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystemsIsTrue :
  b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystems ≡ true
b4LiteralTargetThetaAndCoefficientUniformAcrossPhysicalSystemsIsTrue = refl

b4LiteralTargetRequiresNonnegativeViscosityIsTrue :
  b4LiteralTargetRequiresNonnegativeViscosity ≡ true
b4LiteralTargetRequiresNonnegativeViscosityIsTrue = refl

b4LiteralTargetRequiresCoreMassNonnegativeIsTrue :
  b4LiteralTargetRequiresCoreMassNonnegative ≡ true
b4LiteralTargetRequiresCoreMassNonnegativeIsTrue = refl

b4LiteralTargetRequiresLocalEDNonnegativeIsTrue :
  b4LiteralTargetRequiresLocalEDNonnegative ≡ true
b4LiteralTargetRequiresLocalEDNonnegativeIsTrue = refl

b4LiteralUniformPhysicalR440PaymentClosedIsFalse :
  b4LiteralUniformPhysicalR440PaymentClosed ≡ false
b4LiteralUniformPhysicalR440PaymentClosedIsFalse = refl
