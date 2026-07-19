module DASHI.Physics.Optics.PhysicalConstantsKernelClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Physical constants as authority-calibrated kernel normalisations.
--
-- This file deliberately does not claim to derive measured constants.
-- It records the algebraic closure obligations by which independently
-- supplied constants must agree across Maxwell, quantum, and gravity
-- surfaces.  Exact SI values, measured CODATA values, model laws, and
-- empirical adequacy remain distinct authority classes.

data ConstantAuthority : Set where
  exactSIDefinition : ConstantAuthority
  exactSIDerivation : ConstantAuthority
  measuredExternalInput : ConstantAuthority
  modelIdentity : ConstantAuthority

data ClosureStatus : Set where
  symbolicIdentityClosed : ClosureStatus
  numericalCalibrationRequired : ClosureStatus
  empiricalPromotionBlocked : ClosureStatus

record ConstantSlot : Set where
  field
    label : String
    symbol : String
    valueOrExpression : String
    unit : String
    authority : ConstantAuthority

open ConstantSlot public

record ClosureEquation : Set where
  field
    equationLabel : String
    leftExpression : String
    rightExpression : String
    physicalLane : String
    status : ClosureStatus
    assumptions : List String
    failureMeaning : String

open ClosureEquation public

speedOfLight : ConstantSlot
speedOfLight = record
  { label = "speed of light in vacuum"
  ; symbol = "c"
  ; valueOrExpression = "299792458"
  ; unit = "m s^-1"
  ; authority = exactSIDefinition
  }

planckConstant : ConstantSlot
planckConstant = record
  { label = "Planck constant"
  ; symbol = "h"
  ; valueOrExpression = "6.62607015e-34"
  ; unit = "J s"
  ; authority = exactSIDefinition
  }

elementaryCharge : ConstantSlot
elementaryCharge = record
  { label = "elementary charge"
  ; symbol = "e"
  ; valueOrExpression = "1.602176634e-19"
  ; unit = "C"
  ; authority = exactSIDefinition
  }

reducedPlanckConstant : ConstantSlot
reducedPlanckConstant = record
  { label = "reduced Planck constant"
  ; symbol = "hbar"
  ; valueOrExpression = "h / (2 pi)"
  ; unit = "J s"
  ; authority = exactSIDerivation
  }

fineStructureConstant : ConstantSlot
fineStructureConstant = record
  { label = "fine-structure constant"
  ; symbol = "alpha"
  ; valueOrExpression = "measured CODATA input"
  ; unit = "dimensionless"
  ; authority = measuredExternalInput
  }

newtonConstant : ConstantSlot
newtonConstant = record
  { label = "Newtonian constant of gravitation"
  ; symbol = "G"
  ; valueOrExpression = "measured CODATA input"
  ; unit = "m^3 kg^-1 s^-2"
  ; authority = measuredExternalInput
  }

maxwellWaveSpeedClosure : ClosureEquation
maxwellWaveSpeedClosure = record
  { equationLabel = "Maxwell vacuum propagation closure"
  ; leftExpression = "c^2"
  ; rightExpression = "1 / (epsilon_0 mu_0)"
  ; physicalLane = "Maxwell / SI calibration"
  ; status = symbolicIdentityClosed
  ; assumptions =
      "Lorentz-signature vacuum constitutive law"
      ∷ "epsilon_0 and mu_0 use the same SI convention"
      ∷ []
  ; failureMeaning =
      "a failed numerical equality indicates inconsistent units, rounding, or calibration; it does not refute Maxwell by itself"
  }

fineStructureClosure : ClosureEquation
fineStructureClosure = record
  { equationLabel = "electromagnetic coupling normalisation closure"
  ; leftExpression = "alpha"
  ; rightExpression = "e^2 / (4 pi epsilon_0 hbar c)"
  ; physicalLane = "QED / SI calibration"
  ; status = numericalCalibrationRequired
  ; assumptions =
      "rationalised SI convention"
      ∷ "alpha supplied by external measurement"
      ∷ []
  ; failureMeaning =
      "a failed closure indicates inconsistent authority inputs or convention mismatch"
  }

vacuumImpedanceClosure : ClosureEquation
vacuumImpedanceClosure = record
  { equationLabel = "vacuum impedance closure"
  ; leftExpression = "Z_0"
  ; rightExpression = "mu_0 c = 1 / (epsilon_0 c)"
  ; physicalLane = "Maxwell constitutive calibration"
  ; status = symbolicIdentityClosed
  ; assumptions = "Maxwell wave-speed closure" ∷ []
  ; failureMeaning = "the constitutive and propagation normalisations disagree"
  }

protonGravityCouplingClosure : ClosureEquation
protonGravityCouplingClosure = record
  { equationLabel = "dimensionless proton gravitational coupling"
  ; leftExpression = "alpha_G"
  ; rightExpression = "G m_p^2 / (hbar c)"
  ; physicalLane = "gravity / quantum dimensional comparison"
  ; status = numericalCalibrationRequired
  ; assumptions =
      "G and proton mass supplied by external measurement"
      ∷ "comparison is dimensionless, not a unification theorem"
      ∷ []
  ; failureMeaning = "input provenance, unit transport, or numerical evaluation is inconsistent"
  }

planckLengthClosure : ClosureEquation
planckLengthClosure = record
  { equationLabel = "Planck length dimensional closure"
  ; leftExpression = "ell_P^2"
  ; rightExpression = "hbar G / c^3"
  ; physicalLane = "gravity / quantum scale construction"
  ; status = symbolicIdentityClosed
  ; assumptions = "positive G, hbar, and c" ∷ []
  ; failureMeaning = "the selected dimensional convention is inconsistent"
  }

record PhysicalConstantsKernelClosure : Set where
  field
    exactInputs : List ConstantSlot
    measuredInputs : List ConstantSlot
    closureEquations : List ClosureEquation
    derivesNewMeasuredDigits : Bool
    derivesNewMeasuredDigitsIsFalse : derivesNewMeasuredDigits ≡ false
    supportsCrossConstraintAudit : Bool
    supportsCrossConstraintAuditIsTrue : supportsCrossConstraintAudit ≡ true
    empiricalPromotion : Bool
    empiricalPromotionIsFalse : empiricalPromotion ≡ false

open PhysicalConstantsKernelClosure public

canonicalPhysicalConstantsKernelClosure : PhysicalConstantsKernelClosure
canonicalPhysicalConstantsKernelClosure = record
  { exactInputs =
      speedOfLight
      ∷ planckConstant
      ∷ elementaryCharge
      ∷ reducedPlanckConstant
      ∷ []
  ; measuredInputs =
      fineStructureConstant
      ∷ newtonConstant
      ∷ []
  ; closureEquations =
      maxwellWaveSpeedClosure
      ∷ fineStructureClosure
      ∷ vacuumImpedanceClosure
      ∷ protonGravityCouplingClosure
      ∷ planckLengthClosure
      ∷ []
  ; derivesNewMeasuredDigits = false
  ; derivesNewMeasuredDigitsIsFalse = refl
  ; supportsCrossConstraintAudit = true
  ; supportsCrossConstraintAuditIsTrue = refl
  ; empiricalPromotion = false
  ; empiricalPromotionIsFalse = refl
  }
