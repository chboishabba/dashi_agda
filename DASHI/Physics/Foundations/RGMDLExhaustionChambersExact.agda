module DASHI.Physics.Foundations.RGMDLExhaustionChambersExact where

open import DASHI.Core.Prelude

import DASHI.Core.CandidateFunctionalCore as Candidate
import DASHI.Biology.ResourceLimitedCrystallisationExact as Resource

------------------------------------------------------------------------
-- RG, MDL, and exhaustion are distinct typed processes.

data CouplingPoint : Set where
  weakCoupling : CouplingPoint
  fixedCoupling : CouplingPoint
  strongCoupling : CouplingPoint

rgStep : CouplingPoint → CouplingPoint
rgStep weakCoupling = fixedCoupling
rgStep fixedCoupling = fixedCoupling
rgStep strongCoupling = strongCoupling

isRGFixedPoint : CouplingPoint → Bool
isRGFixedPoint weakCoupling = false
isRGFixedPoint fixedCoupling = true
isRGFixedPoint strongCoupling = true

weakTrajectoryReachesFixedPoint :
  rgStep weakCoupling ≡ fixedCoupling
weakTrajectoryReachesFixedPoint = refl

fixedPointLocationDoesNotMoveWithWeakInitialDatum :
  rgStep (rgStep weakCoupling) ≡ fixedCoupling
fixedPointLocationDoesNotMoveWithWeakInitialDatum = refl

data ModelCandidate : Set where
  shortModel : ModelCandidate
  detailedModel : ModelCandidate

mdlLength : ModelCandidate → Nat
mdlLength shortModel = 3
mdlLength detailedModel = 5

mdlSelect : ModelCandidate
mdlSelect = shortModel

mdlSelectionIsThree : mdlLength mdlSelect ≡ 3
mdlSelectionIsThree = refl

data ExhaustionState : Set where
  unorderedState : ExhaustionState
  orderingState : ExhaustionState
  orderedState : ExhaustionState
  frozenState : ExhaustionState

exhaustionStep : Nat → ExhaustionState → ExhaustionState
exhaustionStep zero state = frozenState
exhaustionStep (suc fuel) unorderedState = orderingState
exhaustionStep (suc fuel) orderingState = orderedState
exhaustionStep (suc fuel) orderedState = orderedState
exhaustionStep (suc fuel) frozenState = frozenState

oneUnitStopsBeforeOrderingCompletes :
  exhaustionStep zero orderingState ≡ frozenState
oneUnitStopsBeforeOrderingCompletes = refl

twoActiveStepsReachOrder :
  exhaustionStep 1 (exhaustionStep 1 unorderedState) ≡ orderedState
twoActiveStepsReachOrder = refl

rgCarrier : Set
rgCarrier = CouplingPoint

mdlCarrier : Set
mdlCarrier = ModelCandidate

exhaustionCarrier : Set
exhaustionCarrier = ExhaustionState

existingCandidateFunctionalCarrier : Set
existingCandidateFunctionalCarrier = Candidate.CandidateFunctionalSurface

existingResourceBoundaryCarrier : Set
existingResourceBoundaryCarrier = Resource.ResourceLimitedCrystallisationBoundary

------------------------------------------------------------------------
-- Static stability, reachability before freeze-out, and robustness.

data ParameterPoint : Set where
  lowParameter : ParameterPoint
  viableParameter : ParameterPoint
  highParameter : ParameterPoint

staticViable : ParameterPoint → Bool
staticViable lowParameter = false
staticViable viableParameter = true
staticViable highParameter = true

reachableBeforeExhaustion : ParameterPoint → Bool
reachableBeforeExhaustion lowParameter = false
reachableBeforeExhaustion viableParameter = true
reachableBeforeExhaustion highParameter = false

robustlyViable : ParameterPoint → Bool
robustlyViable lowParameter = false
robustlyViable viableParameter = true
robustlyViable highParameter = false

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

fullyViable : ParameterPoint → Bool
fullyViable parameter =
  andBool
    (staticViable parameter)
    (andBool
      (reachableBeforeExhaustion parameter)
      (robustlyViable parameter))

canonicalParameterIsFullyViable :
  fullyViable viableParameter ≡ true
canonicalParameterIsFullyViable = refl

highParameterIsStableButDynamicallyUnavailable :
  staticViable highParameter ≡ true
  ×
  reachableBeforeExhaustion highParameter ≡ false
highParameterIsStableButDynamicallyUnavailable = refl , refl

------------------------------------------------------------------------
-- Phase chambers and instability boundaries.

data PhaseChamber : Set where
  symmetricChamber : PhaseChamber
  orderedChamber : PhaseChamber
  unstableChamber : PhaseChamber

parameterChamber : ParameterPoint → PhaseChamber
parameterChamber lowParameter = symmetricChamber
parameterChamber viableParameter = orderedChamber
parameterChamber highParameter = unstableChamber

crossingChangesQualitativePhase :
  parameterChamber viableParameter ≡ orderedChamber
  ×
  parameterChamber highParameter ≡ unstableChamber
crossingChangesQualitativePhase = refl , refl

------------------------------------------------------------------------
-- Correct bound-state viability: a discrete level must be certified below the
-- continuum threshold.  The witness records a nonempty discrete intersection.

data SpectralOrder : Set where
  discreteBelowContinuum : SpectralOrder
  discreteAtOrAboveContinuum : SpectralOrder

record SpectralProfile : Set where
  constructor spectralProfile
  field
    discreteEnergy : Nat
    continuumThreshold : Nat
    certifiedOrder : SpectralOrder

open SpectralProfile public

data BoundStateStatus : Set where
  boundStatePresent : BoundStateStatus
  noCertifiedBoundState : BoundStateStatus

boundStateStatus : SpectralProfile → BoundStateStatus
boundStateStatus (spectralProfile energy threshold discreteBelowContinuum) =
  boundStatePresent
boundStateStatus (spectralProfile energy threshold discreteAtOrAboveContinuum) =
  noCertifiedBoundState

canonicalBoundProfile : SpectralProfile
canonicalBoundProfile =
  spectralProfile 0 3 discreteBelowContinuum

canonicalBoundStateIsPresent :
  boundStateStatus canonicalBoundProfile ≡ boundStatePresent
canonicalBoundStateIsPresent = refl

------------------------------------------------------------------------
-- Avoided-crossing discriminant.
--
-- For a two-level Hermitian operator the squared eigenvalue gap is
-- (E_old-E_new)^2 + 4 |v|^2.  We retain an exact Nat-valued finite witness.

natDistance : Nat → Nat → Nat
natDistance x y = (x ∸ y) + (y ∸ x)

gapSquare : Nat → Nat → Nat → Nat
gapSquare oldEnergy newEnergy coupling =
  natDistance oldEnergy newEnergy * natDistance oldEnergy newEnergy
  +
  4 * (coupling * coupling)

exactDegeneracyWithoutCoupling : gapSquare 5 5 0 ≡ 0
exactDegeneracyWithoutCoupling = refl

couplingOpensGapSquareSixteen : gapSquare 5 5 2 ≡ 16
couplingOpensGapSquareSixteen = refl

------------------------------------------------------------------------
-- Authority boundary.

record RGMDLExhaustionBoundary : Set where
  constructor rgmdlExhaustionBoundary
  field
    rgFlowDefinitionallyEqualsMDLSelection : Bool
    rgFlowDefinitionallyEqualsMDLSelectionIsFalse :
      rgFlowDefinitionallyEqualsMDLSelection ≡ false

    mdlSelectionDefinitionallyEqualsResourceDynamics : Bool
    mdlSelectionDefinitionallyEqualsResourceDynamicsIsFalse :
      mdlSelectionDefinitionallyEqualsResourceDynamics ≡ false

    fixedPointLocationIsChosenByInitialCondition : Bool
    fixedPointLocationIsChosenByInitialConditionIsFalse :
      fixedPointLocationIsChosenByInitialCondition ≡ false

    staticStabilityImpliesFormationBeforeFreezeOut : Bool
    staticStabilityImpliesFormationBeforeFreezeOutIsFalse :
      staticStabilityImpliesFormationBeforeFreezeOut ≡ false

    finiteBoundStateWitnessProvesContinuumSpectrumTheorem : Bool
    finiteBoundStateWitnessProvesContinuumSpectrumTheoremIsFalse :
      finiteBoundStateWitnessProvesContinuumSpectrumTheorem ≡ false

open RGMDLExhaustionBoundary public

canonicalRGMDLExhaustionBoundary : RGMDLExhaustionBoundary
canonicalRGMDLExhaustionBoundary =
  rgmdlExhaustionBoundary false refl false refl false refl false refl false refl
