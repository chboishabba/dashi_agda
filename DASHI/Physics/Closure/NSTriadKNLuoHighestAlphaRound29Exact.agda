module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound29Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Integrate the highest-alpha Round-29 exports without promoting any open
-- physical estimate. This tranche makes the finite-flow state dependent,
-- separates continuation from energy, derives five sources from one global
-- pairing, delays positive taxation, exposes cross-shell almost orthogonality,
-- makes HH-bad feasibility falsifiable, retains symbolic owner costs, classifies
-- boundary limits, and names the compactness/Serrin quantitative reducers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact as Selector
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNDependentPhysicalODECarrierRound29Exact as Dependent
import DASHI.Physics.Closure.NSTriadKNFiniteFlowBlowupAlternativeRound29Exact as Flow
import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNDelayedPositivePartRound29Exact as Positive
import DASHI.Physics.Closure.NSTriadKNDiscreteMultiplierTelescopingRound29Exact as Multiplier
import DASHI.Physics.Closure.NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact as CrossShell
import DASHI.Physics.Closure.NSTriadKNScaleNormalisedAmplitudeAuditRound29Exact as Amplitude
import DASHI.Physics.Closure.NSTriadKNHHBadFeasibilityRound29Exact as HHBad
import DASHI.Physics.Closure.NSTriadKNAffineOwnerCostOptimizationRound29Exact as Costs
import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Serrin
import DASHI.Physics.Closure.NSTriadKNLuoUniformCommutatorTaxRound27Exact as UniformCom
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyContinuationRound27Exact as EnergyBridge
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Language

record Round29ExactEvidence : Set₁ where
  field
    dependentPhysicalVectorField :
      ∀ {State : Set}
        {selectors : Selector.CommutingPhysicalSelectors State} →
      Dependent.SelectorEquivariantVectorField selectors →
      Selector.PhysicalCarrier selectors →
      Selector.PhysicalCarrier selectors

    finiteEnergyExcludesEscape :
      ∀ {Time State : Set}
        {trajectory : Flow.FiniteNormTrajectory Time State}
        (alternative : Flow.FiniteBlowupAlternative trajectory) →
      Flow.EnergyControl trajectory →
      Flow.FiniteMaximalTime alternative → ⊥

    globalFiveSourcePairing :
      (pairing : Shell.StaticPhysicalShellPairing) →
      Shell.globalBilinearPairing pairing
      ≡ Shell.hhValue pairing + Shell.lhValue pairing
        + Shell.hlValue pairing + Shell.ccValue pairing
        + Shell.comValue pairing

    delayedSignedMagnitude :
      (values : List ℚ) →
      ∣ Positive.signedSum values ∣
      ≤ Positive.atomwiseMagnitude values

    discreteMultiplierDifference :
      (current : ℚ) →
      (path : List ℚ) →
      current - Multiplier.terminalSample current path
      ≡ Multiplier.telescopingDifference current path

    finiteCrossShellAlmostOrthogonality :
      (cells : List CrossShell.SignedCrossShellCell) →
      (certificate : CrossShell.CrossShellDecayCertificate cells) →
      ∣ CrossShell.sumSignedPairings cells ∣
      ≤ CrossShell.commonConstant certificate
        * CrossShell.decayMass certificate

    criticalAmplitudeHomogeneity :
      (candidate : Amplitude.ParameterisedBadAmplitudeCandidate) →
      Amplitude.candidateAmplitude candidate
      ≡ Amplitude.quadraticDiffusionScale
          (Amplitude.scale candidate)
          (Amplitude.shellEnergy candidate)

    hhBadUnavoidableFloorNoGo :
      (order : HHBad.BudgetOrder) →
      (costs : HHBad.HHBadCostData) →
      (feasible : HHBad.HHBadFeasible order costs) →
      HHBad.HHBadUnavoidableFloor order costs feasible → ⊥

    symbolicBudgetPromotion :
      ∀ {environment}
        (costs : List (Costs.SymbolicOwnerCost environment)) →
      Costs.SymbolicStrictBudget costs →
      Language.StrictAdmissibleOwnerBudget
        (Costs.mapSymbolicOwnerCosts costs)

    boundaryReasonPartition :
      (atoms : List Boundary.BoundaryAtom) →
      Boundary.boundaryTotal atoms
      ≡ Boundary.reasonTotal Boundary.exactAbsence atoms
        + Boundary.reasonTotal Boundary.fixedCutoffFiniteSupport atoms
        + Boundary.reasonTotal Boundary.geometricTail atoms
        + Boundary.reasonTotal Boundary.strongConvergence atoms
        + Boundary.reasonTotal Boundary.dominatedConvergence atoms

    quantitativeCriticalToSerrin :
      (budget : Serrin.CriticalToSerrinBudget) →
      Serrin.integralL6Fourth budget
      ≤ Serrin.sobolevConstantFourth budget
        * (Serrin.supHOneHalfSquared budget
          * Serrin.integralHThreeHalfSquared budget)

open Round29ExactEvidence public

canonicalRound29ExactEvidence : Round29ExactEvidence
canonicalRound29ExactEvidence = record
  { dependentPhysicalVectorField = Dependent.physicalVectorField
  ; finiteEnergyExcludesEscape = Flow.energyExcludesFiniteMaximalTime
  ; globalFiveSourcePairing = Shell.globalPairingFiveSourceIdentity
  ; delayedSignedMagnitude = Positive.delayedMagnitudeBelowAtomwiseMagnitude
  ; discreteMultiplierDifference =
      Multiplier.multiplierDifferenceIsSignedPathSum
  ; finiteCrossShellAlmostOrthogonality =
      CrossShell.finiteAlmostOrthogonalityBound
  ; criticalAmplitudeHomogeneity =
      Amplitude.candidateHasCriticalHomogeneity
  ; hhBadUnavoidableFloorNoGo =
      HHBad.unavoidableFloorRefutesCurrentHHBadFamily
  ; symbolicBudgetPromotion =
      Costs.symbolicBudgetProducesStrictAdmissibleBudget
  ; boundaryReasonPartition = Boundary.boundaryReasonPartitionExact
  ; quantitativeCriticalToSerrin = Serrin.criticalToSerrinQuantitative
  }

record Round29HighestAlphaBoundary : Set where
  constructor round29-highest-alpha-boundary
  field
    reconstructedPhysicalStateSelector : Bool
    dependentPhysicalODECarrier : Bool
    finiteCommutatorCoefficient : Bool
    finiteEnergyContinuationBridge : Bool
    globalFiveSourcePairing : Bool
    delayedPositivePart : Bool
    discreteMultiplierTelescoping : Bool
    crossShellScalarCore : Bool
    scaleNormalisedAmplitudeAudit : Bool
    hhBadFeasibilityCriterion : Bool
    symbolicOwnerOptimization : Bool
    boundaryVanishingClassification : Bool
    quantitativeCriticalToSerrinReducer : Bool

    fullNonlinearRealityEquivariance : Bool
    continuumRealPicardLindelof : Bool
    physicalEnergyIdentity : Bool
    finiteGlobalGalerkinFlow : Bool
    physicalTimeDependentShellBalance : Bool
    cutoffUniformOperatorCotlarStein : Bool
    physicalHHBadParameterTuple : Bool
    physicalNineOwnerEstimates : Bool
    strictTotalViscosityMargin : Bool
    shellAndGalerkinLimits : Bool
    periodicSerrinContinuation : Bool
    unconditionalClayTheorem : Bool

open Round29HighestAlphaBoundary public

canonicalRound29HighestAlphaBoundary : Round29HighestAlphaBoundary
canonicalRound29HighestAlphaBoundary =
  round29-highest-alpha-boundary
    true true true true true true true true true true true true true
    false false false false false false false false false false false false

finiteArchitectureAdvanced :
  dependentPhysicalODECarrier canonicalRound29HighestAlphaBoundary ≡ true
finiteArchitectureAdvanced = refl

physicalFlowStillOpen :
  finiteGlobalGalerkinFlow canonicalRound29HighestAlphaBoundary ≡ false
physicalFlowStillOpen = refl

uniformOperatorStillOpen :
  cutoffUniformOperatorCotlarStein canonicalRound29HighestAlphaBoundary ≡ false
uniformOperatorStillOpen = refl

physicalTaxesStillOpen :
  physicalNineOwnerEstimates canonicalRound29HighestAlphaBoundary ≡ false
physicalTaxesStillOpen = refl

strictMarginStillOpen :
  strictTotalViscosityMargin canonicalRound29HighestAlphaBoundary ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayTheorem canonicalRound29HighestAlphaBoundary ≡ false
clayPromotionStillFalse = refl
