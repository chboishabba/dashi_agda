module DASHI.Physics.Closure.NSTriadKNArbitraryDataAprioriProgram where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNSignedUniformGapProgram as Gap

------------------------------------------------------------------------
-- Exact Galerkin H^s differential identity.
------------------------------------------------------------------------

record GalerkinRegularityEnergy {c t s : Level} : Set (lsuc (c ⊔ t ⊔ s)) where
  field
    Cutoff : Set c
    Time : Set t
    State : Set s

    viscosity : Nat
    regularityIndex : Nat

    solution : Cutoff → Time → State

    energy dissipation nonlinearContribution energyDerivative :
      Cutoff → Time → State → Nat

    exactEnergyIdentity : ∀ N time →
      energyDerivative N time (solution N time)
      + viscosity * dissipation N time (solution N time)
      ≡ nonlinearContribution N time (solution N time)

open GalerkinRegularityEnergy public

------------------------------------------------------------------------
-- A nonlinear estimate must carry a global scalar comparison.  A cubic
-- remainder alone is not a non-blow-up theorem.
------------------------------------------------------------------------

data GlobalGrowthMechanism : Set where
  linearGrowth dissipativeSuperlinear controlledCriticalNorm integratedBKM :
    GlobalGrowthMechanism

record AbsorbableNonlinearEstimate
    {c t s : Level}
    (energyData : GalerkinRegularityEnergy {c} {t} {s}) :
    Set (lsuc (c ⊔ t ⊔ s)) where
  field
    absorptionNumerator absorptionDenominator : Nat
    strictAbsorption : absorptionNumerator < absorptionDenominator

    remainder : Nat → Nat

    nonlinearBound : ∀ N time →
      nonlinearContribution energyData N time (solution energyData N time)
      ≤ absorptionNumerator *
          dissipation energyData N time (solution energyData N time)
        + remainder (energy energyData N time (solution energyData N time))

    growthMechanism : GlobalGrowthMechanism
    scalarComparisonGlobal : Set
    cubicOnlyComparisonRejected : Set

open AbsorbableNonlinearEstimate public

------------------------------------------------------------------------
-- Stage-3 gap must control the actual nonlinear term on every trajectory.
------------------------------------------------------------------------

record Stage3GapControlsGalerkinEvolution
    {c t s : Level}
    (energyData : GalerkinRegularityEnergy {c} {t} {s}) :
    Set (lsuc (c ⊔ t ⊔ s)) where
  field
    spectralGap : Gap.UniformSignedSpectralGap

    StateEmbedding : State energyData → Gap.State spectralGap
    CutoffEmbedding : Cutoff energyData → Gap.Cutoff spectralGap

    exactErrorIdentification : Set
    baseFormIdentifiesDissipation : Set
    strongNormIdentifiesRegularityNorm : Set

    nonlinearEstimate : AbsorbableNonlinearEstimate energyData

    everyGalerkinStateAdmissible : ∀ N time → Set
    noSmallnessAssumption : Set
    noSymmetryAssumption : Set
    noPhaseRestriction : Set
    noHelicityRestriction : Set

open Stage3GapControlsGalerkinEvolution public

------------------------------------------------------------------------
-- Uniform finite-horizon estimate.
------------------------------------------------------------------------

record UniformGalerkinAprioriEstimate
    {c t s : Level}
    (energyData : GalerkinRegularityEnergy {c} {t} {s}) :
    Set (lsuc (c ⊔ t ⊔ s)) where
  field
    Horizon : Set
    bound : Horizon → Nat

    timeWithin : Time energyData → Horizon → Set

    energyUniform : ∀ horizon N time →
      timeWithin time horizon →
      energy energyData N time (solution energyData N time)
      ≤ bound horizon

    integratedDissipationUniform : ∀ horizon N → Set
    boundIndependentOfCutoff : Set

open UniformGalerkinAprioriEstimate public

record ArbitrarySmoothDivergenceFreeData
    {i : Level} (InitialData : Set i) : Set (lsuc i) where
  field
    Admissible Smooth DivergenceFree : InitialData → Set i
    everyDatumCovered :
      (u0 : InitialData) →
      Admissible u0 → Smooth u0 → DivergenceFree u0 → Set

open ArbitrarySmoothDivergenceFreeData public

record GapToArbitraryDataApriori
    {i c t s : Level}
    (InitialData : Set i)
    (energyData : GalerkinRegularityEnergy {c} {t} {s}) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ s)) where
  field
    arbitraryData : ArbitrarySmoothDivergenceFreeData InitialData
    evolutionControl : Stage3GapControlsGalerkinEvolution energyData

    initialDataToGalerkinState : InitialData → Cutoff energyData → State energyData
    projectedInitialDataConverges : Set

    uniformApriori :
      (u0 : InitialData) →
      Admissible arbitraryData u0 →
      Smooth arbitraryData u0 →
      DivergenceFree arbitraryData u0 →
      UniformGalerkinAprioriEstimate energyData

open GapToArbitraryDataApriori public

exactHsEnergyIdentityTargetImplemented : Bool
exactHsEnergyIdentityTargetImplemented = true

exactHsEnergyIdentityTargetImplementedIsTrue :
  exactHsEnergyIdentityTargetImplemented ≡ true
exactHsEnergyIdentityTargetImplementedIsTrue = refl

nonBlowupComparisonRequired : Bool
nonBlowupComparisonRequired = true

nonBlowupComparisonRequiredIsTrue : nonBlowupComparisonRequired ≡ true
nonBlowupComparisonRequiredIsTrue = refl

stage3GapToArbitraryDataAprioriClosed : Bool
stage3GapToArbitraryDataAprioriClosed = false

stage3GapToArbitraryDataAprioriClosedIsFalse :
  stage3GapToArbitraryDataAprioriClosed ≡ false
stage3GapToArbitraryDataAprioriClosedIsFalse = refl
