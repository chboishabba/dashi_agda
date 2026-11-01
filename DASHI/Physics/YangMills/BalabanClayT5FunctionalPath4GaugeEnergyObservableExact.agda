{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5FunctionalPath4GaugeEnergyObservableExact where

------------------------------------------------------------------------
-- FUNCTIONAL T5 OBSERVABLE CARRIER WITH DEFINITIONAL PATH4 ENERGY
--
-- On the preferred semantic route an observable is literally a scalar-valued
-- function of a physical configuration.  Given only a physical chart into the
-- configured Path4 tangent carrier, the gauge-fixed energy observable and its
-- pointwise meaning are therefore definitions, not post-hoc equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact using
  (PhysicalSU2Tangent4)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact using
  (configuredGaugeFixedEnergy)
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Realization

FunctionalObservable : Set → Set
FunctionalObservable Configuration = Configuration → ℚ

functionalObservableValue :
  ∀ {Configuration} →
  FunctionalObservable Configuration → Configuration → ℚ
functionalObservableValue observable configuration = observable configuration

functionalPath4GaugeEnergyObservable :
  ∀ {Configuration} →
  (Configuration → PhysicalSU2Tangent4) →
  FunctionalObservable Configuration
functionalPath4GaugeEnergyObservable chart configuration =
  configuredGaugeFixedEnergy (chart configuration)

functionalPath4GaugeEnergyPointwiseExact :
  ∀ {Configuration}
    (chart : Configuration → PhysicalSU2Tangent4)
    configuration →
  functionalObservableValue
    (functionalPath4GaugeEnergyObservable chart) configuration
  ≡ configuredGaugeFixedEnergy (chart configuration)
functionalPath4GaugeEnergyPointwiseExact chart configuration = refl

compileFunctionalPath4GaugeEnergyRealization :
  ∀ {Measure Configuration}
    (expectationData :
      T5.PhysicalExpectationProducerData
        Measure (FunctionalObservable Configuration) ℚ)
    (chart : Configuration → PhysicalSU2Tangent4) →
  Realization.Path4GaugeEnergyObservableRealization
    Measure (FunctionalObservable Configuration) Configuration expectationData
compileFunctionalPath4GaugeEnergyRealization expectationData chart = record
  { observableValue = functionalObservableValue
  ; physicalTangentCoordinate = chart
  ; path4GaugeEnergyObservable = functionalPath4GaugeEnergyObservable chart
  ; path4GaugeEnergyObservablePointwiseExact =
      functionalPath4GaugeEnergyPointwiseExact chart
  }

functionalObservableSemanticsLevel : ProofLevel
functionalObservableSemanticsLevel = machineChecked

functionalPath4GaugeEnergyRealizationCompilerLevel : ProofLevel
functionalPath4GaugeEnergyRealizationCompilerLevel = machineChecked

-- The remaining representation datum is the physical chart itself.  This
-- module does not manufacture a configuration-to-fluctuation identification.
physicalConfigurationToPath4TangentChartLevel : ProofLevel
physicalConfigurationToPath4TangentChartLevel = conditional
