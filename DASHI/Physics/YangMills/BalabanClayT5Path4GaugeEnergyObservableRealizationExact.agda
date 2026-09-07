{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact where

------------------------------------------------------------------------
-- PATH4 GAUGE ENERGY -> LITERAL T5 OBSERVABLE REALIZATION
--
-- The T5 OS/measure layer deliberately leaves `Observable` abstract.  The
-- existing configured Path4 coercivity theorem, however, is a theorem about the
-- concrete scalar-valued function `configuredGaugeFixedEnergy` on
-- `PhysicalSU2Tangent4`.  This module states the exact representation seam
-- needed to reuse that theorem without conflating the two carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact using
  (PhysicalSU2Tangent4; physicalUnweightedNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact using
  (configuredGaugeFixedEnergy; configuredGaugeFixedMatrixPositive)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGaugeFixedEnergyNonnegativeExact using
  (configuredGaugeFixedEnergyNonnegative)
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

record Path4GaugeEnergyObservableRealization
    (Measure Observable Configuration : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ) : Set₁ where
  field
    -- Pointwise semantics for the otherwise abstract T5 observable carrier.
    observableValue : Observable → Configuration → ℚ

    -- The physical small-field/tangent coordinate on which the existing Path4
    -- energy theorem is stated.
    physicalTangentCoordinate : Configuration → PhysicalSU2Tangent4

    -- Literal observable selected for the T5 moment/tightness route.
    path4GaugeEnergyObservable : Observable

    -- Same-object theorem at the semantic boundary.
    path4GaugeEnergyObservablePointwiseExact : ∀ configuration →
      observableValue path4GaugeEnergyObservable configuration
      ≡ configuredGaugeFixedEnergy
          (physicalTangentCoordinate configuration)

open Path4GaugeEnergyObservableRealization public

path4GaugeEnergyObservablePointwiseNonnegative :
  ∀ {Measure Observable Configuration}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    (realization :
      Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData)
    configuration →
  0ℚ ≤ observableValue realization
    (path4GaugeEnergyObservable realization) configuration
path4GaugeEnergyObservablePointwiseNonnegative realization configuration =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (path4GaugeEnergyObservablePointwiseExact realization configuration))
    (configuredGaugeFixedEnergyNonnegative
      (physicalTangentCoordinate realization configuration))

path4GaugeEnergyObservablePointwiseCoercive :
  ∀ {Measure Observable Configuration}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    (realization :
      Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData)
    configuration →
  configuredPathCoercivityConstant
    * physicalUnweightedNormSq
        (physicalTangentCoordinate realization configuration)
  ≤ observableValue realization
      (path4GaugeEnergyObservable realization) configuration
path4GaugeEnergyObservablePointwiseCoercive realization configuration =
  subst
    (λ value →
      configuredPathCoercivityConstant
        * physicalUnweightedNormSq
            (physicalTangentCoordinate realization configuration)
      ≤ value)
    (sym (path4GaugeEnergyObservablePointwiseExact realization configuration))
    (configuredGaugeFixedMatrixPositive
      (physicalTangentCoordinate realization configuration))

record RenormalizedPath4GaugeEnergyObservable
    {Measure Observable Configuration : Set}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    (realization :
      Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData) : Set where
  field
    path4GaugeEnergyRenormalized :
      T5.RenormalizedObservable
        (T5.thermodynamic expectationData)
        (path4GaugeEnergyObservable realization)

open RenormalizedPath4GaugeEnergyObservable public

path4GaugeEnergyObservableRealizationLevel : ProofLevel
path4GaugeEnergyObservableRealizationLevel = conditional

path4GaugeEnergyPointwiseNonnegativeLevel : ProofLevel
path4GaugeEnergyPointwiseNonnegativeLevel = machineChecked

path4GaugeEnergyPointwiseCoercivityTransportLevel : ProofLevel
path4GaugeEnergyPointwiseCoercivityTransportLevel = machineChecked

path4GaugeEnergyRenormalizationLevel : ProofLevel
path4GaugeEnergyRenormalizationLevel = conditional
