module DASHI.Physics.YangMills.BalabanClayGate4GaugeRandomWalkLocalizationExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (Σ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix as Finite
import DASHI.Physics.YangMills.BalabanUniformWeightedNeumannFamily as Uniform
import DASHI.Physics.YangMills.BalabanUniformNeumannAsymptoticResidual as Asymptotic
import DASHI.Physics.YangMills.BalabanGeometricPowerVanishing as Geometric

------------------------------------------------------------------------
-- Gauge-Hessian random-walk localization through the uniform Neumann family.
--
-- Tadeusz Bałaban,
-- "Regularity and Decay of Lattice Green's Functions",
-- Communications in Mathematical Physics 89 (1983), 571--597.
-- DOI: 10.1007/BF01214744.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215753.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban, I. Small Fields",
-- Reviews in Mathematical Physics 25 (7) (2013), article 1330010.
-- arXiv:1108.1335v2. DOI: 10.1142/S0129055X13300100.
--
-- The repository already proves the finite Neumann telescope and uniform
-- residual-power bounds.  Once the physical local Hessian/parametrix is
-- identified and its common contraction factor has Archimedean power coverage,
-- the random-walk truncation error is eventually below every positive target.
------------------------------------------------------------------------

record GaugeRandomWalkLocalizationInputs
    {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) →
      Finite.AdditiveParametrixData (Carrier index)}
    (family : Uniform.UniformWeightedResidualFamily
      Index Bound Carrier bundle) : Set₁ where
  field
    orderLaws : Geometric.GeometricPowerOrderLaws family
    powerCoverage : Geometric.ArchimedeanPowerCoverage family

    PhysicalLocalHessianMeaning : Set
    PhysicalParametrixMeaning : Set
    RandomWalkTermMeaning : Set
    HaloDepthMeaning : Nat → Set

    physicalLocalHessianMeaning : PhysicalLocalHessianMeaning
    physicalParametrixMeaning : PhysicalParametrixMeaning
    randomWalkTermMeaning : RandomWalkTermMeaning
    haloDepthMeaning : ∀ depth → HaloDepthMeaning depth

open GaugeRandomWalkLocalizationInputs public

asGaugeNeumannAsymptoticResidual :
  ∀ {Index Bound}
    {Carrier : Index → Set}
    {bundle : (index : Index) →
      Finite.AdditiveParametrixData (Carrier index)}
    {family : Uniform.UniformWeightedResidualFamily
      Index Bound Carrier bundle} →
  GaugeRandomWalkLocalizationInputs family →
  Asymptotic.UniformNeumannAsymptoticResidual family
asGaugeNeumannAsymptoticResidual {family = family} inputs = record
  { Asymptotic.UniformNeumannAsymptoticResidual.powerVanishing =
      Geometric.coveragePowerVanishing family
        (orderLaws inputs) (powerCoverage inputs)
  }

gaugeRandomWalkResidualEventuallyBelow :
  ∀ {Index Bound}
    {Carrier : Index → Set}
    {bundle : (index : Index) →
      Finite.AdditiveParametrixData (Carrier index)}
    {family : Uniform.UniformWeightedResidualFamily
      Index Bound Carrier bundle}
    (inputs : GaugeRandomWalkLocalizationInputs family)
    index value →
  Uniform.LessEqual family
    (Uniform.norm family value) (Uniform.oneBound family) →
  ∀ tolerance →
  Geometric.Positive (powerCoverage inputs) tolerance →
  Σ Nat (λ start →
    ∀ depth → start ≤ depth →
    Uniform.LessEqual family
      (Uniform.norm family
        (Finite.residualPower (bundle index) depth value))
      tolerance)
gaugeRandomWalkResidualEventuallyBelow {family = family}
    inputs index value unitBound tolerance positive =
  Asymptotic.neumannResidualEventuallyBelow
    family
    (asGaugeNeumannAsymptoticResidual inputs)
    index value unitBound tolerance positive

gaugeRandomWalkFiniteTelescopeLevel : ProofLevel
gaugeRandomWalkFiniteTelescopeLevel = machineChecked

gaugeRandomWalkAsymptoticLocalizationLevel : ProofLevel
gaugeRandomWalkAsymptoticLocalizationLevel = machineChecked

balabanLatticeGreenDecaySourceLevel : ProofLevel
balabanLatticeGreenDecaySourceLevel = standardImported

physicalGaugeHessianParametrixIdentificationInputsLevel : ProofLevel
physicalGaugeHessianParametrixIdentificationInputsLevel = conditional

physicalGaugeRandomWalkContractionInputsLevel : ProofLevel
physicalGaugeRandomWalkContractionInputsLevel = conditional
