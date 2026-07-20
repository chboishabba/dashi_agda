module DASHI.Physics.YangMills.BalabanGeometricNeumannClosure where

------------------------------------------------------------------------
-- Closes the order-theoretic Neumann lane:
--
--   strict common contraction
--   + ordered multiplication laws
--   + Archimedean coverage of positive tolerances
--   ------------------------------------------------
--   uniform asymptotic residual decay on the unit ball.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (Σ)

import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix as Finite
open import DASHI.Physics.YangMills.BalabanUniformWeightedNeumannFamily
open import DASHI.Physics.YangMills.BalabanUniformNeumannAsymptoticResidual
open import DASHI.Physics.YangMills.BalabanGeometricPowerVanishing
open import DASHI.Physics.YangMills.CompactLieProofLevel

geometricNeumannAsymptotic :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  GeometricPowerOrderLaws family →
  ArchimedeanPowerCoverage family →
  UniformNeumannAsymptoticResidual family
geometricNeumannAsymptotic family laws coverage = record
  { powerVanishing = coveragePowerVanishing family laws coverage }

geometricUnitBallResidualEventuallyBelow :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (laws : GeometricPowerOrderLaws family) →
  (coverage : ArchimedeanPowerCoverage family) →
  ∀ index value →
  LessEqual family (norm family value) (oneBound family) →
  ∀ tolerance → Positive coverage tolerance →
  Σ Nat (λ start →
    ∀ depth → start ≤ depth →
    LessEqual family
      (norm family (Finite.residualPower (bundle index) depth value))
      tolerance)
geometricUnitBallResidualEventuallyBelow
  family laws coverage =
  neumannResidualEventuallyBelow
    family (geometricNeumannAsymptotic family laws coverage)

geometricNeumannClosureLevel : ProofLevel
geometricNeumannClosureLevel = machineChecked

archimedeanPowerCoverageLevel : ProofLevel
archimedeanPowerCoverageLevel = standardImported
