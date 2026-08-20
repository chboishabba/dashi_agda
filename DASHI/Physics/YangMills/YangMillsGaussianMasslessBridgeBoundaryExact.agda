module DASHI.Physics.YangMills.YangMillsGaussianMasslessBridgeBoundaryExact where

------------------------------------------------------------------------
-- ROUND75: GAUSSIANITY ALONE DOES NOT IMPLY A MASSLESS MAXWELL SECTOR.
--
-- The attractive nontriviality shortcut
--
--   Gaussian continuum YM -> massless Maxwell -> contradiction with gap
--
-- is valid only if the first arrow is a SAME-THEORY structural theorem.
-- Gaussianity by itself is insufficient: massive Gaussian theories exist.
-- Therefore the physical bridge must retain the gauge/Ward/kinetic data that
-- exclude a mass term and identify the transverse quadratic sector with
-- Maxwell. This module makes that missing hypothesis impossible to hide.
--
-- CALIBRATION SOURCES
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- Stephen J. Gustafson and Israel Michael Sigal,
-- "Mathematical Concepts of Quantum Mechanics", Springer.
-- DOI: 10.1007/978-3-642-55729-3.
--
-- The repository's `YangMillsFreeGaussianMaxwellNoGapExact` already proves
-- that a massless one-particle sector contradicts a positive spectral gap.
-- The only point here is to guard the premise of that compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record GaussianToyState : Set where
  constructor gaussianToy
  field
    gaussian : Bool
    massless : Bool

open GaussianToyState public

masslessGaussian : GaussianToyState
masslessGaussian = gaussianToy true true

massiveGaussian : GaussianToyState
massiveGaussian = gaussianToy true false

gaussianCollision :
  gaussian masslessGaussian ≡ gaussian massiveGaussian
gaussianCollision = refl

masslessValuesDiffer :
  massless masslessGaussian ≡ true
masslessValuesDiffer = refl

massiveValueIsFalse :
  massless massiveGaussian ≡ false
massiveValueIsFalse = refl

------------------------------------------------------------------------
-- Positive route: the extra structure needed by #8 is named explicitly.
------------------------------------------------------------------------

record GaussianToMaxwellPhysicalBridge : Set₁ where
  field
    ContinuumState ReconstructedHamiltonian : Set
    Gaussian : ContinuumState → Set
    ExactGaugeWardIdentity : ContinuumState → Set
    StandardQuadraticKineticNormalization : ContinuumState → Set
    NoGaugeInvariantMassTerm : ContinuumState → Set
    SameHamiltonian : ContinuumState → ReconstructedHamiltonian → Set
    MasslessMaxwellSector : ReconstructedHamiltonian → Set

    gaussianWardKineticToMassless :
      ∀ state H →
      Gaussian state →
      ExactGaugeWardIdentity state →
      StandardQuadraticKineticNormalization state →
      NoGaugeInvariantMassTerm state →
      SameHamiltonian state H →
      MasslessMaxwellSector H

open GaussianToMaxwellPhysicalBridge public

gaussianToMaxwellRequiresPhysicalStructureLevel : ProofLevel
gaussianToMaxwellRequiresPhysicalStructureLevel = machineChecked

physicalGaussianWardKineticMasslessBridgeLevel : ProofLevel
physicalGaussianWardKineticMasslessBridgeLevel = conditional
