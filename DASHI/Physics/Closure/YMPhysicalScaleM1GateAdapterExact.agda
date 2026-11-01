{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMPhysicalScaleM1GateAdapterExact where

------------------------------------------------------------------------
-- YM MASS-GAP GATE M1 / PHYSICAL-SCALE CLUSTERING
--
-- Row-C geometric decay is not by itself a continuum physical-mass statement.
-- The existing physical-scale theorem isolates the additional uniform bridge
--
--     m_phys * a(cutoff) <= m_lat(cutoff).
--
-- This adapter pays an abstract Clay M1 slot only after the gate proposition is
-- explicitly identified with that exact `UniformPhysicalScaleClustering` object.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayPhysicalScaleExponentExact as Scale
import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Gates

record PhysicalScaleM1GateWeld
    {Cutoff : Set}
    {algebra : Scale.OrderedScaleAlgebra}
    (physicalScale : Scale.UniformPhysicalScaleClustering Cutoff algebra)
    (gates : Gates.ClayMassGapGatePropositions) : Set₁ where
  field
    m1IsExactUniformPhysicalScaleClustering :
      Gates.M1PhysicalScaleClustering gates
      ≡ Scale.UniformPhysicalScaleClustering Cutoff algebra

open PhysicalScaleM1GateWeld public

physicalScalePaysM1 :
  ∀ {Cutoff algebra gates}
    {physicalScale : Scale.UniformPhysicalScaleClustering Cutoff algebra} →
  PhysicalScaleM1GateWeld physicalScale gates →
  Gates.M1PhysicalScaleClustering gates
physicalScalePaysM1 {physicalScale = physicalScale} weld =
  subst
    (λ P → P)
    (sym (m1IsExactUniformPhysicalScaleClustering weld))
    physicalScale

physicalScaleM1TransportCompilerLevel : ProofLevel
physicalScaleM1TransportCompilerLevel = machineChecked

-- The scale transport algebra is already proved generically.  The live physical
-- input is the cutoff-uniform bridge itself plus the same-proposition gate weld.
uniformPhysicalMassScaleBridgeInputLevel : ProofLevel
uniformPhysicalMassScaleBridgeInputLevel =
  Scale.uniformPhysicalMassScaleBridgeInputsLevel

physicalScaleM1SamePropositionWeldLevel : ProofLevel
physicalScaleM1SamePropositionWeldLevel = conditional
