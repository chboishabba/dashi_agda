{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawM1M2MassGapResidualCompilerExact where

------------------------------------------------------------------------
-- YM FULL-PROOF RESIDUAL AFTER M1 + M2
--
-- M1: cutoff-uniform physical scale bridge.
-- M2: dense-core spectral exclusion from the active-raw -> BC1 -> Row-C spine.
--
-- Once both are theorem-bearing payments, the remaining mandatory Clay mass-gap
-- gates are exactly:
--
--   M3, M4, M6, M7a, M7b, M7c, M8, M9.
--
-- M5 remains optional for sharp spectral-edge identification.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Gates
import DASHI.Physics.YangMills.BalabanClayPhysicalScaleExponentExact as Scale
import DASHI.Physics.Closure.YMPhysicalScaleM1GateAdapterExact as M1
import DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineExact as Spine
import DASHI.Physics.Closure.YMActiveRawDenseCoreM2GateAdapterExact as M2

record RemainingMandatoryMassGapGatesAfterM1M2
    (gates : Gates.ClayMassGapGatePropositions) : Set₁ where
  field
    m3 : Gates.M3LocalNoncollapse gates
    m4 :
      Gates._or_
        (Gates.M4ExactOSPullback gates)
        (Gates.M4TransferIntertwining gates)
    m6 : Gates.M6SpectralUVCompatibility gates
    m7a : Gates.M7aPhysicalActionVariationHamiltonianSameObject gates
    m7b : Gates.M7bHamiltonianDomainCommonInvariantDenseCore gates
    m7c : Gates.M7cSelfAdjointSelectedYMForm gates
    m8 : Gates.M8YMOSGeneratorEvolutionIdentification gates
    m9 : Gates.M9PhysicalVacuumRecoverySystem gates

open RemainingMandatoryMassGapGatesAfterM1M2 public

assembleMandatoryMassGapGatesAfterM1M2 :
  ∀ {gates} →
  Gates.M1PhysicalScaleClustering gates →
  Gates.M2DenseCoreSpectralExclusion gates →
  RemainingMandatoryMassGapGatesAfterM1M2 gates →
  Gates.MandatoryClayMassGapGates gates
assembleMandatoryMassGapGatesAfterM1M2 {gates} m1Payment m2Payment remaining =
  Gates.assembleMandatoryClayMassGapGates gates
    m1Payment
    m2Payment
    (m3 remaining)
    (m4 remaining)
    (m6 remaining)
    (m7a remaining)
    (m7b remaining)
    (m7c remaining)
    (m8 remaining)
    (m9 remaining)

assembleMandatoryMassGapGatesFromPhysicalScaleAndActiveRawDenseCore :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness bc1Inputs
      Cutoff algebra gates}
    {spine : Spine.ActiveRawBC1ToDenseCoreInputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background} {Fluctuation = Fluctuation}
      {Action = Action} {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {objects = objects} {predicates = predicates}
      {decoder = decoder} {rawWitness = rawWitness}
      bc1Inputs}
    {physicalScale : Scale.UniformPhysicalScaleClustering Cutoff algebra} →
  M1.PhysicalScaleM1GateWeld physicalScale gates →
  M2.ActiveRawDenseCoreM2GateWeld spine gates →
  RemainingMandatoryMassGapGatesAfterM1M2 gates →
  Gates.MandatoryClayMassGapGates gates
assembleMandatoryMassGapGatesFromPhysicalScaleAndActiveRawDenseCore
    m1Weld m2Weld remaining =
  assembleMandatoryMassGapGatesAfterM1M2
    (M1.physicalScalePaysM1 m1Weld)
    (M2.activeRawDenseCorePaysM2 m2Weld)
    remaining

activeRawM1M2ToMandatoryGateCompilerLevel : ProofLevel
activeRawM1M2ToMandatoryGateCompilerLevel = machineChecked

remainingMandatoryMassGapGatesAfterM1M2Level : ProofLevel
remainingMandatoryMassGapGatesAfterM1M2Level = conditional
