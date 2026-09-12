{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawMassGapGateResidualCompilerExact where

------------------------------------------------------------------------
-- YM FULL-PROOF RESIDUAL AFTER THE ACTIVE-RAW DENSE-CORE M2 ROUTE
--
-- The mandatory Clay mass-gap package has nine required coordinates, with M4
-- allowing either exact OS pullback or transfer intertwining.  The current
-- active-raw source -> BC1 -> Row-C -> dense-core spine can now pay M2 after an
-- explicit same-proposition weld.
--
-- This file freezes the resulting residual cut by type.  Once M2 is supplied,
-- the remaining mandatory gates are exactly:
--
--   M1, M3, M4, M6, M7a, M7b, M7c, M8, M9.
--
-- M5 remains optional and is needed only for sharp spectral-edge identification.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Gates
import DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineExact as Spine
import DASHI.Physics.Closure.YMActiveRawDenseCoreM2GateAdapterExact as M2

record RemainingMandatoryMassGapGatesAfterM2
    (gates : Gates.ClayMassGapGatePropositions) : Set₁ where
  field
    m1 : Gates.M1PhysicalScaleClustering gates
    m3 : Gates.M3LocalNoncollapse gates
    m4 :
      Gates.M4ExactOSPullback gates
      Gates.or
      Gates.M4TransferIntertwining gates
    m6 : Gates.M6SpectralUVCompatibility gates
    m7a : Gates.M7aPhysicalActionVariationHamiltonianSameObject gates
    m7b : Gates.M7bHamiltonianDomainCommonInvariantDenseCore gates
    m7c : Gates.M7cSelfAdjointSelectedYMForm gates
    m8 : Gates.M8YMOSGeneratorEvolutionIdentification gates
    m9 : Gates.M9PhysicalVacuumRecoverySystem gates

open RemainingMandatoryMassGapGatesAfterM2 public

assembleMandatoryMassGapGatesAfterM2 :
  ∀ {gates} →
  Gates.M2DenseCoreSpectralExclusion gates →
  RemainingMandatoryMassGapGatesAfterM2 gates →
  Gates.MandatoryClayMassGapGates gates
assembleMandatoryMassGapGatesAfterM2 {gates} m2Payment remaining =
  Gates.assembleMandatoryClayMassGapGates gates
    (m1 remaining)
    m2Payment
    (m3 remaining)
    (m4 remaining)
    (m6 remaining)
    (m7a remaining)
    (m7b remaining)
    (m7c remaining)
    (m8 remaining)
    (m9 remaining)

assembleMandatoryMassGapGatesFromActiveRawDenseCore :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness bc1Inputs gates}
    {spine : Spine.ActiveRawBC1ToDenseCoreInputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background} {Fluctuation = Fluctuation}
      {Action = Action} {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {objects = objects} {predicates = predicates}
      {decoder = decoder} {rawWitness = rawWitness}
      bc1Inputs} →
  M2.ActiveRawDenseCoreM2GateWeld spine gates →
  RemainingMandatoryMassGapGatesAfterM2 gates →
  Gates.MandatoryClayMassGapGates gates
assembleMandatoryMassGapGatesFromActiveRawDenseCore weld remaining =
  assembleMandatoryMassGapGatesAfterM2
    (M2.activeRawDenseCorePaysM2 weld)
    remaining

activeRawM2ToMandatoryGateCompilerLevel : ProofLevel
activeRawM2ToMandatoryGateCompilerLevel = machineChecked

-- M2 is not declared physically closed merely because the transport compiler is
-- closed: the underlying Row-C/dense-core spine and exact gate proposition weld
-- remain theorem-bearing physical inputs.
activeRawDenseCoreM2PhysicalPaymentLevel : ProofLevel
activeRawDenseCoreM2PhysicalPaymentLevel = conditional

-- This is the exact residual after a physical M2 payment on this route.
remainingMandatoryMassGapGatesAfterM2Level : ProofLevel
remainingMandatoryMassGapGatesAfterM2Level = conditional
