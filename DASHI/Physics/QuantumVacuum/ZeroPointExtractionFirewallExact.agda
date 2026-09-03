module DASHI.Physics.QuantumVacuum.ZeroPointExtractionFirewallExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.ZeroPointModeHyperfabricExact as ZPE
import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- PURPOSE
--
-- Connect the structural ground-state theorem to the existing extraction
-- promotion surface without equating nonzero zero-point energy with a usable
-- reservoir.
------------------------------------------------------------------------

record SameHypervoxelIsolation
    {S : ZPE.ScalarSpectrum}
    {B : ZPE.FieldBoundaryBase S}
    {k : ZPE.Mode B}
    {ak : ZPE.admissible B k}
    (F : ZPE.OscillatorModeFibre B k ak) : Set₁ where
  field
    sameField : Set
    sameBoundary : Set
    sameMode : Set
    sameHamiltonian : Set
    noExternalDrive : Set
    noExternalReservoir : Set
    isolationReading : String

open SameHypervoxelIsolation public

record GroundZeroPointFirewall
    {S : ZPE.ScalarSpectrum}
    (order : ZPE.StrictOrderIrreflexiveAgainstLE S)
    {B : ZPE.FieldBoundaryBase S}
    {k : ZPE.Mode B}
    {ak : ZPE.admissible B k}
    (F : ZPE.OscillatorModeFibre B k ak) : Set₁ where
  field
    ground : ZPE.GroundStateReceipt F
    zeroPoint : ZPE.ZeroPointFormulaReceipt F
    isolated : SameHypervoxelIsolation F

open GroundZeroPointFirewall public

isolatedGroundHasNoPositiveDescentWork :
  {S : ZPE.ScalarSpectrum} →
  (order : ZPE.StrictOrderIrreflexiveAgainstLE S) →
  {B : ZPE.FieldBoundaryBase S} →
  {k : ZPE.Mode B} →
  {ak : ZPE.admissible B k} →
  (F : ZPE.OscillatorModeFibre B k ak) →
  GroundZeroPointFirewall order F →
  ¬ ZPE.PositiveWorkFromGroundAlone F
isolatedGroundHasNoPositiveDescentWork order F firewall =
  ZPE.groundStateBlocksPositiveWorkFromGroundAlone
    order F (ground firewall)

------------------------------------------------------------------------
-- A nonzero ground-state assignment is not an ExtractionClaim receipt.
-- Promotion still belongs to the existing five-gate surface:
-- observable effect, coupling, non-equilibrium asymmetry, reset accounting,
-- and replication.
------------------------------------------------------------------------

record BoundaryChangedVacuumProcess : Set₁ where
  field
    InitialHypervoxel : Set
    FinalHypervoxel : Set
    BoundaryControl : Set
    ExternalWorkAccounting : Set
    ResetAccounting : Set
    ProcessObservable : Set
    processReading : String

open BoundaryChangedVacuumProcess public

-- Casimir motion, cavity retuning, material switching, and other boundary
-- changes belong here rather than under PositiveWorkFromGroundAlone: changing
-- a boundary changes the mode hyperfabric and therefore changes the physical
-- accounting problem.

record ZeroPointToExtractionBridge : Set₁ where
  field
    Process : Set
    process : Process
    extractionClaim : Process → Surface.ExtractionClaim

    zeroPointFormulaAloneClosesObservableEffect : Bool
    zeroPointFormulaAloneClosesCoupling : Bool
    zeroPointFormulaAloneClosesNonEquilibrium : Bool
    zeroPointFormulaAloneClosesReset : Bool
    zeroPointFormulaAloneClosesReplication : Bool

    zeroPointFormulaAloneClosesObservableEffectIsFalse :
      zeroPointFormulaAloneClosesObservableEffect ≡ false
    zeroPointFormulaAloneClosesCouplingIsFalse :
      zeroPointFormulaAloneClosesCoupling ≡ false
    zeroPointFormulaAloneClosesNonEquilibriumIsFalse :
      zeroPointFormulaAloneClosesNonEquilibrium ≡ false
    zeroPointFormulaAloneClosesResetIsFalse :
      zeroPointFormulaAloneClosesReset ≡ false
    zeroPointFormulaAloneClosesReplicationIsFalse :
      zeroPointFormulaAloneClosesReplication ≡ false

open ZeroPointToExtractionBridge public

canonicalZeroPointNonPromotionClaim : Surface.ExtractionClaim
canonicalZeroPointNonPromotionClaim =
  Surface.mkExtractionClaim
    Surface.groundStateSuppression
    Surface.transient
    Surface.theoreticalProposal
    false false false false false

zeroPointFormulaAloneNotPromotable :
  Surface.promotable? canonicalZeroPointNonPromotionClaim ≡ false
zeroPointFormulaAloneNotPromotable = refl
