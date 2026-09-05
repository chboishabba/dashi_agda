module DASHI.Physics.QuantumVacuum.CasimirModeHyperfabricBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.ZeroPointModeHyperfabricExact as ZPE
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- PURPOSE
--
-- Put the existing parallel-plate Casimir kernel downstream of a genuine
-- same-field / different-boundary mode-hyperfabric comparison.
--
--   boundary A -> admissible mode fabric A -> raw vacuum aggregate A
--   boundary B -> admissible mode fabric B -> raw vacuum aggregate B
--                            |
--                            v
--                 renormalised difference observable
--                            |
--                            v
--                 Casimir energy/stress comparison
--
-- Nothing here identifies either raw sum with an observable, and nothing here
-- turns a boundary-changing process into extraction from one unchanged ground
-- hypervoxel.
------------------------------------------------------------------------

record BoundaryRetopologyReceipt
    {S : ZPE.ScalarSpectrum}
    (free cavity : ZPE.FiniteVacuumHyperfabric S) : Set₁ where
  field
    sameFieldDifferentBoundary :
      ZPE.SameFieldDifferentBoundaryWitness free cavity

    FreeModeCoordinate : Set
    CavityModeCoordinate : Set

    freeModeChart : ZPE.Hypervoxel free → FreeModeCoordinate
    cavityModeChart : ZPE.Hypervoxel cavity → CavityModeCoordinate

    modeFamiliesDiffer : Set
    retopologyReading : String

open BoundaryRetopologyReceipt public

------------------------------------------------------------------------
-- The physically meaningful comparison is mediated by a renormalisation /
-- subtraction fibre.  Raw finite sums remain inputs, not observables.
------------------------------------------------------------------------

record VacuumDifferenceObservable
    {S : ZPE.ScalarSpectrum}
    (free cavity : ZPE.FiniteVacuumHyperfabric S) : Set₁ where
  field
    Observable : Set
    Regulator : Set
    Scheme : Set
    Reference : Set

    regulator : Regulator
    scheme : Scheme
    reference : Reference

    compareRawVacua :
      ZPE.Scalar S →
      ZPE.Scalar S →
      Regulator →
      Scheme →
      Reference →
      Observable

    observable : Observable

    observableIsComparison :
      observable ≡
      compareRawVacua
        (ZPE.finiteVacuumEnergy free)
        (ZPE.finiteVacuumEnergy cavity)
        regulator scheme reference

    differenceReading : String

open VacuumDifferenceObservable public

------------------------------------------------------------------------
-- Same-object weld to the existing Casimir equation carrier.
--
-- The weld is deliberately typed as evidence: CasimirScalarModel owns the
-- analytic parallel-plate equation, while the vacuum-difference surface owns
-- the boundary-dependent mode comparison.  A concrete real/rational model
-- must prove that they denote the same observable before the two lanes may be
-- identified.
------------------------------------------------------------------------

record CasimirModeHyperfabricWeld
    {S : ZPE.ScalarSpectrum}
    (free cavity : ZPE.FiniteVacuumHyperfabric S) : Set₁ where
  field
    retopology : BoundaryRetopologyReceipt free cavity
    difference : VacuumDifferenceObservable free cavity

    separation : Q.Length
    plateArea : Q.Area
    kernel : Casimir.CasimirScalarModel

    SameObservable : Set

    vacuumDifferenceAgreesWithEnergyPerArea : SameObservable
    boundaryDerivativeAgreesWithPressure : SameObservable

    weldReading : String

open CasimirModeHyperfabricWeld public

------------------------------------------------------------------------
-- Classification firewall.
--
-- A Casimir stroke changes the boundary coordinate.  It therefore does not
-- inhabit the same-hypervoxel ground-state-only extraction class.
------------------------------------------------------------------------

record CasimirBoundaryChangeProcess : Set₁ where
  field
    stroke : Casimir.ConductiveStroke
    boundaryChanged : Set
    externalBoundaryControlAccounted : Set
    resetAccountingRequired : Set
    processReading : String

open CasimirBoundaryChangeProcess public

casimirBoundaryChangeIsSameGroundHypervoxelExtraction : Bool
casimirBoundaryChangeIsSameGroundHypervoxelExtraction = false

casimirBoundaryChangeIsSameGroundHypervoxelExtractionIsFalse :
  casimirBoundaryChangeIsSameGroundHypervoxelExtraction ≡ false
casimirBoundaryChangeIsSameGroundHypervoxelExtractionIsFalse = refl

------------------------------------------------------------------------
-- Existing Casimir boundary stress still does not close a cycle.  We expose
-- that result at the mode-hyperfabric bridge so downstream consumers cannot
-- mistake the new microscopic interpretation for stronger extraction
-- authority than the existing kernel supplies.
------------------------------------------------------------------------

casimirStressStillDoesNotCloseCycle :
  Casimir.BoundaryStressEstablished → Set
casimirStressStillDoesNotCloseCycle = Casimir.boundaryStressDoesNotCloseCycle

casimirModeDifferenceAlonePromotable : Surface.ExtractionClaim
casimirModeDifferenceAlonePromotable =
  Surface.mkExtractionClaim
    Surface.casimirRelaxation
    Surface.transient
    Surface.theoreticalProposal
    true true false false false

casimirModeDifferenceAloneNotPromoted :
  Surface.promotable? casimirModeDifferenceAlonePromotable ≡ false
casimirModeDifferenceAloneNotPromoted = refl

------------------------------------------------------------------------
-- Machine-readable authority boundary.
------------------------------------------------------------------------

record CasimirModeBridgeBoundary : Set where
  field
    rawModeSumsAreObservablesByDefinition : Bool
    boundaryChangeIsFreeExtractionByDefinition : Bool
    casimirEquationClosesResetByDefinition : Bool
    cosmologicalConstantImportedByDefinition : Bool

    rawModeSumsAreObservablesByDefinitionIsFalse :
      rawModeSumsAreObservablesByDefinition ≡ false
    boundaryChangeIsFreeExtractionByDefinitionIsFalse :
      boundaryChangeIsFreeExtractionByDefinition ≡ false
    casimirEquationClosesResetByDefinitionIsFalse :
      casimirEquationClosesResetByDefinition ≡ false
    cosmologicalConstantImportedByDefinitionIsFalse :
      cosmologicalConstantImportedByDefinition ≡ false

open CasimirModeBridgeBoundary public

canonicalCasimirModeBridgeBoundary : CasimirModeBridgeBoundary
canonicalCasimirModeBridgeBoundary =
  record
    { rawModeSumsAreObservablesByDefinition = false
    ; boundaryChangeIsFreeExtractionByDefinition = false
    ; casimirEquationClosesResetByDefinition = false
    ; cosmologicalConstantImportedByDefinition = false
    ; rawModeSumsAreObservablesByDefinitionIsFalse = refl
    ; boundaryChangeIsFreeExtractionByDefinitionIsFalse = refl
    ; casimirEquationClosesResetByDefinitionIsFalse = refl
    ; cosmologicalConstantImportedByDefinitionIsFalse = refl
    }
