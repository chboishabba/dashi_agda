module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard

------------------------------------------------------------------------
-- SOURCE-BOUNDED METADYNAMICS FREE-ENERGY UNCERTAINTY
--
-- Li, Liu & Ji report that the metadynamics free-energy error estimated by the
-- cited method is about 0.5 kcal/mol.  This pays an uncertainty envelope for
-- BE-META-derived free-energy values.  It does NOT pay the missing per-state
-- Figure-5 free-energy labels, make a visual readout exact, or convert relative
-- free energy into absolute thermodynamic free energy.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

record RationalUncertainty : Set where
  constructor rational-uncertainty
  field
    numerator : Nat
    denominator : Nat
    unit : String
    approximationRole : String
    sourceLocator : String
open RationalUncertainty public

metadynamicsFreeEnergyUncertainty : RationalUncertainty
metadynamicsFreeEnergyUncertainty = rational-uncertainty
  1 2 "kcal/mol"
  "source reports approximately 0.5 kcal/mol free-energy error; represented exactly as the printed decimal 1/2 while retaining approximate-source semantics"
  "PMC4572606 abstract/method summary: metadynamics free-energy error estimated according to Marinelli et al. is ~0.5 kcal/mol"

record FreeEnergyUncertaintyEnvelope : Set where
  constructor free-energy-uncertainty-envelope
  field
    uncertainty : RationalUncertainty
    appliesToMetadynamicsFreeEnergy : Bool
    stateSpecificEnergyValuePaid : Bool
    absoluteThermodynamicReferencePaid : Bool
    figureReadoutExactnessPaid : Bool
    acquisitionGuard : Guard.GuardedCalibrationAcquisitionBoundary
open FreeEnergyUncertaintyEnvelope public

canonicalFreeEnergyUncertaintyEnvelope : FreeEnergyUncertaintyEnvelope
canonicalFreeEnergyUncertaintyEnvelope = free-energy-uncertainty-envelope
  metadynamicsFreeEnergyUncertainty
  true false false false
  Guard.canonicalGuardedCalibrationAcquisitionBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data UncertaintyCreatesMissingStateEnergy : Set where
data ErrorBoundMakesVisualReadoutExact : Set where
data RelativeEnergyBecomesAbsoluteThermodynamics : Set where

data ApproximateSourceValueBecomesExactPhysicalTruth : Set where

uncertaintyDoesNotCreateMissingStateEnergy :
  UncertaintyCreatesMissingStateEnergy → ⊥
uncertaintyDoesNotCreateMissingStateEnergy ()

errorBoundDoesNotMakeVisualReadoutExact :
  ErrorBoundMakesVisualReadoutExact → ⊥
errorBoundDoesNotMakeVisualReadoutExact ()

relativeEnergyDoesNotBecomeAbsoluteThermodynamics :
  RelativeEnergyBecomesAbsoluteThermodynamics → ⊥
relativeEnergyDoesNotBecomeAbsoluteThermodynamics ()

printedApproximationDoesNotBecomeExactPhysicalTruth :
  ApproximateSourceValueBecomesExactPhysicalTruth → ⊥
printedApproximationDoesNotBecomeExactPhysicalTruth ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKMetadynamicsUncertaintyBoundary : Set where
  constructor adk-metadynamics-uncertainty-boundary
  field
    freeEnergyErrorHalfKcalMolPaid : Bool
    uncertaintyAppliesToMetadynamicsFreeEnergy : Bool
    acquisitionGuardRetained : Bool
    uncertaintyCreatesMissingStateEnergy : Bool
    errorBoundMakesVisualReadoutExact : Bool
    relativeEnergyBecomesAbsoluteThermodynamics : Bool
    approximateSourceValuePromotedToExactPhysicalTruth : Bool
    nextResidual : String
open AdKMetadynamicsUncertaintyBoundary public

canonicalAdKMetadynamicsUncertaintyBoundary : AdKMetadynamicsUncertaintyBoundary
canonicalAdKMetadynamicsUncertaintyBoundary = adk-metadynamics-uncertainty-boundary
  true true true
  false false false false
  "attach the ~0.5 kcal/mol uncertainty envelope only to same-object BE-META free-energy values after their exact state/figure locator is acquired. It does not fill the currently unpaid per-state Delta-G cells or relax the supporting-material manifestation guard."
