module DASHI.Physics.Photovoltaic.GaAs111QuantumWellConfinementExact where

-- P1d max-cut: quantum-well confinement is the missing material-to-spectrum
-- producer, not a replacement for original 369 atomic/C3 or PV P2 transport.
-- Source Molenkamp et al. PRB 38 4314(R) (1988), DOI 10.1103/PhysRevB.38.4314
-- Original Philips QW envelope review: Eppenga/Schuurmans, Philips Technical
-- Review 44, No 5 (1988), 137-149. Attribution retained.
-- Agda Golden kernel typecheck not executed; physical model not fitted.

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Photovoltaic.GaAs111MeasuredMassAdversarialExact as Mass
import DASHI.Physics.Photovoltaic.GaAs111OpticalDeviceSourceWeldExact as Optical
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Transport

-- Existing prior source exact mass identities:
-- theoretical (111) HH bulk curvature m/m0 = 25/28
-- 1988 QW-model inferred m/m0 = 7/10
-- The inverse-mass kinetic prefactors differ. Since the same width L
-- contributes the same factor 1/L² in the infinite-well limit, its
-- coordinate change cannot reconcile these masses by relabelling.
same111MassCannotBePromoted :
  25 * 10 ≡ 7 * 28 -> Mass.False
same111MassCannotBePromoted =
  Mass.predicted111HHCannotEqual1988Observed

-- Do NOT conflate a finite-well energy calculation with spectroscopy:
-- interfaces require continuity of envelope and (1/m) derivative
-- (BenDaniel-Duke); excitons require separate coupled e-hole dynamics.
record GaAs111QWFiniteBarrierPhysicalAdmission : Set₁ where
  field
    SameSpecimenMaterial : Set
    specimen : SameSpecimenMaterial

    MeasuredWellThickness : Set
    wellThickness : MeasuredWellThickness

    MeasuredBarrierComposition : Set
    barrierComposition : MeasuredBarrierComposition

    ActualElectronHoleBandOffsets : Set
    bandOffsets : ActualElectronHoleBandOffsets

    SameBasisLuttingerKane : Set
    sourceEightBandHamiltonian : SameBasisLuttingerKane

    PhysicalEnvelopeInterfaceFlux : Set
    benDanielDukeMatching : PhysicalEnvelopeInterfaceFlux

    MeasuredExcitonPLE : Set
    originalPLE : MeasuredExcitonPLE

    SourceMatchedLevelFit : Set
    checkedConfinementFit : SourceMatchedLevelFit

    SameSampleExtraction : Set
    collectedCarrierAndJV : SameSampleExtraction

-- The actual P2 device weld continues to consume original continuity,
-- real G173 solar field and PV energy accounting through existing
-- Optical.SameArtifactPVConversionWeld. No instance is manufactured.
