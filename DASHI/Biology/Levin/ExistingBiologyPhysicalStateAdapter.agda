module DASHI.Biology.Levin.ExistingBiologyPhysicalStateAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EpigeneticTemporalRegulationBridge as Epigenetic
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Longitudinal
import DASHI.Biology.BodyMemoryMeasurementProxyBoundary as Measurement
import DASHI.Biology.TraumaClinicalGovernanceBoundary as Governance

import DASHI.Biology.Levin.CondensateElectroosmoticState as Condensate
import DASHI.Biology.Levin.ATPDependentCytoplasmicOrganisation as ATP
import DASHI.Biology.Levin.StressGranuleVoltageBoundary as Granule

------------------------------------------------------------------------
-- Adapter into existing DASHI biology lanes.
--
-- Physical-state candidates are upstream observation surfaces.  They do not
-- replace epigenetic, longitudinal, proxy-governance, or clinical-boundary
-- modules and cannot independently recover a hidden body-memory chart.

record ExistingBiologyPhysicalStateAdapter : Set where
  field
    epigeneticTemporalRoute :
      Epigenetic.TemporalRegulationRoute
    epigeneticTemporalRouteIsCandidateOnly :
      epigeneticTemporalRoute ≡ Epigenetic.candidateOnlyTemporalRegulationRoute

    intersectionalAxes :
      List Longitudinal.IntersectionalAxis
    intersectionalAxesAreCanonical :
      intersectionalAxes ≡ Longitudinal.canonicalIntersectionalAxes

    bodyMemoryBoundaryClaims :
      List Measurement.BoundaryClaimKind
    bodyMemoryBoundaryClaimsAreCanonical :
      bodyMemoryBoundaryClaims ≡ Measurement.canonicalBoundaryClaims

    traumaGovernanceAxes :
      List Governance.TraumaClinicalGovernanceAxis
    traumaGovernanceAxesAreCanonical :
      traumaGovernanceAxes ≡ Governance.canonicalTraumaClinicalGovernanceAxes

    condensateWitness :
      Condensate.ElectroosmoticCondensateWitness

    ATPOrganisationWitness :
      ATP.ATPOrganisationWitness

    stressGranuleVoltageWitness :
      Granule.StressGranuleVoltageWitness

    physicalStateIsObservationLayer : Bool
    physicalStateIsObservationLayerIsTrue :
      physicalStateIsObservationLayer ≡ true

    physicalStateDoesNotRecoverHiddenChart : Bool
    physicalStateDoesNotRecoverHiddenChartIsFalse :
      physicalStateDoesNotRecoverHiddenChart ≡ false

    associationIsNotCausalClosure : Bool
    associationIsNotCausalClosureIsFalse :
      associationIsNotCausalClosure ≡ false

    noClinicalAuthority : Bool
    noClinicalAuthorityIsFalse : noClinicalAuthority ≡ false

    reading : String

open ExistingBiologyPhysicalStateAdapter public

canonicalExistingBiologyPhysicalStateAdapter : ExistingBiologyPhysicalStateAdapter
canonicalExistingBiologyPhysicalStateAdapter = record
  { epigeneticTemporalRoute =
      Epigenetic.candidateOnlyTemporalRegulationRoute
  ; epigeneticTemporalRouteIsCandidateOnly = refl
  ; intersectionalAxes =
      Longitudinal.canonicalIntersectionalAxes
  ; intersectionalAxesAreCanonical = refl
  ; bodyMemoryBoundaryClaims =
      Measurement.canonicalBoundaryClaims
  ; bodyMemoryBoundaryClaimsAreCanonical = refl
  ; traumaGovernanceAxes =
      Governance.canonicalTraumaClinicalGovernanceAxes
  ; traumaGovernanceAxesAreCanonical = refl
  ; condensateWitness =
      Condensate.canonicalElectroosmoticCondensateWitness
  ; ATPOrganisationWitness =
      ATP.canonicalATPOrganisationWitness
  ; stressGranuleVoltageWitness =
      Granule.canonicalStressGranuleVoltageWitness
  ; physicalStateIsObservationLayer = true
  ; physicalStateIsObservationLayerIsTrue = refl
  ; physicalStateDoesNotRecoverHiddenChart = false
  ; physicalStateDoesNotRecoverHiddenChartIsFalse = refl
  ; associationIsNotCausalClosure = false
  ; associationIsNotCausalClosureIsFalse = refl
  ; noClinicalAuthority = false
  ; noClinicalAuthorityIsFalse = refl
  ; reading =
      "Levin physical state observations adapt to existing biology lanes as candidate-only layers without clinical or causal closure authority."
  }
