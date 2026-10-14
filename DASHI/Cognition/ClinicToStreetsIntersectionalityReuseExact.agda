module DASHI.Cognition.ClinicToStreetsIntersectionalityReuseExact where

------------------------------------------------------------------------
-- CLINIC-TO-STREETS AS AN INSTANCE OF EXISTING INTERSECTIONAL MACHINERY
--
-- This file deliberately does not introduce another non-descent, sufficiency,
-- observer-pair, or situated-context ontology.  The repository already owns:
--
--   * IntersectionalNonFactorability:
--       coarse/single-axis collisions block factorisation;
--       post-composition/recharting cannot recover erased information;
--   * RequiredObserverAxisJoinAdequacyExact:
--       multiple required axes must be retained jointly;
--   * IntersectionalLongitudinalResidualDynamics:
--       body/time/place/relation/institution/axis-bundle situated carriers;
--   * SituatedConstituency:
--       affected constituencies may articulate further axes and finite lists
--       are not exhaustive;
--   * RecognitionDistributionRepresentationAxesExact:
--       recognition, distribution and representation do not collapse.
--
-- Clinic-to-Streets contributes only the case-specific projection and residual
-- coordinates needed to instantiate those generic owners.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Longitudinal
import DASHI.Governance.SituatedConstituency as Constituency
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Cognition.ClinicToStreetsCausalProvenanceExact as Clinic

------------------------------------------------------------------------
-- 1. The atomising projection is exactly a coarse/single-axis-style quotient.
------------------------------------------------------------------------

AtomisedSurface : Set
AtomisedSurface = Bool × Bool

atomisingProjection : Clinic.ProvenanceVisibility → AtomisedSurface
atomisingProjection visibility =
  Clinic.ProvenanceVisibility.intimateVisible visibility ,
  Clinic.ProvenanceVisibility.intrapsychicVisible visibility

structuralAxis : Clinic.ProvenanceVisibility → Bool
structuralAxis = Clinic.ProvenanceVisibility.structuralVisible

canonicalAtomisingIntersectionalWitness :
  NF.NonFactorabilityWitness atomisingProjection structuralAxis
canonicalAtomisingIntersectionalWitness =
  NF.nonFactorabilityWitness
    Clinic.fullContext
    Clinic.atomisedContext
    refl
    (λ ())

atomisingProjectionCannotRecoverStructuralAxis :
  NF.FactorsThrough atomisingProjection structuralAxis → ⊥
atomisingProjectionCannotRecoverStructuralAxis =
  NF.witnessRulesOutEveryFlatFactorisation
    canonicalAtomisingIntersectionalWitness

-- Merely relabelling, reweighting, or otherwise post-processing the atomised
-- surface cannot recreate the erased structural coordinate.
atomisingRechartCannotRecoverStructuralAxis :
  ∀ {Recharted : Set} →
  (rechart : AtomisedSurface → Recharted) →
  NF.FactorsThrough (λ state → rechart (atomisingProjection state)) structuralAxis →
  ⊥
atomisingRechartCannotRecoverStructuralAxis rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart canonicalAtomisingIntersectionalWitness

------------------------------------------------------------------------
-- 2. Reskilling/context restoration is existing required-axis join repair.
------------------------------------------------------------------------

structuralResidual : Clinic.ProvenanceVisibility → Bool
structuralResidual = structuralAxis

repairedProjection : Clinic.ProvenanceVisibility → AtomisedSurface × Bool
repairedProjection = AxisJoin.jointAxis atomisingProjection structuralResidual

repairedProjectionRetainsStructuralAxis :
  AxisJoin.RetainsAxis repairedProjection structuralAxis
repairedProjectionRetainsStructuralAxis =
  AxisJoin.jointRetainsRight atomisingProjection structuralResidual

------------------------------------------------------------------------
-- 3. Existing situated/intersectional carrier: family/institution coordinates
-- are explicit but non-exhaustive.  This is a formal adapter, not a claim that
-- the supplied reel empirically measures every listed axis.
------------------------------------------------------------------------

clinicSituatedAxes : List Longitudinal.IntersectionalAxis
clinicSituatedAxes =
  Longitudinal.familyAxis
  ∷ Longitudinal.institutionAxis
  ∷ []

canonicalClinicSituatedCarrier : Longitudinal.IntersectionalResidualCarrier
canonicalClinicSituatedCarrier =
  Longitudinal.mkIntersectionalResidualCarrierOf
    "situated subject / affected constituency"
    2026
    "situated place retained rather than erased"
    "family, intimate, communal and interpersonal relations"
    "clinic and wider social institutions"
    clinicSituatedAxes
    "Clinic-to-Streets is read through situated relation/institution coordinates; the listed axes are illustrative and non-exhaustive."

affectedConstituencyMayArticulateFurtherAxes : Bool
affectedConstituencyMayArticulateFurtherAxes =
  Constituency.affectedConstituencyMayArticulateAxes
    Constituency.canonicalAxisAwareRepresentationBoundary

finiteAxisListExhaustive : Bool
finiteAxisListExhaustive =
  Constituency.axisBundleIsExhaustiveClaimed
    Constituency.canonicalAxisAwareRepresentationBoundary

------------------------------------------------------------------------
-- 4. "Who's at the table" and material effect remain transverse questions.
-- Representation/recognition does not silently pay distribution/material access.
------------------------------------------------------------------------

participationAxesBoundary : Fraser.ParticipationAxesBoundary
participationAxesBoundary = Fraser.canonicalParticipationAxesBoundary

representationPaysMaterialDistribution : Bool
representationPaysMaterialDistribution = false

singleAxisWorldComplete : Bool
singleAxisWorldComplete = false

------------------------------------------------------------------------
-- 5. Explicit reuse ledger: prevents this case layer from drifting back into
-- a parallel generic framework.
------------------------------------------------------------------------

reusesIntersectionalNonFactorability : Bool
reusesIntersectionalNonFactorability = true

reusesRequiredAxisJoin : Bool
reusesRequiredAxisJoin = true

reusesIntersectionalLongitudinalCarrier : Bool
reusesIntersectionalLongitudinalCarrier = true

reusesSituatedConstituency : Bool
reusesSituatedConstituency = true

reusesParticipationAxes : Bool
reusesParticipationAxes = true

record ClinicIntersectionalityReuseBoundary : Set where
  constructor clinic-intersectionality-reuse-boundary
  field
    genericNonFactorabilityReimplemented : Bool
    genericConsumerSufficiencyReimplemented : Bool
    genericObserverPairingReimplemented : Bool
    finiteAxisEnumerationClaimedExhaustive : Bool
    affectedVoiceReplaceableByProxy : Bool
    representationAutomaticallyPaysMaterialAccess : Bool
    caseSpecificProjectionAdapterRetained : Bool
    caseSpecificEmpiricalReceiptsRemainSeparate : Bool

canonicalClinicIntersectionalityReuseBoundary :
  ClinicIntersectionalityReuseBoundary
canonicalClinicIntersectionalityReuseBoundary =
  clinic-intersectionality-reuse-boundary
    false false false false false false true true
