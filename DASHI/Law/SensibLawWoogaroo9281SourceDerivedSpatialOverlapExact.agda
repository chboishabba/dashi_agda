module DASHI.Law.SensibLawWoogaroo9281SourceDerivedSpatialOverlapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 9281/2024/OW P3 SOURCE-DERIVED SPATIAL OVERLAP
--
-- This owner records a high-alpha raster/geometric investigative receipt.
-- It deliberately does not promote image registration into authoritative CAD,
-- does not let a generic plan note saying "EPBC approval" identify a specific
-- Commonwealth instrument, and does not let the pre-existing 2014/7306 overlap
-- pay authorisation for the separate 2019/8575 action.
--
-- Snowball rule: acquisition may run out of dependency order; conclusion
-- payment may not skip same-object identity, source manifestation, authoritative
-- geometry or the literal Commonwealth instrument relied on under condition 6(a).
------------------------------------------------------------------------

data SourceClass : Set where
  councilApprovedPlan : SourceClass
  proponentEcologyPlan : SourceClass
  commonwealthPreliminaryDocumentation : SourceClass
  sourceDerivedAnalytical : SourceClass

data P3Coordinate : Set where
  localApprovedWorks : P3Coordinate
  localTreeRetentionRemoval : P3Coordinate
  commonwealthPlanA1 : P3Coordinate
  epbc2014Overlap : P3Coordinate
  epbc8575ProposedUrban : P3Coordinate
  condition6aFederalInstrument : P3Coordinate
  authoritativeLocalGeometry : P3Coordinate

record BoundedSpatialReceipt : Set where
  constructor bounded-spatial-receipt
  field
    sourceClass : SourceClass
    coordinate : P3Coordinate
    sourceLocator : String
    boundedStatement : String
    primarySameObjectSource : Bool
    authoritativeVectorGeometry : Bool

open BoundedSpatialReceipt public

cherishTreePlanSameObjectBridge : BoundedSpatialReceipt
cherishTreePlanSameObjectBridge = bounded-spatial-receipt
  proponentEcologyPlan
  localTreeRetentionRemoval
  "A10552668 — Tree Retention and Removal Plan, Village 2 Stages 1 to 16 Bulk Earthworks; Lot 9999 SP292760; Cherish Enterprises Pty Ltd; Springview"
  "The 9281 supporting tree plan repeatedly identifies the mapped Village 2 Stages 1 to 16 bulk-earthworks object with Cherish Enterprises Pty Ltd and Lot 9999 SP292760. This is a same-object project-material bridge, not a corporate-ownership conclusion."
  true
  false

stocklandTreeScheduleSameObjectBridge : BoundedSpatialReceipt
stocklandTreeScheduleSameObjectBridge = bounded-spatial-receipt
  proponentEcologyPlan
  localTreeRetentionRemoval
  "A10552668 tree schedule — Kalina - Village 2, Springfield (Stockland Development Pty Ltd)"
  "The same tree-plan package later titles its tree schedule Kalina - Village 2, Springfield (Stockland Development Pty Ltd). The dual Cherish/Stockland manifestation strengthens project-object continuity while leaving ownership/control questions separate."
  true
  false

approvedGeneralArrangementEPBCApprovalNote : BoundedSpatialReceipt
approvedGeneralArrangementEPBCApprovalNote = bounded-spatial-receipt
  councilApprovedPlan
  localApprovedWorks
  "A12705838, general arrangement KV2-AAP-BE-P1-DRG-CI-0061, general clearing and earthworks note 10"
  "The approved local plan states that clearing by the contractor must be in accordance with the Council-approved vegetation management plan and EPBC approval. The phrase EPBC approval does not identify which Commonwealth approval instrument applies to which polygon."
  true
  false

sourceDerivedBoundaryRegistrationReceipt : BoundedSpatialReceipt
sourceDerivedBoundaryRegistrationReceipt = bounded-spatial-receipt
  sourceDerivedAnalytical
  epbc8575ProposedUrban
  "Raster registration: A10552668 overview Site DCDB boundary aligned to EPBC 2019/8575 Plan A1 by boundary-shape matching; Plan A1 printed graticule used for WGS84 calibration"
  "The source-derived registration aligns the distinctive local site boundary to Plan A1 and places the Stage 1 to 16 works footprint predominantly within Plan A1 proposed-urban land. It is suitable for investigative routing and falsification, not authoritative legal geometry."
  false
  false

------------------------------------------------------------------------
-- Approximate analytical quantities.
-- Unit is centi-hectares to avoid manufacturing floating-point proof claims.
-- 4174 = about 41.74 ha; 828 = about 8.28 ha; 3284 = about 32.84 ha.
------------------------------------------------------------------------

approxStageFootprintCentiHa : Nat
approxStageFootprintCentiHa = 4174

approxEPBC2014OverlapCentiHa : Nat
approxEPBC2014OverlapCentiHa = 828

approxStagePinkOutside2014CentiHa : Nat
approxStagePinkOutside2014CentiHa = 3284

record ApproximateOverlapReceipt : Set where
  constructor approximate-overlap-receipt
  field
    stageFootprintCentiHa : Nat
    stageIntersect2014CentiHa : Nat
    stagePlanA1UrbanOutsideDetected2014CentiHa : Nat
    imageDerived : Bool
    authoritative : Bool
    mayProveFederalContraventionAlone : Bool

approximateP3Receipt : ApproximateOverlapReceipt
approximateP3Receipt = approximate-overlap-receipt
  approxStageFootprintCentiHa
  approxEPBC2014OverlapCentiHa
  approxStagePinkOutside2014CentiHa
  true false false

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data GenericEPBCApprovalIdentifiesInstrument : Set where
data SourceDerivedRasterEqualsAuthoritativeGeometry : Set where
data EPBC2014OverlapPays8575Authorisation : Set where
data SameShapeRegistrationPaysContravention : Set where
data CherishStocklandSameObjectPaysCommonOwnership : Set where

genericEPBCApprovalDoesNotIdentifyInstrument : GenericEPBCApprovalIdentifiesInstrument → ⊥
genericEPBCApprovalDoesNotIdentifyInstrument ()

sourceDerivedRasterDoesNotEqualAuthoritativeGeometry : SourceDerivedRasterEqualsAuthoritativeGeometry → ⊥
sourceDerivedRasterDoesNotEqualAuthoritativeGeometry ()

epbc2014OverlapDoesNotPay8575Authorisation : EPBC2014OverlapPays8575Authorisation → ⊥
epbc2014OverlapDoesNotPay8575Authorisation ()

sameShapeRegistrationDoesNotPayContravention : SameShapeRegistrationPaysContravention → ⊥
sameShapeRegistrationDoesNotPayContravention ()

cherishStocklandSameObjectDoesNotPayCommonOwnership : CherishStocklandSameObjectPaysCommonOwnership → ⊥
cherishStocklandSameObjectDoesNotPayCommonOwnership ()

------------------------------------------------------------------------
-- First-paying leaves.
------------------------------------------------------------------------

record P3Residual : Set where
  constructor p3-residual
  field
    coordinate : P3Coordinate
    exactMissingObject : String
    whyNeeded : String
    mayBeAcquiredOutOfOrder : Bool
    conclusionMaySkip : Bool

open P3Residual public

condition6aSubmissionRemainsFirstInstrumentLeaf : P3Residual
condition6aSubmissionRemainsFirstInstrumentLeaf = p3-residual
  condition6aFederalInstrument
  "The actual condition 6(a) submission to Ipswich City Council: either DCCEEW evidence that the proposed clearing is not a controlled action or the literal Commonwealth approval relied on for that clearing."
  "The approved drawing's generic reference to EPBC approval cannot distinguish the pre-existing EPBC 2014/7306 approval from any approval required for EPBC 2019/8575. The condition-satisfaction record can identify the instrument actually relied on."
  true false

authoritativeCADGISRemainsFirstGeometryLeaf : P3Residual
authoritativeCADGISRemainsFirstGeometryLeaf = p3-residual
  authoritativeLocalGeometry
  "Original Arcadis/Saunders Havill CAD/GIS or another authoritative vector export for the 9281 extent-of-work and vegetation-clearing polygons, together with authoritative Commonwealth polygons for 2014/7306 and 2019/8575."
  "The source-derived raster receipt strongly localises the decisive overlap but cannot substitute for survey/CAD geometry in a final same-controlled-action conclusion."
  true false

record P3Pareto : Set where
  constructor p3-pareto
  field
    condition6aBeforeInstrumentConclusion : Bool
    authoritativeGeometryBeforeFinalOverlapConclusion : Bool
    separate2014And2019FederalActions : Bool
    sourceDerivedGeometryUsefulForAcquisition : Bool
    sourceDerivedGeometryMayPayLegalContravention : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool

canonicalP3Pareto : P3Pareto
canonicalP3Pareto = p3-pareto true true true true false true false
