{-# OPTIONS --safe #-}
module DASHI.Unified.FleetFormalGapTargetTOEExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.PNFSpectralCoordinateRebuildability as Rebuild
import DASHI.Interop.PNFSpectralNumericABICore as Numeric
import DASHI.Interop.PNFResidualFieldInvariants as Residual
import DASHI.Planning.PlanningPNFClaimBoundaryExact as Planning
import DASHI.Promotion.ObligationIndex as Obligation
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as ParetoSnowball

------------------------------------------------------------------------
-- Fleet R4/R5 selection boundary.
--
-- External execution context:
--   chboishabba/ITIR-suite
--   COMPACTIFIED_CONTEXT.md
--   docs/planning/fleet_topical_pnf_world_model_convergence_20261027.md
--
-- The external receipt reports an R4 numeric spectral reduction and an R5
-- formal-AST subtraction.  This module does not re-run either producer.
-- It does not promote the external counts or eigenvalues into theorem truth.
-- It only binds the reported planning frontier to existing DASHI owners.
------------------------------------------------------------------------

record FleetFormalGapTargetReceipt : Set where
  constructor fleet-formal-gap-target-receipt
  field
    externalSourceRepository : String
    externalSourceSurface : String
    spectralNumericABI : String
    spectralParityHash : String
    sourceFormalStemCount : Nat
    dischargedCoreKnowledgeFibres : Nat
    polarityContradictionGaps : Nat
    unformalisedFormalGaps : Nat
    macroscopicEigenMotifCount : Nat
    firstEigenvalueLabel : String
    secondEigenvalueLabel : String
    thirdEigenvalueLabel : String
    targetOnlyUnformalisedFormalGaps : Bool
    dischargedFibresRemainDischarged : Bool
    contradictionGapsRemainSeparate : Bool
    eigenvalueMagnitudeCreatesProofAuthority : Bool
    externalCountCreatesFormalProof : Bool
    externalPlanningTextCreatesFormalResidual : Bool
    metaIntrospectorAttributionPreserved : Bool
    esdSurfaceEdited : Bool

open FleetFormalGapTargetReceipt public

canonicalFleetFormalGapTargetReceipt : FleetFormalGapTargetReceipt
canonicalFleetFormalGapTargetReceipt =
  fleet-formal-gap-target-receipt
    "chboishabba/ITIR-suite"
    "COMPACTIFIED_CONTEXT.md; docs/planning/fleet_topical_pnf_world_model_convergence_20261027.md"
    "itir.pnf.spectral_numeric_abi.v0_2"
    "6853373e81e551aea8fca490ce2ad9f5264664d49bde8804edfc4e98e7517799"
    13344
    584
    44
    58
    3
    "lambda1=74.5526; external planning label: Balaban RG"
    "lambda2=18.8350; external planning label: NS BM2"
    "lambda3=5.5865; external planning label: Quantum Mereology"
    true
    true
    true
    false
    false
    false
    true
    false

------------------------------------------------------------------------
-- Exact values of the recorded external planning receipt.
-- These equalities validate this DASHI wrapper only.
-- They do not validate the external producer run.
------------------------------------------------------------------------

fleetRecordedDischargedCountIs584 :
  dischargedCoreKnowledgeFibres canonicalFleetFormalGapTargetReceipt ≡ 584
fleetRecordedDischargedCountIs584 = refl

fleetRecordedContradictionCountIs44 :
  polarityContradictionGaps canonicalFleetFormalGapTargetReceipt ≡ 44
fleetRecordedContradictionCountIs44 = refl

fleetRecordedUnformalisedGapCountIs58 :
  unformalisedFormalGaps canonicalFleetFormalGapTargetReceipt ≡ 58
fleetRecordedUnformalisedGapCountIs58 = refl

fleetRecordedMacroscopicMotifCountIs3 :
  macroscopicEigenMotifCount canonicalFleetFormalGapTargetReceipt ≡ 3
fleetRecordedMacroscopicMotifCountIs3 = refl

fleetTargetsOnlyUnformalisedFormalGaps :
  targetOnlyUnformalisedFormalGaps canonicalFleetFormalGapTargetReceipt ≡ true
fleetTargetsOnlyUnformalisedFormalGaps = refl

fleetDoesNotRetargetDischargedFibres :
  dischargedFibresRemainDischarged canonicalFleetFormalGapTargetReceipt ≡ true
fleetDoesNotRetargetDischargedFibres = refl

fleetKeepsContradictionsSeparate :
  contradictionGapsRemainSeparate canonicalFleetFormalGapTargetReceipt ≡ true
fleetKeepsContradictionsSeparate = refl

------------------------------------------------------------------------
-- Reused canonical proof and receipt owners.
------------------------------------------------------------------------

fleetCoordinateRebuildabilityReceipt :
  Rebuild.PNFSpectralCoordinateRebuildabilityReceipt
fleetCoordinateRebuildabilityReceipt =
  Rebuild.canonicalPNFSpectralCoordinateRebuildabilityReceipt

fleetNumericABIReceipt :
  Numeric.PNFSpectralNumericABICoreReceipt
fleetNumericABIReceipt =
  Numeric.canonicalPNFSpectralNumericABICoreReceipt

fleetResidualInvariantReceipt :
  Residual.PNFResidualFieldInvariantReceipt
fleetResidualInvariantReceipt =
  Residual.canonicalPNFResidualFieldInvariantReceipt

fleetPlanningBoundary :
  Planning.PNFPlanningAdapterBoundary
fleetPlanningBoundary =
  Planning.canonicalPNFPlanningAdapterBoundary

fleetPromotionObligationIndex :
  Obligation.UnifiedPromotionObligationIndex
fleetPromotionObligationIndex =
  Obligation.canonicalUnifiedPromotionObligationIndex

fleetVectorCoordinateDoesNotCreateTruth :
  Rebuild.vectorCoordinateIsTruth ≡ false
fleetVectorCoordinateDoesNotCreateTruth =
  Rebuild.vectorCoordinateTruthFalse

PlanningSourceTextFormalResidualFlag : Set
PlanningSourceTextFormalResidualFlag =
  Planning.PNFPlanningAdapterBoundary.sourceTextAloneCreatesFormalResidual
    Planning.canonicalPNFPlanningAdapterBoundary
  ≡ false

fleetPlanningTextDoesNotCreateFormalResidual :
  PlanningSourceTextFormalResidualFlag
fleetPlanningTextDoesNotCreateFormalResidual =
  Planning.PNFPlanningAdapterBoundary.sourceTextAloneCreatesFormalResidualIsFalse
    Planning.canonicalPNFPlanningAdapterBoundary

------------------------------------------------------------------------
-- Exact non-promotion gates for the external fleet selection.
------------------------------------------------------------------------

data FleetEigenPriorityCreatesProof : Set where

fleetEigenPriorityDoesNotCreateProof :
  FleetEigenPriorityCreatesProof → ⊥
fleetEigenPriorityDoesNotCreateProof ()

data FleetExternalCountCreatesFormalDischarge : Set where

fleetExternalCountDoesNotCreateFormalDischarge :
  FleetExternalCountCreatesFormalDischarge → ⊥
fleetExternalCountDoesNotCreateFormalDischarge ()

data FleetDischargedFibreRetargetPermission : Set where

fleetDischargedFibresCannotBeRetargetedByThisBoundary :
  FleetDischargedFibreRetargetPermission → ⊥
fleetDischargedFibresCannotBeRetargetedByThisBoundary ()

data FleetContradictionGapReclassificationPermission : Set where

fleetContradictionsCannotBeRelabelledAsFormalGaps :
  FleetContradictionGapReclassificationPermission → ⊥
fleetContradictionsCannotBeRelabelledAsFormalGaps ()

------------------------------------------------------------------------
-- Reuse the existing O/R/C/S/L/P/G/F process carrier.
------------------------------------------------------------------------

canonicalFleetFormalGapZKPFrame : ParetoSnowball.TOEZKPFrame
canonicalFleetFormalGapZKPFrame =
  ParetoSnowball.toe-zkp-frame
    "target only the externally reported 58 unformalised formal gaps after the 584 discharged fibres remain excluded"
    "reuse canonical PNF spectral, residual, planning, obligation, Balaban and Ibrahim owners"
    "bind one external fleet planning receipt to existing owners; add no duplicate theorem owner"
    "spectral rank, external counts, planning labels and contradiction classes do not create proof authority or formal discharge"
    "one disjoint fleet residual-selection normalization lane"
    "the R4/R5 receipt is external context; canonical DASHI owners remain proof authority; ESD surfaces are read-only"
    "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma and C4/PlantUML are process lenses only; meta-introspector attribution remains separate"
    "TOE consumers expose the 58-gap target boundary while the 584 discharged fibres and 44 contradiction gaps remain outside that target"
    "reuse/duplicate search, exact-branch read-back, trust-escape scan, ESD diff scan and owner-alias validation"
    false
    false
    false
    false
