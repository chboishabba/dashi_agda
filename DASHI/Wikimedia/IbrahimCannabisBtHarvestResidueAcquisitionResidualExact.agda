module DASHI.Wikimedia.IbrahimCannabisBtHarvestResidueAcquisitionResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisBtCannabisUseProductExact as Product
import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Measurement
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- Bt HARVEST-RESIDUE ACQUISITION RESIDUAL
--
-- Exact cannabis-use products are now paid. The remaining empirical gap is a
-- same-object post-application harvested-flower burden for viable Btk and/or
-- Cry protein. Nearby cannabis microbial literature does not pay that object.
------------------------------------------------------------------------

record BtHarvestResidueStatus : Set where
  constructor bt-harvest-residue-status
  field
    productIdentityReference : String
    strainIdentityReference : String
    applicationCarrierReference : String
    postHarvestCannabisCFUReference : String
    postHarvestCryProteinReference : String
    strainSpecificMolecularReference : String
    nearestCannabisEvidenceReference : String
    exactPostApplicationBurdenPaid : Bool
open BtHarvestResidueStatus public

currentBtHarvestResidual : BtHarvestResidueStatus
currentBtHarvestResidual = bt-harvest-residue-status
  "DiPel Pro DF / ABTS-351 in California and Bioprotec PLUS / EVB113-19 in Canada are exact cannabis-use product objects"
  "strain identity paid by regulatory/product records"
  "application rate/timing paid where label-specific; exact treated-harvest sample remains unacquired"
  "unresolved: no public same-object study located measuring viable Btk CFU/spores on harvested cannabis flower after a known Btk application"
  "unresolved: no public same-object study located measuring Cry protein burden on harvested cannabis flower after a known Btk application"
  "unresolved: no post-harvest strain-specific PCR/qPCR packet located for Btk-treated cannabis flower"
  "Cannabis post-harvest microbiology studies quantify generic TAMC/TYM and note stage-specific microbial buildup is incompletely characterised; this does not identify applied Btk"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GenericTAMCIdentifiesAppliedBtk : Set where
data CannabisBtLabelCreatesHarvestCFU : Set where
data ZeroDayPHICreatesZeroBtBurden : Set where

genericTAMCDoesNotIdentifyAppliedBtk : GenericTAMCIdentifiesAppliedBtk → ⊥
genericTAMCDoesNotIdentifyAppliedBtk ()

labelDoesNotCreateHarvestCFU : CannabisBtLabelCreatesHarvestCFU → ⊥
labelDoesNotCreateHarvestCFU ()

zeroDayPHIDoesNotCreateZeroBtBurden : ZeroDayPHICreatesZeroBtBurden → ⊥
zeroDayPHIDoesNotCreateZeroBtBurden ()

------------------------------------------------------------------------
-- Acquisition Pareto.
------------------------------------------------------------------------

data BtResidueParetoTarget : Set where
  targetedCannabisFieldStudy
  archivedRegulatoryResidueStudy
  strainSpecificQPCR
  cryProteinImmunoassay
  routeFate : BtResidueParetoTarget

record BtResidueParetoStep : Set where
  constructor bt-residue-pareto-step
  field
    priority : Nat
    target : BtResidueParetoTarget
    action : String
    pays : String
open BtResidueParetoStep public

pareto0 : BtResidueParetoStep
pareto0 = bt-residue-pareto-step
  0 archivedRegulatoryResidueStudy
  "search PMRA/EPA/EFSA registration dossiers and residue studies for harvested commodity burdens tied to ABTS-351 or EVB113-19; prefer cannabis/hemp but retain crop identity"
  "existing experimental residue packet if public"

pareto1 : BtResidueParetoStep
pareto1 = bt-residue-pareto-step
  1 targetedCannabisFieldStudy
  "locate or design a same-product cannabis experiment measuring pre-application, post-application and harvest-time burden"
  "cannabis-specific decay/persistence trajectory"

pareto2 : BtResidueParetoStep
pareto2 = bt-residue-pareto-step
  2 strainSpecificQPCR
  "use strain-specific or cry-gene molecular markers alongside culture counts so ambient Bacillus does not collapse into applied Btk"
  "organism/strain identity at harvest"

pareto3 : BtResidueParetoStep
pareto3 = bt-residue-pareto-step
  3 cryProteinImmunoassay
  "quantify Cry proteins independently from viable cells/spores"
  "protein burden at harvest"

pareto9 : BtResidueParetoStep
pareto9 = bt-residue-pareto-step
  9 routeFate
  "defer smoking/vaping transfer until source burden exists"
  "consumer exposure bridge"

record BtHarvestResidueBoundary : Set where
  constructor bt-harvest-residue-boundary
  field
    exactCannabisUseProductsPaid : Bool
    genericMicrobialCountsSufficient : Bool
    harvestBtBurdenPaid : Bool
    routeFateDominatedBySourceBurden : Bool
open BtHarvestResidueBoundary public

canonicalBtHarvestResidueBoundary : BtHarvestResidueBoundary
canonicalBtHarvestResidueBoundary =
  bt-harvest-residue-boundary true false false true
