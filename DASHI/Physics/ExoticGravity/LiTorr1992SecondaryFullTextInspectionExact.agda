module DASHI.Physics.ExoticGravity.LiTorr1992SecondaryFullTextInspectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Diligence
import DASHI.Physics.ExoticGravity.LiTorrScalingModelSourceEntitlementBridgeExact as ModelSource

------------------------------------------------------------------------
-- LI/TORR 1992 SECONDARY FULL-TEXT INSPECTION
--
-- The DOI/title identify the canonical PRB article.  The inspected bytes/text
-- used here are a secondary full-text copy of that article, not APS custody.
-- This pays content-inspection/page-locator information while preserving:
--
--   secondary copy != primary publisher carrier.
--
-- It also does NOT identify the paper's sigma-mu model with DASHI's later
-- material-effective-G multiplicative scaling class.
------------------------------------------------------------------------

data CarrierCustody : Set where
  primaryPublisherCustody : CarrierCustody
  secondaryFullTextCopy : CarrierCustody

liTorr1992AttributedArticle : Source.AttributedSource
liTorr1992AttributedArticle = Source.mkDOISource
  "Ning Li; D. G. Torr"
  "Gravitational effects on the magnetic attenuation of superconductors"
  "Physical Review B 46, 5489-5495"
  "1992"
  "10.1103/PhysRevB.46.5489"
  "https://journals.aps.org/prb/abstract/10.1103/PhysRevB.46.5489"
  Source.academicArticleSource
  "source identity for the 1992 Li-Torr paper; separate secondary full-text inspection below is used only for bounded page/equation content"
  Source.publicAttribution

record SecondaryFullTextInspectionReceipt : Set where
  constructor secondary-full-text-inspection-receipt
  field
    sourceCandidate : Diligence.LiTorrTheorySourceCandidate
    sourceMatches1992Candidate : sourceCandidate ≡ Diligence.prb1992Candidate
    attributedArticle : Source.AttributedSource
    attributedArticleMatches : attributedArticle ≡ liTorr1992AttributedArticle
    custody : CarrierCustody
    custodyIsSecondary : custody ≡ secondaryFullTextCopy
    carrierURL : String
    inspectedOn : String
    exactPageEquationLocator : String
    boundedInspectedUse : String

open SecondaryFullTextInspectionReceipt public

liTorr1992SecondaryInspection : SecondaryFullTextInspectionReceipt
liTorr1992SecondaryInspection = secondary-full-text-inspection-receipt
  Diligence.prb1992Candidate
  refl
  liTorr1992AttributedArticle
  refl
  secondaryFullTextCopy
  refl
  "https://unpublished.ca/sites/default/files/letter/263060/Ning%20Li%20Paper1.pdf"
  "2026-09-09"
  "Phys. Rev. B 46, pp. 5493-5494; Eqs. (51)-(54), with Eq. (53) combined with Eq. (39) to introduce the sigma-mu model"
  "secondary full-text inspection supports the bounded claim that the paper develops the sigma-mu conductivity/permeability model in this equation region; no claim is made that this is DASHI's material-effective-G scaling law"

------------------------------------------------------------------------
-- Model-form identity remains a separate residual.
------------------------------------------------------------------------

data SameAsDASHIMaterialEffectiveGScalingPermission : Set where

secondaryInspectionDoesNotCreateSameModelForm :
  SameAsDASHIMaterialEffectiveGScalingPermission → ⊥
secondaryInspectionDoesNotCreateSameModelForm ()

record LiTorr1992InspectionBoundary : Set where
  constructor li-torr-1992-inspection-boundary
  field
    doiIdentityKnown : Bool
    secondaryFullTextContentInspected : Bool
    primaryAPSCustodyInspectedThroughThisReceipt : Bool
    exactEquationRegionLocatedInSecondaryCopy : Bool
    sigmaMuModelAutomaticallyEqualsMaterialEffectiveGModel : Bool
    secondaryCopyAutomaticallyBecomesPrimaryCarrier : Bool
    inspectionAutomaticallyProvesPhysicalCorrectness : Bool
    inspectionAutomaticallyProvesNegativeEffectiveG : Bool
    sameModelFormReceiptStillRequiredForScalingImport : Bool

canonicalLiTorr1992InspectionBoundary : LiTorr1992InspectionBoundary
canonicalLiTorr1992InspectionBoundary =
  li-torr-1992-inspection-boundary
    true true false true false false false false true

existingScalingSourceBoundary : ModelSource.LiTorrScalingModelSourceBoundary
existingScalingSourceBoundary = ModelSource.canonicalLiTorrScalingModelSourceBoundary
