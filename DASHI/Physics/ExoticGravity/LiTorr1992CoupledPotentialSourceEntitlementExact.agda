module DASHI.Physics.ExoticGravity.LiTorr1992CoupledPotentialSourceEntitlementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorr1992SecondaryFullTextInspectionExact as Inspection
import DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact as LiTorr

------------------------------------------------------------------------
-- 1992 COUPLED-POTENTIAL SOURCE ENTITLEMENT
--
-- The inspected secondary full-text copy of the DOI-identified 1992 article
-- supports the bounded historical equation-shape transcription around Eqs.
-- (33)-(35): the supercurrent and the separate electromagnetic / gravito-
-- magnetic response equations use the same combined A + (m/q) A_g coordinate.
--
-- This is source attribution for a historical model shape, not physical
-- validation and not entitlement for DASHI's later material-effective-G model.
------------------------------------------------------------------------

data EquationShapeClaim : Set where
  combinedPotentialFeedsSupercurrent : EquationShapeClaim
  sameCombinedPotentialFeedsSeparateResponses : EquationShapeClaim

record LiTorr1992EquationShapeEntitlement
    (claim : EquationShapeClaim) : Set where
  constructor li-torr-1992-equation-shape-entitlement
  field
    inspection : Inspection.SecondaryFullTextInspectionReceipt
    inspectionMatchesCanonical : inspection ≡ Inspection.liTorr1992SecondaryInspection
    exactLocator : String
    sourceEntitledScope : String
    transcriptionCarrier : String

open LiTorr1992EquationShapeEntitlement public

combinedPotentialEntitlement :
  LiTorr1992EquationShapeEntitlement combinedPotentialFeedsSupercurrent
combinedPotentialEntitlement =
  li-torr-1992-equation-shape-entitlement
    Inspection.liTorr1992SecondaryInspection
    refl
    "Phys. Rev. B 46, p. 5492; Eq. (33), with Eqs. (37)-(40) continuing the A / A_g current-response algebra"
    "historical equation-shape claim: the superconducting current is written using the combined electromagnetic and gravitomagnetic potential coordinate A + (m/q) A_g"
    "DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact.canonicalCoupledPotentialChart"

separateResponseEntitlement :
  LiTorr1992EquationShapeEntitlement sameCombinedPotentialFeedsSeparateResponses
separateResponseEntitlement =
  li-torr-1992-equation-shape-entitlement
    Inspection.liTorr1992SecondaryInspection
    refl
    "Phys. Rev. B 46, p. 5492; Eqs. (34)-(35)"
    "historical equation-shape claim: separate electromagnetic and gravitomagnetic response equations are written from the same combined potential coordinate"
    "DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact.canonicalCoupledResponseEquations"

------------------------------------------------------------------------
-- Exact owner weld: these source-entitled historical shapes are attached to
-- the existing Li/Torr owner, not to the later negative-G interpretation.
------------------------------------------------------------------------

record CoupledPotentialSourceWeld : Set where
  constructor coupled-potential-source-weld
  field
    combinedPotentialSource :
      LiTorr1992EquationShapeEntitlement combinedPotentialFeedsSupercurrent
    separateResponsesSource :
      LiTorr1992EquationShapeEntitlement sameCombinedPotentialFeedsSeparateResponses
    coupledPotentialConsumer : LiTorr.CoupledPotentialChart
    coupledResponseConsumer : LiTorr.CoupledResponseEquations
    consumerChartMatchesCanonical :
      coupledPotentialConsumer ≡ LiTorr.canonicalCoupledPotentialChart
    consumerResponsesMatchCanonical :
      coupledResponseConsumer ≡ LiTorr.canonicalCoupledResponseEquations

open CoupledPotentialSourceWeld public

canonicalCoupledPotentialSourceWeld : CoupledPotentialSourceWeld
canonicalCoupledPotentialSourceWeld = coupled-potential-source-weld
  combinedPotentialEntitlement
  separateResponseEntitlement
  LiTorr.canonicalCoupledPotentialChart
  LiTorr.canonicalCoupledResponseEquations
  refl refl

record CoupledPotentialAttributionBoundary : Set where
  constructor coupled-potential-attribution-boundary
  field
    secondaryInspectionMaySupportBoundedHistoricalEquationShape : Bool
    secondaryInspectionEqualsPrimaryPublisherCustody : Bool
    equationShapeAttributionProvesPhysicalCorrectness : Bool
    equationShapeAttributionProvesConstitutiveEnhancement : Bool
    equationShapeAttributionProvesMaterialEffectiveNegativeG : Bool
    equationShapeAttributionRetroactivelyBecomesAmyStatement : Bool

canonicalCoupledPotentialAttributionBoundary : CoupledPotentialAttributionBoundary
canonicalCoupledPotentialAttributionBoundary =
  coupled-potential-attribution-boundary true false false false false false
