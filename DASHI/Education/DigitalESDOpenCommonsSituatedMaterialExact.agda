module DASHI.Education.DigitalESDOpenCommonsSituatedMaterialExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDOpenKnowledgeCommonsCollaborationExact as Commons
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact as Material
import DASHI.Ontology.DeweyQidCoverageQualityExact as Identity

------------------------------------------------------------------------
-- THIN COMPOSITION ONLY
--
-- The open-commons architecture does not replace any of the canonical audits.
-- A globally visible, linked and editable curriculum can still exclude people,
-- externalise material burdens, or carry incorrect entity/source assertions.
------------------------------------------------------------------------

commonsBoundary : Commons.OpenKnowledgeCommonsBoundary
commonsBoundary = Commons.canonicalOpenKnowledgeCommonsBoundary

absenceQuestionCount : Nat
absenceQuestionCount = Absence.absenceAuditQuestionCount

materialStageCount : Nat
materialStageCount = Material.digitalMaterialStageCount

qidCoverageBoundary : Identity.CoverageQualityBoundary
qidCoverageBoundary = Identity.canonicalCoverageQualityBoundary

absenceReading : String
absenceReading = Absence.intersectionalAbsenceReading

materialReading : String
materialReading = Material.materialEnvironmentalReading

record OpenCommonsBoundary : Set where
  constructor open-commons-boundary
  field
    openCommonsClosesWhoMissingAudit : Bool
    openCommonsClosesWhoMissingAuditIsFalse :
      openCommonsClosesWhoMissingAudit ≡ false
    openCommonsClosesMaterialAudit : Bool
    openCommonsClosesMaterialAuditIsFalse :
      openCommonsClosesMaterialAudit ≡ false
    qidCoverageCreatesSemanticTruth : Bool
    qidCoverageCreatesSemanticTruthIsFalse :
      qidCoverageCreatesSemanticTruth ≡ false
    openCollaborationCreatesRepresentativeParticipation : Bool
    openCollaborationCreatesRepresentativeParticipationIsFalse :
      openCollaborationCreatesRepresentativeParticipation ≡ false
    openCollaborationCreatesLowEnvironmentalBurden : Bool
    openCollaborationCreatesLowEnvironmentalBurdenIsFalse :
      openCollaborationCreatesLowEnvironmentalBurden ≡ false
    allFourAuditsRetained : Bool
    allFourAuditsRetainedIsTrue : allFourAuditsRetained ≡ true

open OpenCommonsBoundary public

canonicalOpenCommonsBoundary : OpenCommonsBoundary
canonicalOpenCommonsBoundary =
  open-commons-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

openCommonsSituatedMaterialReading : String
openCommonsSituatedMaterialReading =
  "Open/shared curriculum, intersectional representation, material/environmental substrate and QID/provenance are independent audit axes. Public contribution and multilingual adaptation do not answer who is absent; open-source/OER practice does not dematerialise chips, devices, networks, energy, water, repair or e-waste; QID coverage supplies external entity addressability but not semantic truth. A sustainable global knowledge commons must retain all four audits simultaneously."
