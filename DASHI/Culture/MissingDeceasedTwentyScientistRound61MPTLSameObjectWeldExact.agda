module DASHI.Culture.MissingDeceasedTwentyScientistRound61MPTLSameObjectWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound57FirstRealAcquisitionAssessmentExact as R57
import DASHI.Culture.MissingDeceasedTwentyScientistRound59MPTLAchromatAcquisitionExact as R59
import DASHI.Culture.MissingDeceasedTwentyScientistRound60MPTLECRExternalCitationExact as R60

------------------------------------------------------------------------
-- ROUND 61: MPTL SAME-OBJECT WELD
--
-- 2024 IEEE IPMHVC programme P2-29 explicitly co-names Aaron M. Brandes,
-- M. Schulze, A. Press and J. Campos on one presentation titled
-- "Multi-Pulse Test Line (MPTL)" from Los Alamos National Laboratory.
--
-- This closes the previous Press <-> Schulze/Brandes same-named-object gap.
-- Chavez is separately paid on an exact MPTL beam-position-monitor report.
-- No second retained scientist is yet located on the exact MPTL object family.
------------------------------------------------------------------------

record SameObjectConferenceReceipt : Set where
  constructor same-object-conference-receipt
  field
    sourceOwner : String
    sourceKind : String
    nativeLocator : String
    eventReference : String
    presentationIdentifier : String
    presentationTitle : String
    authors : String
    affiliation : String
    sameNamedObjectReference : String
    sourceBoundary : String

open SameObjectConferenceReceipt public

ipmhvcMPTLPosterReceipt : SameObjectConferenceReceipt
ipmhvcMPTLPosterReceipt = same-object-conference-receipt
  "IEEE International Power Modulator and High Voltage Conference programme"
  "conference programme / presentation roster"
  "https://www.ipmhvc.com/wp-content/uploads/2024/04/IPMHVC-2024-ConfTool-Schedule-With-Presentations-20240425.pdf"
  "2024 IEEE IPMHVC"
  "P2-29"
  "Multi-Pulse Test Line (MPTL)"
  "A. M. Brandes; M. Schulze; A. Press; J. Campos"
  "Los Alamos National Lab"
  "literal title-level MPTL co-authorship/presentation object"
  "Pays co-naming on this exact conference presentation only; does not by itself prove each author's role on every MPTL drawing, review, report or hardware revision."

brandesSchulzePressSameNamedMPTLObjectPaid : Bool
brandesSchulzePressSameNamedMPTLObjectPaid = true

pressToSchulzeBrandesGapClosed : Bool
pressToSchulzeBrandesGapClosed = true

jCamposSameNamedMPTLObjectPaid : Bool
jCamposSameNamedMPTLObjectPaid = true

------------------------------------------------------------------------
-- Existing exact MPTL objects now sit in one explicit object family.
------------------------------------------------------------------------

chavezMPTLObjectPaid : Bool
chavezMPTLObjectPaid = true

schulzeAchromatMPTLObjectPaid : Bool
schulzeAchromatMPTLObjectPaid = true

brandesMPTLECRObjectPaid : Bool
brandesMPTLECRObjectPaid = true

pressMPTLPresentationObjectPaid : Bool
pressMPTLPresentationObjectPaid = true

mptlNamedPersonnelSurfaceNowIncludesBrandesSchulzePressCamposChavez : Bool
mptlNamedPersonnelSurfaceNowIncludesBrandesSchulzePressCamposChavez = true

------------------------------------------------------------------------
-- Retained-person promotion boundary.
------------------------------------------------------------------------

secondRetainedScientistOnMPTLPaid : Bool
secondRetainedScientistOnMPTLPaid = false

sameNamedMPTLObjectDoesNotPaySecondRetainedPerson : Bool
sameNamedMPTLObjectDoesNotPaySecondRetainedPerson = true

sameNamedObjectFamilyDoesNotEraseRevisionOrRoleGranularity : Bool
sameNamedObjectFamilyDoesNotEraseRevisionOrRoleGranularity = true

nonRetainedCoauthorsDoNotPayH2 : Bool
nonRetainedCoauthorsDoNotPayH2 = true

------------------------------------------------------------------------
-- Acquisition consequence.
------------------------------------------------------------------------

round61NarrowedResidual : String
round61NarrowedResidual = "Search exact P2-29 derivative abstract/poster/proceedings and MPTL ECR/design-review support material for J. Campos full identity, explicit report/drawing cross-references, approval/reviewer lists and any second retained scientist. The Press-Schulze-Brandes same-named MPTL seam is now paid and should no longer consume acquisition budget."

round61H2PaidCount : Nat
round61H2PaidCount = 0

round61H3PaidCount : Nat
round61H3PaidCount = 0

round61Reading : String
round61Reading = "The MPTL branch now has a literal same-object personnel weld: IPMHVC 2024 P2-29 co-names A. M. Brandes, M. Schulze, A. Press and J. Campos on 'Multi-Pulse Test Line (MPTL)'. This closes the earlier Press-to-Schulze/Brandes same-named-object gap. Anthony/Mark Anthony Chavez is separately named on an exact MPTL beam-position-monitor report, so the MPTL object family now has a richer named engineering graph. Only Chavez is retained in the twenty, however; no second retained scientist has been located on the exact MPTL object family, so H2/H3 remain unpaid."
