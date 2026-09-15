module DASHI.Culture.MissingDeceasedTwentyScientistRound62MPTLAchromatPublicationWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound59MPTLAchromatAcquisitionExact as R59
import DASHI.Culture.MissingDeceasedTwentyScientistRound61MPTLSameObjectWeldExact as R61

------------------------------------------------------------------------
-- ROUND 62: FORMAL ACHROMAT PUBLICATION WELD
--
-- A 2025 IEEE Pulsed Power & Plasma Science proceedings entry co-names Press,
-- Brandes, Campos, Schulze and Jaworski on an exact 90-degree achromatic-bend
-- paper.  This strengthens the lifecycle from 2022 design note -> 2024 MPTL
-- poster/ECR -> 2025 formal technical publication.
------------------------------------------------------------------------

record TechnicalPublicationReceipt : Set where
  constructor technical-publication-receipt
  field
    sourceOwner : String
    sourceKind : String
    nativeLocator : String
    publicationReference : String
    publicationTitle : String
    authors : String
    publicationYear : String
    exactObjectReference : String
    sourceBoundary : String

open TechnicalPublicationReceipt public

ieeeAchromatPublicationReceipt : TechnicalPublicationReceipt
ieeeAchromatPublicationReceipt = technical-publication-receipt
  "IEEE Pulsed Power & Plasma Science proceedings"
  "conference proceedings bibliographic carrier"
  "https://www.proceedings.com/content/083/083021webtoc.pdf"
  "2025 IEEE PPPS"
  "90-Degree Achromatic Bend for Transport of an Intense Electron Beam with Nominal Energy Spread of 16-17 MeV"
  "A. F. Press; A. M. Brandes; J. M. Campos; M. Schulze; M. A. Jaworski"
  "2025"
  "DARHT/MPTL 90-degree achromatic-bend technical object"
  "Pays the coauthor/publication surface and exact achromat title. It does not by itself identify every drawing/revision or prove participation in all MPTL hardware and review stages."

pressBrandesCamposSchulzeJaworskiCoauthorPaid : Bool
pressBrandesCamposSchulzeJaworskiCoauthorPaid = true

formalAchromatPublicationPaid : Bool
formalAchromatPublicationPaid = true

pressSchulzeBrandesObjectWeldStrengthened : Bool
pressSchulzeBrandesObjectWeldStrengthened = true

jaworskiAchromatObjectPaid : Bool
jaworskiAchromatObjectPaid = true

------------------------------------------------------------------------
-- Non-U.S. bibliographic mirror.
------------------------------------------------------------------------

record BibliographicMirrorReceipt : Set where
  constructor bibliographic-mirror-receipt
  field
    sourceOwner : String
    sourceKind : String
    nativeLocator : String
    mirroredTitle : String
    mirroredAuthors : String
    mirrorRole : String

open BibliographicMirrorReceipt public

jGlobalBibliographicMirror : BibliographicMirrorReceipt
jGlobalBibliographicMirror = bibliographic-mirror-receipt
  "Japan Science and Technology Agency J-GLOBAL"
  "non-U.S. bibliographic/indexing mirror"
  "https://jglobal.jst.go.jp/en/detail?JGLOBAL_ID=202602275966019137"
  "90-Degree Achromatic Bend for Transport of an Intense Electron Beam with Nominal Energy Spread of 16-17 MeV"
  "Press A. F.; Brandes A. M.; Campos J. M.; Schulze M.; Jaworski M. A."
  "independent bibliographic indexing of the publication metadata; not an independent experimental observation"

jGlobalBibliographicMirrorPaid : Bool
jGlobalBibliographicMirrorPaid = true

bibliographicMirrorDoesNotCreateIndependentTechnicalObservation : Bool
bibliographicMirrorDoesNotCreateIndependentTechnicalObservation = true

nonUSIndexDoesNotCreateInternationalProgrammeInference : Bool
nonUSIndexDoesNotCreateInternationalProgrammeInference = true

------------------------------------------------------------------------
-- Retained-scientist boundary.
------------------------------------------------------------------------

chavezStillOnlyRetainedScientistOnMPTLObjectFamily : Bool
chavezStillOnlyRetainedScientistOnMPTLObjectFamily = true

formalPublicationDoesNotPaySecondRetainedPerson : Bool
formalPublicationDoesNotPaySecondRetainedPerson = true

round62H2PaidCount : Nat
round62H2PaidCount = 0

round62H3PaidCount : Nat
round62H3PaidCount = 0

round62Next : String
round62Next = "Acquire the full IEEE paper/abstract or public derivative technical record and trace its explicit references to LA-UR-22-21508, LA-UR-24-30822, the P2-29 MPTL presentation and Chavez's LA-UR-24-27763 BPM report. Highest-value discriminator remains an identity-bearing MPTL drawing/review/component carrier naming a second retained scientist."

round62Reading : String
round62Reading = "The MPTL acquisition line now has a formal 2025 achromat publication coauthored by Press, Brandes, Campos, Schulze and Jaworski, strengthening the exact same-object engineering lineage beyond compatible descriptions and conference scheduling. A Japanese JST/J-GLOBAL bibliographic record independently mirrors the publication metadata, but this is source-index corroboration rather than a new technical observation. Anthony/Mark Anthony Chavez remains the only retained scientist currently paid on the MPTL object family, so H2/H3 remain zero."
