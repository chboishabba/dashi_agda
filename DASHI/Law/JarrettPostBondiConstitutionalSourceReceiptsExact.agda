module DASHI.Law.JarrettPostBondiConstitutionalSourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source attribution discipline for Jarrett v State of NSW [2026] NSWCA 62.
-- Court holdings, party submissions, government descriptions, media labels,
-- and DASHI formal bridges remain different proposition relations.
------------------------------------------------------------------------

data LegalSourceRole : Set where
  courtHolding
  plaintiffSubmission
  defendantSubmission
  governmentMediaRelease
  secondaryReport
  dashiFormalBridge : LegalSourceRole

data PropositionKind : Set where
  provisionsDeclaredInvalid
  impliedFreedomImpermissibleBurden
  purposeConstitutionallyIllegitimate
  stateReasonablyAppropriateAdaptedArgument
  plaintiffsInvalidityArgument
  postBondiEnactmentHistory
  shorthandUnconstitutionalLabel
  operationalAuthorityConsequence : PropositionKind

record LegalSourceReceipt : Set where
  constructor legalSourceReceipt
  field
    proposition : PropositionKind
    role : LegalSourceRole
    sourceReference : String
    boundedDescription : String

open LegalSourceReceipt public

jarrettInvalidityHolding : LegalSourceReceipt
jarrettInvalidityHolding = legalSourceReceipt
  provisionsDeclaredInvalid
  courtHolding
  "Jarrett v State of New South Wales [2026] NSWCA 62; NSW Court of Appeal, 16 April 2026"
  "Court declared the impugned PARD scheme provisions invalid"

jarrettBurdenHolding : LegalSourceReceipt
jarrettBurdenHolding = legalSourceReceipt
  impliedFreedomImpermissibleBurden
  courtHolding
  "Jarrett v State of New South Wales [2026] NSWCA 62"
  "Court held the scheme impermissibly burdened the implied freedom of political communication"

jarrettPurposeHolding : LegalSourceReceipt
jarrettPurposeHolding = legalSourceReceipt
  purposeConstitutionallyIllegitimate
  courtHolding
  "Jarrett v State of New South Wales [2026] NSWCA 62, including [136], [157] as summarised by NSW Court of Appeal Decisions of Interest"
  "Discouraging all public assemblies in a declared area irrespective of their purpose was not a constitutionally legitimate purpose"

stateJustificationSubmission : LegalSourceReceipt
stateJustificationSubmission = legalSourceReceipt
  stateReasonablyAppropriateAdaptedArgument
  defendantSubmission
  "State of NSW submissions filed 19 February 2026 in Jarrett"
  "State argued the burden was tightly confined and reasonably justified by safety/social-cohesion concerns"

plaintiffsInvaliditySubmission : LegalSourceReceipt
plaintiffsInvaliditySubmission = legalSourceReceipt
  plaintiffsInvalidityArgument
  plaintiffSubmission
  "Plaintiffs' submissions filed 26 January 2026 in Jarrett"
  "Plaintiffs argued the PARD scheme impermissibly burdened political communication and was invalid"

postBondiHistoryReceipt : LegalSourceReceipt
postBondiHistoryReceipt = legalSourceReceipt
  postBondiEnactmentHistory
  courtHolding
  "Jarrett v State of NSW [2026] NSWCA 62 / NSW Court of Appeal summary"
  "PARD scheme was introduced by the Terrorism and Other Legislation Amendment Act 2025 following the Bondi Beach terrorist attack of 14 December 2025"

mediaUnconstitutionalShorthand : LegalSourceReceipt
mediaUnconstitutionalShorthand = legalSourceReceipt
  shorthandUnconstitutionalLabel
  secondaryReport
  "ABC News, 16 April 2026"
  "Secondary shorthand described the struck-down post-Bondi protest laws as unconstitutional"

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

record SourceAttributionBoundary : Set where
  constructor sourceAttributionBoundary
  field
    plaintiffSubmissionCountsAsCourtHolding : Bool
    plaintiffSubmissionCountsAsCourtHoldingIsFalse : plaintiffSubmissionCountsAsCourtHolding ≡ false
    governmentDescriptionCountsAsCourtHolding : Bool
    governmentDescriptionCountsAsCourtHoldingIsFalse : governmentDescriptionCountsAsCourtHolding ≡ false
    mediaShorthandReplacesExactHolding : Bool
    mediaShorthandReplacesExactHoldingIsFalse : mediaShorthandReplacesExactHolding ≡ false
    formalBridgeCountsAsHistoricalAuthorship : Bool
    formalBridgeCountsAsHistoricalAuthorshipIsFalse : formalBridgeCountsAsHistoricalAuthorship ≡ false

canonicalSourceAttributionBoundary : SourceAttributionBoundary
canonicalSourceAttributionBoundary =
  sourceAttributionBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- Legal consequence is separately typed: invalidity of the PARD provisions
-- does not by itself decide every individual officer act, charge or remedy.
------------------------------------------------------------------------

data IndividualConsequenceClaim : Set where
  everyHerzogPoliceActUnlawful
  everyHerzogChargeInvalid
  individualActRequiresIndependentLawfulnessAudit : IndividualConsequenceClaim

record ConstitutionalConsequenceBoundary : Set where
  constructor constitutionalConsequenceBoundary
  field
    invalidPARDMeansEveryPoliceActUnlawful : Bool
    invalidPARDMeansEveryPoliceActUnlawfulIsFalse : invalidPARDMeansEveryPoliceActUnlawful ≡ false
    invalidPARDMeansEveryChargeInvalid : Bool
    invalidPARDMeansEveryChargeInvalidIsFalse : invalidPARDMeansEveryChargeInvalid ≡ false
    individualLawfulnessStillRequiresPowerAndFacts : Bool
    individualLawfulnessStillRequiresPowerAndFactsIsTrue : individualLawfulnessStillRequiresPowerAndFacts ≡ true

canonicalConstitutionalConsequenceBoundary : ConstitutionalConsequenceBoundary
canonicalConstitutionalConsequenceBoundary =
  constitutionalConsequenceBoundary false refl false refl true refl
