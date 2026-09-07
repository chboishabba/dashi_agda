module DASHI.Law.UNZionismTerrorismAttributionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- UN attribution discipline for Zionism/terrorism claims.
-- UN-hosted documents may contain statements by Member States, the PLO,
-- seminar participants or other speakers.  Those do not automatically become
-- institutional findings/resolutions of the United Nations.
------------------------------------------------------------------------

data UNSourceRole : Set where
  generalAssemblyResolution : UNSourceRole
  memberStateLetter : UNSourceRole
  memberStateSpeech : UNSourceRole
  ploStatement : UNSourceRole
  unHistoricalCompilation : UNSourceRole
  unSeminarContribution : UNSourceRole
  dashiAttributionConclusion : UNSourceRole

data UNTerrorismProposition : Set where
  unga3379ZionismRacism : UNTerrorismProposition
  irgunSternDescribedAsZionistTerroristGroups : UNTerrorismProposition
  zionismAchievedStatehoodThroughTerrorismClaim : UNTerrorismProposition
  israelPractisesStateTerrorismClaim : UNTerrorismProposition
  unFormallyDesignatedZionismTerroristIdeology : UNTerrorismProposition
  unFormallyDesignatedZionismTerroristSympathyGroup : UNTerrorismProposition

record UNAttributionReceipt : Set where
  constructor unAttributionReceipt
  field
    proposition : UNTerrorismProposition
    role : UNSourceRole
    sourceReference : String
    boundedDescription : String

open UNAttributionReceipt public

unga3379Receipt : UNAttributionReceipt
unga3379Receipt = unAttributionReceipt
  unga3379ZionismRacism generalAssemblyResolution
  "A/RES/3379 (XXX), 10 November 1975; revoked by A/RES/46/86 on 16 December 1991"
  "The General Assembly determined that Zionism was a form of racism and racial discrimination; that determination was later revoked."

irgunSternUNRecordReceipt : UNAttributionReceipt
irgunSternUNRecordReceipt = unAttributionReceipt
  irgunSternDescribedAsZionistTerroristGroups unHistoricalCompilation
  "UN Palestine debate/historical records describing Irgun and Stern as Zionist terrorist organizations"
  "UN records preserve descriptions of Irgun and Stern as Zionist terrorist organisations. The source relation varies by document and must not be flattened into a whole-ideology designation."

egypt1972Receipt : UNAttributionReceipt
egypt1972Receipt = unAttributionReceipt
  zionismAchievedStatehoodThroughTerrorismClaim memberStateLetter
  "A/8875-S/10827, Letter from the Permanent Representative of Egypt, 8 November 1972"
  "Egypt's representative argued that Zionism achieved the establishment of Israel through terrorism and cited Stern, Irgun and Haganah. This is a Member State claim transmitted in a UN document, not a UN institutional finding."

unSeminarStateTerrorismReceipt : UNAttributionReceipt
unSeminarStateTerrorismReceipt = unAttributionReceipt
  israelPractisesStateTerrorismClaim unSeminarContribution
  "Fourth United Nations Seminar on the Question of Palestine, Havana, 31 August-4 September 1981"
  "A seminar contribution characterised Zionist/Israeli practice as terrorism/state terrorism. Publication by the UN does not convert the contributor's statement into a General Assembly determination."

------------------------------------------------------------------------
-- Highest-alpha correction: no formal 'terrorist sympathy group' designation
-- has been recovered from authoritative UN institutional sources in this audit.
------------------------------------------------------------------------

record UNDesignationBoundary : Set where
  constructor unDesignationBoundary
  field
    memberStateStatementEqualsUNFinding : Bool
    memberStateStatementEqualsUNFindingIsFalse : memberStateStatementEqualsUNFinding ≡ false
    seminarContributionEqualsUNFinding : Bool
    seminarContributionEqualsUNFindingIsFalse : seminarContributionEqualsUNFinding ≡ false
    irgunSternTerrorismEqualsWholeZionismDesignation : Bool
    irgunSternTerrorismEqualsWholeZionismDesignationIsFalse : irgunSternTerrorismEqualsWholeZionismDesignation ≡ false
    formalUNTerroristIdeologyDesignationRecovered : Bool
    formalUNTerroristIdeologyDesignationRecoveredIsFalse : formalUNTerroristIdeologyDesignationRecovered ≡ false
    formalUNTerroristSympathyGroupDesignationRecovered : Bool
    formalUNTerroristSympathyGroupDesignationRecoveredIsFalse : formalUNTerroristSympathyGroupDesignationRecovered ≡ false

canonicalUNDesignationBoundary : UNDesignationBoundary
canonicalUNDesignationBoundary =
  unDesignationBoundary false refl false refl false refl false refl false refl
