module DASHI.Culture.PowersPlantationParadiseMinetteChronologyContestationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Chronology
import DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact as Minette

------------------------------------------------------------------------
-- MINETTE 1790 NOTICE: TYPED CHRONOLOGY CONTESTATION
--
-- Prest and the Laméca dossier preserve different dates for what appears to be
-- the same Périgord/Minette legal-notice wording.  We retain both as qualified
-- claim leaves under one proposition root.  The relation is unresolved until
-- the primary newspaper image/issue is inspected.
------------------------------------------------------------------------

minette1790NoticeRoot : Chronology.PropositionRoot
minette1790NoticeRoot =
  Chronology.proposition-root
    "proposition:minette:1790-perigord-legal-notice-date"
    "date of the Affiches Americaines Périgord/Minette legal notice"
    true refl
    false refl
    false refl
    false refl

prest1790TemporalAssertion : Chronology.TemporalAssertion
prest1790TemporalAssertion =
  Chronology.temporal-assertion
    "temporal:minette:prest:1790-07-01"
    (Chronology.exactDate "1 July 1790")
    ("statement:minette:prest-iphigenie:legal-notice-date" ∷ [])
    ("observation:minette:prest-iphigenie:footnote" ∷ [])
    "review:minette:chronology:primary-not-yet-inspected"
    "Prest peer-reviewed secondary citation -> claimed Affiches issue/page"
    true refl
    false refl
    false refl
    false refl

lameca1790TemporalAssertion : Chronology.TemporalAssertion
lameca1790TemporalAssertion =
  Chronology.temporal-assertion
    "temporal:minette:lameca:1790-07-17"
    (Chronology.exactDate "17 July 1790")
    ("statement:minette:lameca:legal-notice-date" ∷ [])
    ("observation:minette:lameca:digital-dossier" ∷ [])
    "review:minette:chronology:primary-not-yet-inspected"
    "Laméca institutional secondary reproduction -> claimed Affiches date"
    true refl
    false refl
    false refl
    false refl

prest1790ClaimLeaf : Chronology.ClaimLeaf minette1790NoticeRoot
prest1790ClaimLeaf =
  Chronology.claim-leaf
    "claim:minette:1790-notice-date:prest"
    Chronology.qualification
    "Julia Prest"
    ("statement:minette:prest-iphigenie:legal-notice-date" ∷ [])
    ("observation:minette:prest-iphigenie:footnote" ∷ [])
    ("temporal:minette:prest:1790-07-01" ∷ [])
    ("scope:secondary-citation-until-primary-inspection" ∷ [])
    Chronology.qualified
    "review:minette:chronology:primary-not-yet-inspected"
    "Prest Iphigenie -> Affiches Americaines 1 July 1790 p.368"
    true refl
    false refl
    false refl
    false refl

lameca1790ClaimLeaf : Chronology.ClaimLeaf minette1790NoticeRoot
lameca1790ClaimLeaf =
  Chronology.claim-leaf
    "claim:minette:1790-notice-date:lameca"
    Chronology.alternativeAccount
    "Médiathèque Caraïbe / Laméca"
    ("statement:minette:lameca:legal-notice-date" ∷ [])
    ("observation:minette:lameca:digital-dossier" ∷ [])
    ("temporal:minette:lameca:1790-07-17" ∷ [])
    ("scope:secondary-citation-until-primary-inspection" ∷ [])
    Chronology.qualified
    "review:minette:chronology:primary-not-yet-inspected"
    "Laméca digital dossier -> Affiches Americaines 17 July 1790"
    true refl
    false refl
    false refl
    false refl

minette1790NoticeContestationRelation :
  Chronology.ContestationRelation prest1790ClaimLeaf lameca1790ClaimLeaf
minette1790NoticeContestationRelation =
  Chronology.contestation-relation
    "contestation:minette:1790-notice-date:prest-v-lameca"
    Chronology.sameIncidentDifferentAccount
    ("statement:minette:prest-iphigenie:legal-notice-date"
      ∷ "statement:minette:lameca:legal-notice-date"
      ∷ [])
    ("observation:minette:prest-iphigenie:footnote"
      ∷ "observation:minette:lameca:digital-dossier"
      ∷ [])
    "review:minette:chronology:unresolved-pending-primary"
    "two secondary surfaces appear to reference the same legal notice but disagree on date"
    true refl
    false refl
    false refl
    false refl

prest1790ChronologyEntry : Chronology.ChronologyEntry
prest1790ChronologyEntry =
  Chronology.chronology-entry
    "event:minette:1790-perigord-legal-notice"
    prest1790TemporalAssertion
    ("statement:minette:prest-iphigenie:legal-notice-date" ∷ [])
    ("observation:minette:prest-iphigenie:footnote" ∷ [])
    ("proposition:minette:1790-perigord-legal-notice-date" ∷ [])
    ("claim:minette:1790-notice-date:prest" ∷ [])
    ("contestation:minette:1790-notice-date:prest-v-lameca" ∷ [])
    true refl
    false refl
    false refl

lameca1790ChronologyEntry : Chronology.ChronologyEntry
lameca1790ChronologyEntry =
  Chronology.chronology-entry
    "event:minette:1790-perigord-legal-notice"
    lameca1790TemporalAssertion
    ("statement:minette:lameca:legal-notice-date" ∷ [])
    ("observation:minette:lameca:digital-dossier" ∷ [])
    ("proposition:minette:1790-perigord-legal-notice-date" ∷ [])
    ("claim:minette:1790-notice-date:lameca" ∷ [])
    ("contestation:minette:1790-notice-date:prest-v-lameca" ∷ [])
    true refl
    false refl
    false refl

chronologyContestationBoundary : Chronology.S28ChronologyContestationBoundary
chronologyContestationBoundary = Chronology.canonicalS28ChronologyContestationBoundary

microhistoryPrimaryInspectionFirewall :
  Minette.SecondaryDateDisagreementResolvedWithoutPrimaryInspection → ⊥
microhistoryPrimaryInspectionFirewall =
  Minette.secondaryDateDisagreementNeedsPrimaryInspection

record MinetteChronologyContestationBoundary : Set where
  constructor minette-chronology-contestation-boundary
  field
    bothSecondaryDatesRetained : Bool
    bothSecondaryDatesRetainedIsTrue : bothSecondaryDatesRetained ≡ true
    disagreementTypedAsContestation : Bool
    disagreementTypedAsContestationIsTrue : disagreementTypedAsContestation ≡ true
    primaryIssueInspectionStillRequired : Bool
    primaryIssueInspectionStillRequiredIsTrue : primaryIssueInspectionStillRequired ≡ true
    contestationSelectsWinningDate : Bool
    contestationSelectsWinningDateIsFalse : contestationSelectsWinningDate ≡ false

canonicalMinetteChronologyContestationBoundary :
  MinetteChronologyContestationBoundary
canonicalMinetteChronologyContestationBoundary =
  minette-chronology-contestation-boundary
    true refl
    true refl
    true refl
    false refl
