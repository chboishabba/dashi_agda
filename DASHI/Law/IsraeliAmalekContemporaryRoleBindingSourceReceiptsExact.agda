module DASHI.Law.IsraeliAmalekContemporaryRoleBindingSourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek

------------------------------------------------------------------------
-- Contemporary Israeli Amalek role-binding source receipts.
--
-- This owner corrects the too-strong absence claim in earlier discussion.
-- Modern Amalek role-binding is source-backed in Israeli executive,
-- parliamentary, and military-context rhetoric.  What remains separately
-- evidentiary is literal ethnic identity, collective propagation scope, and
-- transport of the scriptural exterminatory command into operational policy.
------------------------------------------------------------------------

data ContemporaryAmalekSourceRole : Set where
  primeMinisterWarSpeech
  primeMinisterLetterToSoldiers
  knessetOfficialRecord
  icjPartySubmission
  icjJudicialObservation
  secondaryReport : ContemporaryAmalekSourceRole

data ContemporaryAmalekProposition : Set where
  netanyahuInvokedAmalekInGazaWarContext
  netanyahuRepeatedAmalekToSoldiers
  knessetInstitutionallyRepeatedAmalekVerse
  parliamentaryLightDarkEnemyFraming
  inflammatoryRhetoricEchoedByArmedForces
  palestiniansLiterallyIdenticalToScripturalAmalek
  exterminatoryCommandOperationallyImported : ContemporaryAmalekProposition

record ContemporaryAmalekReceipt : Set where
  constructor contemporaryAmalekReceipt
  field
    proposition : ContemporaryAmalekProposition
    sourceRole : ContemporaryAmalekSourceRole
    sourceReference : String
    boundedDescription : String

open ContemporaryAmalekReceipt public

netanyahu28OctoberReceipt : ContemporaryAmalekReceipt
netanyahu28OctoberReceipt = contemporaryAmalekReceipt
  netanyahuInvokedAmalekInGazaWarContext
  primeMinisterWarSpeech
  "Benjamin Netanyahu statement, 28 October 2023; quoted in Israel's ICJ submission and South Africa's oral pleading"
  "Netanyahu invoked 'Remember what Amalek did to you' while addressing the Gaza war and soldiers. This closes contemporary role-binding rhetoric, not literal ethnic identity or command transport."

netanyahu3NovemberReceipt : ContemporaryAmalekReceipt
netanyahu3NovemberReceipt = contemporaryAmalekReceipt
  netanyahuRepeatedAmalekToSoldiers
  primeMinisterLetterToSoldiers
  "Prime Minister public missive to IDF soldiers and commanders, 3 November 2023"
  "Netanyahu again invoked the Amalek verse directly to serving soldiers in a wartime message."

knessetMemorialReceipt : ContemporaryAmalekReceipt
knessetMemorialReceipt = contemporaryAmalekReceipt
  knessetInstitutionallyRepeatedAmalekVerse
  knessetOfficialRecord
  "Knesset official record, 26 February 2025, memorial for Bibas family and others"
  "The Knesset Speaker repeated the Amalek remembrance verse in an official parliamentary setting."

knessetLightDarkReceipt : ContemporaryAmalekReceipt
knessetLightDarkReceipt = contemporaryAmalekReceipt
  parliamentaryLightDarkEnemyFraming
  knessetOfficialRecord
  "Knesset official record, 6 November 2023"
  "Knesset Speaker Amir Ohana described the conflict as a struggle of the sons of light against the sons of darkness. This is a separate enemy-framing receipt, not itself an Amalek quote."

nolteEchoReceipt : ContemporaryAmalekReceipt
nolteEchoReceipt = contemporaryAmalekReceipt
  inflammatoryRhetoricEchoedByArmedForces
  icjJudicialObservation
  "ICJ, Declaration of Judge Nolte, Order of 26 January 2024, South Africa v Israel"
  "Judge Nolte stated that South Africa had provided evidence, not contradicted by Israel, that inflammatory parts of relevant statements had been echoed in a threatening way by members of the Israeli armed forces."

------------------------------------------------------------------------
-- Reuse the generic Amalek provenance firewall.  The empirical correction is
-- that a modern role-binding receipt EXISTS.  The non-promotions remain.
------------------------------------------------------------------------

amalekCoreBoundary : Amalek.AmalekBoundary
amalekCoreBoundary = Amalek.canonicalAmalekBoundary

record ContemporaryAmalekBoundary : Set where
  constructor contemporaryAmalekBoundary
  field
    modernRoleBindingAbsent : Bool
    modernRoleBindingAbsentIsFalse : modernRoleBindingAbsent ≡ false
    modernRoleBindingEqualsLiteralEthnicIdentity : Bool
    modernRoleBindingEqualsLiteralEthnicIdentityIsFalse : modernRoleBindingEqualsLiteralEthnicIdentity ≡ false
    amalekInvocationAutomaticallyImportsExterminatoryCommand : Bool
    amalekInvocationAutomaticallyImportsExterminatoryCommandIsFalse : amalekInvocationAutomaticallyImportsExterminatoryCommand ≡ false
    wartimeMessageToSoldiersIsOperationallyRelevantContext : Bool
    wartimeMessageToSoldiersIsOperationallyRelevantContextIsTrue : wartimeMessageToSoldiersIsOperationallyRelevantContext ≡ true

canonicalContemporaryAmalekBoundary : ContemporaryAmalekBoundary
canonicalContemporaryAmalekBoundary =
  contemporaryAmalekBoundary false refl false refl false refl true refl

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data ContemporaryAmalekClaim : Set where
  contemporaryStateAmalekRoleBindingExists
  roleBindingReachedMilitaryAudience
  rhetoricWasEchoedInMilitaryContext
  palestiniansAreLiterallyScripturalAmalek
  scripturalErasureCommandBecameOperationalOrder : ContemporaryAmalekClaim

data ContemporaryAmalekProducer : Set where
  executiveSpeechProducer
  soldierMessageProducer
  judicialEchoReceiptProducer
  literalIdentityProducer
  commandTransportProducer : ContemporaryAmalekProducer

reverseContemporaryAmalek : ContemporaryAmalekClaim → ContemporaryAmalekProducer
reverseContemporaryAmalek contemporaryStateAmalekRoleBindingExists = executiveSpeechProducer
reverseContemporaryAmalek roleBindingReachedMilitaryAudience = soldierMessageProducer
reverseContemporaryAmalek rhetoricWasEchoedInMilitaryContext = judicialEchoReceiptProducer
reverseContemporaryAmalek palestiniansAreLiterallyScripturalAmalek = literalIdentityProducer
reverseContemporaryAmalek scripturalErasureCommandBecameOperationalOrder = commandTransportProducer
