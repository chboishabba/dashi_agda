module DASHI.Governance.IRGCOpenLetter2026PrimarySpanReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

tasnimFullTextPrimary : Source.AttributedSource
tasnimFullTextPrimary = Source.mkNoDOISource
  "Islamic Revolutionary Guard Corps (IRGC), carried by Tasnim News Agency"
  "IRGC Urges American People to Distance Themselves from Israel's Occupation"
  "Tasnim full-text English HTML carrier"
  "2026-09-29"
  "https://www.tasnimnews.ir/en/news/2026/09/29/3709444/irgc-urges-american-people-to-distance-themselves-from-israel-s-occupation/amp"
  (Source.namedSourceKind "primary full-text political communication carrier")
  "Primary carrier for source-local wording and section order; not independent verification of embedded empirical, causal, theological, or geopolitical claims and not asserted byte-identical to the linked PDF"
  Source.publicAttribution

record PrimarySpanReceipt : Set where
  constructor primary-span-receipt
  field
    receiptRef : String
    propositionRef : String
    source : Source.AttributedSource
    sectionLocator : String
    paragraphLocator : String
    boundedReading : String
    sourceLocalStructurePaid : Bool
    sourceLocalStructurePaidIsTrue :
      sourceLocalStructurePaid ≡ true
    embeddedClaimTruthPaid : Bool
    embeddedClaimTruthPaidIsFalse :
      embeddedClaimTruthPaid ≡ false
    pdfByteIdentityPaid : Bool
    pdfByteIdentityPaidIsFalse :
      pdfByteIdentityPaid ≡ false

open PrimarySpanReceipt public

peopleStateReceipt : PrimarySpanReceipt
peopleStateReceipt =
  primary-span-receipt
    "span:irgc:people-state"
    "irgc:argument:people-state-distinction"
    tasnimFullTextPrimary
    "The Common Pain That Iranians and Americans Share / Are Iranians Hostile to the American people?"
    "paragraphs beginning with the two nations as victims and ending before The Meaning of Death to America"
    "The source explicitly distinguishes the American public from White House occupants and claims those rulers do not truly represent the public."
    true refl false refl false refl

commonOppressorReceipt : PrimarySpanReceipt
commonOppressorReceipt =
  primary-span-receipt
    "span:irgc:common-oppressor"
    "irgc:argument:common-oppressor"
    tasnimFullTextPrimary
    "The Common Pain That Iranians and Americans Share"
    "closing paragraph immediately before The Meaning of Death to America"
    "The source frames Iranians and Americans as harmed by the same elite actors and says they share the same pain."
    true refl false refl false refl

deathToAmericaPeopleStateReceipt : PrimarySpanReceipt
deathToAmericaPeopleStateReceipt =
  primary-span-receipt
    "span:irgc:death-to-america-target"
    "irgc:argument:elite-target-not-public"
    tasnimFullTextPrimary
    "The Meaning of Death to America"
    "opening paragraphs of the section"
    "The source says the slogan is directed at a ruling elite rather than the American people."
    true refl false refl false refl

agencyReceipt : PrimarySpanReceipt
agencyReceipt =
  primary-span-receipt
    "span:irgc:popular-agency"
    "irgc:argument:popular-agency"
    tasnimFullTextPrimary
    "How Can the U.S. Be Saved? and final appeal"
    "Quran 13:11 application through the final voter/government appeal"
    "The source attributes political agency to Americans, connecting change of course, voting, accountability, and leadership selection."
    true refl false refl false refl

coexistenceReceipt : PrimarySpanReceipt
coexistenceReceipt =
  primary-span-receipt
    "span:irgc:conditional-coexistence"
    "irgc:argument:conditional-coexistence"
    tasnimFullTextPrimary
    "final appeal"
    "paragraph beginning with peaceful coexistence"
    "The source offers peaceful coexistence while simultaneously urging removal of current political leaders."
    true refl false refl false refl

canonicalPrimarySpanReceipts : List PrimarySpanReceipt
canonicalPrimarySpanReceipts =
  peopleStateReceipt
  ∷ commonOppressorReceipt
  ∷ deathToAmericaPeopleStateReceipt
  ∷ agencyReceipt
  ∷ coexistenceReceipt
  ∷ []

tasnimPrimarySnowball :
  Snowball.SourceRoleSnowballReceipt tasnimFullTextPrimary
tasnimPrimarySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt tasnimFullTextPrimary

data HTMLCarrierEqualsPDFBytes : Set where
data ExactSpanPaysEmbeddedTruth : Set where
data PrimaryCarrierPaysCausalMechanism : Set where
data SourceLocalArgumentMeansAudienceEffect : Set where

htmlCarrierDoesNotEqualPDFBytes :
  HTMLCarrierEqualsPDFBytes → ⊥
htmlCarrierDoesNotEqualPDFBytes ()

spanDoesNotPayEmbeddedTruth :
  ExactSpanPaysEmbeddedTruth → ⊥
spanDoesNotPayEmbeddedTruth ()

primaryCarrierDoesNotPayCausalMechanism :
  PrimaryCarrierPaysCausalMechanism → ⊥
primaryCarrierDoesNotPayCausalMechanism ()

sourceArgumentDoesNotPayAudienceEffect :
  SourceLocalArgumentMeansAudienceEffect → ⊥
sourceArgumentDoesNotPayAudienceEffect ()
