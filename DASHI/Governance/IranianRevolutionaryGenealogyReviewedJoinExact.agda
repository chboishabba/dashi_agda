module DASHI.Governance.IranianRevolutionaryGenealogyReviewedJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.HistoricalMechanismCompilerExact as Compiler
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IranianRevolutionaryIntellectualGenealogyExact as Genealogy

------------------------------------------------------------------------
-- REVIEWED GENEALOGY JOIN BASES
--
-- These receipts strengthen already-declared genealogy edges using bounded
-- source passages/descriptions.  They do not create person-to-person influence
-- where the source only supports field continuity.
------------------------------------------------------------------------

mirsepessiShariati : Source.AttributedSource
mirsepessiShariati = Source.mkDOISource
  "Ali Mirsepassi"
  "Islam as a modernizing ideology: Al-e Ahmad and Shari'ati"
  "Intellectual Discourse and the Politics of Modernization, chapter 4"
  "2000"
  "10.1017/CBO9780511489242.005"
  "https://www.cambridge.org/core/books/abs/intellectual-discourse-and-the-politics-of-modernization/islam-as-a-modernizing-ideology-ale-ahmad-and-shariati/7AB233BCA3B40A7E7A7EB4655C37B916"
  Source.academicChapterSource
  "chapter summary explicitly describes Shariati drawing from Marxism to construct a populist activist Islam for national liberation"
  Source.publicAttribution

kamravaKhomeiniWest : Source.AttributedSource
kamravaKhomeiniWest = Source.mkDOISource
  "Mehran Kamrava"
  "Khomeini and the West"
  "A Critical Introduction to Khomeini, chapter 6"
  "2014"
  "10.1017/CBO9780511998485.009"
  "https://www.cambridge.org/core/books/critical-introduction-to-khomeini/khomeini-and-the-west/41E5A25E505AC13DC5B78BC9676BC01E"
  Source.academicChapterSource
  "chapter summary explicitly places Khomeini's West discourse in continuity with the Iranian left's standard neocolonial framing while preserving Khomeini's distinct revolutionary discourse"
  Source.publicAttribution

saffariShariatiGeneration : Source.AttributedSource
saffariShariatiGeneration = Source.mkDOISource
  "Siavash Saffari"
  "Beyond Shariati: Modernity, Cosmopolitanism, and Islam in Iranian Political Thought"
  "Cambridge University Press"
  "2017"
  "10.1017/9781316686966"
  "https://www.cambridge.org/core/books/beyond-shariati/450299E58ECC483475FD8EA829F02B59"
  Source.academicBookSource
  "book description identifies Shariati as an inspiration to many of the revolutionary generation and describes his combination of Islamic political thought and Left-leaning ideology"
  Source.publicAttribution

record GenealogyReviewedJoin : Set where
  constructor genealogy-reviewed-join
  field
    joinRef : String
    edge : Genealogy.GenealogyEdge
    source : Source.AttributedSource
    passageLocator : String
    boundedReading : String
    reviewed : Bool
    reviewedIsTrue : reviewed ≡ true
    preservesDeclaredEdgeStrength : Bool
    preservesDeclaredEdgeStrengthIsTrue :
      preservesDeclaredEdgeStrength ≡ true
    createsPersonalInfluence : Bool
    createsPersonalInfluenceIsFalse :
      createsPersonalInfluence ≡ false
    createsExactConceptIdentity : Bool
    createsExactConceptIdentityIsFalse :
      createsExactConceptIdentity ≡ false

open GenealogyReviewedJoin public

marxianToShariatiJoin : GenealogyReviewedJoin
marxianToShariatiJoin =
  genealogy-reviewed-join
    "join:iran:marxian-field-to-shariati"
    Genealogy.marxianFieldToShariati
    mirsepessiShariati
    "Cambridge chapter summary, paragraph describing Shariati's positive theory of Islamic ideology"
    "The source explicitly supports Marxian input into Shariati's activist Islamic synthesis."
    true refl
    true refl
    false refl
    false refl

shariatiGenerationJoin : GenealogyReviewedJoin
shariatiGenerationJoin =
  genealogy-reviewed-join
    "join:iran:shariati-to-revolutionary-generation"
    Genealogy.shariatiToRevolutionaryGeneration
    saffariShariatiGeneration
    "Cambridge book description"
    "The source explicitly supports Shariati as an inspiration to many members of the revolutionary generation."
    true refl
    true refl
    false refl
    false refl

iranianLeftKhomeiniJoin : GenealogyReviewedJoin
iranianLeftKhomeiniJoin =
  genealogy-reviewed-join
    "join:iran:iranian-left-to-khomeini-west-grammar"
    Genealogy.iranianLeftToKhomeiniWestGrammar
    kamravaKhomeiniWest
    "Cambridge chapter summary, opening paragraph"
    "The source explicitly supports field-level continuity between Khomeini's West discourse and established Iranian-left neocolonial framing."
    true refl
    true refl
    false refl
    false refl

canonicalReviewedJoins : List GenealogyReviewedJoin
canonicalReviewedJoins =
  marxianToShariatiJoin
  ∷ shariatiGenerationJoin
  ∷ iranianLeftKhomeiniJoin
  ∷ []

marxianJoinCompilerReceipt : Compiler.ReviewedJoinReceipt
marxianJoinCompilerReceipt =
  Compiler.reviewed-join-receipt
    "join:iran:marxian-field-to-shariati"
    "node:marxian-left-field"
    "node:shariati-islamic-revolutionary-synthesis"
    "Mirsepassi chapter summary / Genealogy.marxianFieldToShariati"
    true refl
    false refl

khomeiniJoinCompilerReceipt : Compiler.ReviewedJoinReceipt
khomeiniJoinCompilerReceipt =
  Compiler.reviewed-join-receipt
    "join:iran:iranian-left-to-khomeini-west-grammar"
    "node:marxian-left-field"
    "node:khomeini-anti-west-revolutionary-discourse"
    "Kamrava chapter summary / Genealogy.iranianLeftToKhomeiniWestGrammar"
    true refl
    false refl

mirsepessiSnowball :
  Snowball.SourceRoleSnowballReceipt mirsepessiShariati
mirsepessiSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt mirsepessiShariati

kamravaSnowball :
  Snowball.SourceRoleSnowballReceipt kamravaKhomeiniWest
kamravaSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt kamravaKhomeiniWest

data FieldContinuityMeansPersonalTransmission : Set where
data ReviewedJoinMeansCausalMechanism : Set where
data ShariatiInfluenceOnGenerationMeansShariatiDeterminesKhomeini : Set where

fieldContinuityDoesNotCreatePersonalTransmission :
  FieldContinuityMeansPersonalTransmission → ⊥
fieldContinuityDoesNotCreatePersonalTransmission ()

reviewedJoinDoesNotCreateCausalMechanism :
  ReviewedJoinMeansCausalMechanism → ⊥
reviewedJoinDoesNotCreateCausalMechanism ()

generationInfluenceDoesNotCreateShariatiKhomeiniDetermination :
  ShariatiInfluenceOnGenerationMeansShariatiDeterminesKhomeini → ⊥
generationInfluenceDoesNotCreateShariatiKhomeiniDetermination ()
