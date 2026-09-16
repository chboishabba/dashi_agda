module DASHI.Wikimedia.IbrahimMonster42CulturalQIDProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CULTURAL / QID 42 PROVENANCE
--
-- Source-bounded cultural coordinate only:
--   Q3107329 = the 1979 Douglas Adams novel,
--   Q836821  = the distinct 2005 film.
--
-- The short retained quotation records the role of 42 in the novel.  Neither
-- Wikidata identity nor literary co-occurrence imports mathematical authority
-- into the Monster / OEIS / Base369 proof surfaces.
------------------------------------------------------------------------

record Cultural42Receipt : Set where
  constructor cultural-42-receipt
  field
    qid : String
    title : String
    workKind : String
    sourceURL : String
    retainedQuote : String
open Cultural42Receipt public

novel42Receipt : Cultural42Receipt
novel42Receipt = cultural-42-receipt
  "Q3107329"
  "The Hitchhiker's Guide to the Galaxy"
  "1979 novel by Douglas Adams"
  "https://www.wikidata.org/wiki/Q3107329"
  "Forty-two, said Deep Thought, with infinite majesty and calm."

filmIdentityReceipt : Cultural42Receipt
filmIdentityReceipt = cultural-42-receipt
  "Q836821"
  "The Hitchhiker's Guide to the Galaxy"
  "2005 film directed by Garth Jennings"
  "https://www.wikidata.org/wiki/Q836821"
  ""

------------------------------------------------------------------------
-- WrongType firewall.
------------------------------------------------------------------------

data Cultural42CreatesMonsterMathematics : Set where

cultural42DoesNotCreateMonsterMathematics :
  Cultural42CreatesMonsterMathematics → ⊥
cultural42DoesNotCreateMonsterMathematics ()

record Cultural42Boundary : Set where
  constructor cultural-42-boundary
  field
    novelQIDIsQ3107329 : Bool
    filmQIDIsDistinctQ836821 : Bool
    shortQuoteRetained : Bool
    culturalNumericalCooccurrence : Bool
    monsterMathematicalAuthority : Bool
    sameObjectWithMonster42Class : Bool
    nextUse : String
open Cultural42Boundary public

currentCultural42Boundary : Cultural42Boundary
currentCultural42Boundary = cultural-42-boundary
  true true true true false false
  "Retain 42 <-> Q3107329 as a cultural/QID discovery coordinate only. Keep Q836821 as a distinct film identity. Do not place the cultural coordinate on any Monster, OEIS, representation, class-fusion, or action proof arrow."
