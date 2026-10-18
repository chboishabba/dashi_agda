module DASHI.Moonshine.TwoSevenNineNumberRoleHubExact where

------------------------------------------------------------------------
-- 279 NUMBER-ROLE HUB
--
-- This file joins two already-owned roles of the same printed integer 279:
--
--   arithmetic / Moonshine observer role
--     279 = 9 * 31 = 9 * (1 + 3 * 10)
--
--   Principia OCR corpus role
--     cardinalKeywordHits = 279
--
-- The equality of printed scalars is exact.  Their meanings are deliberately
-- not identified.  This is the NumberRoleProvenanceAtlas discipline applied
-- to the newly explicit 279 hub.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggP31CompletionTenTwoSevenNineCrossPollinationExact as P279
import DASHI.Foundations.PrincipiaVol1DashiBridge as Principia

------------------------------------------------------------------------
-- 1. Shared scalar.
------------------------------------------------------------------------

twoSevenNine : Nat
twoSevenNine = 279

moonshineObserver279 : Nat
moonshineObserver279 = P279.nonaryPointedP31

moonshineObserver279Is279 :
  moonshineObserver279 ≡ twoSevenNine
moonshineObserver279Is279 = P279.nonaryPointedP31Is279

principiaCardinalKeyword279 : Nat
principiaCardinalKeyword279 =
  Principia.PMVol1OCRFacts.cardinalKeywordHits
    Principia.canonicalPMVol1OCRFacts

principiaCardinalKeyword279Is279 :
  principiaCardinalKeyword279 ≡ twoSevenNine
principiaCardinalKeyword279Is279 = refl

sharedPrintedScalar :
  moonshineObserver279 ≡ principiaCardinalKeyword279
sharedPrintedScalar = refl

------------------------------------------------------------------------
-- 2. Distinct typed roles.
------------------------------------------------------------------------

data TwoSevenNineRole : Set where
  nonaryPointedP31ObserverRole : TwoSevenNineRole
  principiaCardinalKeywordCorpusRole : TwoSevenNineRole

rolesAreDistinct :
  nonaryPointedP31ObserverRole ≡ principiaCardinalKeywordCorpusRole → ⊥
rolesAreDistinct ()

record TwoSevenNineProvenanceEntry : Set where
  constructor two-seven-nine-provenance-entry
  field
    printedValue : String
    role : TwoSevenNineRole
    sourceOrOwner : String
    meaning : String
    exactRealisation : String

moonshine279Entry : TwoSevenNineProvenanceEntry
moonshine279Entry =
  two-seven-nine-provenance-entry
    "279"
    nonaryPointedP31ObserverRole
    "DASHI Moonshine / SSP15 / nonary composite"
    "nonary scale applied to the pointed p31 observer"
    "9 * (1 + 3 * Completion10) = 9 * 31 = 279"

principia279Entry : TwoSevenNineProvenanceEntry
principia279Entry =
  two-seven-nine-provenance-entry
    "279"
    principiaCardinalKeywordCorpusRole
    "PrincipiaVol1DashiBridge OCR inventory"
    "number of OCR keyword hits classified under cardinal vocabulary"
    "canonicalPMVol1OCRFacts.cardinalKeywordHits = 279"

------------------------------------------------------------------------
-- 3. Semantic firewall.
------------------------------------------------------------------------

data Same279ScalarCreatesSameRole : Set where
data Principia279CreatesMonsterObserver : Set where
data MonsterObserver279ExplainsPrincipiaCount : Set where

sameScalarDoesNotIdentifyRoles :
  Same279ScalarCreatesSameRole → ⊥
sameScalarDoesNotIdentifyRoles ()

principiaCountDoesNotCreateMonsterObserver :
  Principia279CreatesMonsterObserver → ⊥
principiaCountDoesNotCreateMonsterObserver ()

monsterObserverDoesNotExplainPrincipiaCount :
  MonsterObserver279ExplainsPrincipiaCount → ⊥
monsterObserverDoesNotExplainPrincipiaCount ()

record TwoSevenNineRoleBoundary : Set where
  constructor two-seven-nine-role-boundary
  field
    moonshineComposite279Paid : Bool
    principiaCorpus279Paid : Bool
    sharedPrintedScalarPaid : Bool
    rolesKeptDistinct : Bool
    sameScalarPromotedToSharedMeaning : Bool

canonicalTwoSevenNineRoleBoundary : TwoSevenNineRoleBoundary
canonicalTwoSevenNineRoleBoundary =
  two-seven-nine-role-boundary true true true true false
