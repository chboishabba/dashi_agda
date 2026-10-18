module DASHI.Moonshine.MonsterOgg279ProvenanceHubExact where

------------------------------------------------------------------------
-- 279 PROVENANCE / FACTORISATION HUB
--
-- This owner makes explicit a scalar seam that was previously distributed
-- across the J369 / Monster / Ogg / SSP15 programme:
--
--   279 = 9 * 31 = 3^2 * 31 = 243 + 27 + 9 = (101100)_3.
--
-- The point is NOT that every occurrence of the printed integer 279 has the
-- same meaning.  The repository already contains an independent Principia
-- Volume-I OCR statistic whose cardinal-keyword count is also 279.
--
-- This module therefore separates:
--   * exact arithmetic identity;
--   * the existing Monster/Ogg prime lane p31;
--   * existing nonary / SSP15 projections of p31;
--   * the independent Principia corpus-count role.
--
-- Equal scalar values do not identify those roles or their source semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Biology.SSP15NineObserverAtlasExact as Nine
import DASHI.Foundations.PrincipiaVol1DashiBridge as PM
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Signed
import DASHI.Moonshine.OggSSP15CanonicalRankThreeByFiveExact as Rank
import DASHI.Moonshine.SSP15AffineC3TranslationExact as Affine
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

------------------------------------------------------------------------
-- 1. The literal scalar and its exact arithmetic decompositions.
------------------------------------------------------------------------

single279 : Nat
single279 = 279

nonaryScale : Nat
nonaryScale = 9

monsterLane31Value : Nat
monsterLane31Value = Lane.monsterPrimeLaneToNat Lane.p31

monsterLane31Is31 : monsterLane31Value ≡ 31
monsterLane31Is31 = refl

p31OggEuclideanAddress :
  9 * 3 + 4 ≡ monsterLane31Value
p31OggEuclideanAddress = refl

nonaryOfP31OggAddressIs279 :
  9 * (9 * 3 + 4) ≡ single279
nonaryOfP31OggAddressIs279 = refl

nonaryTimesMonster31Is279 :
  nonaryScale * monsterLane31Value ≡ single279
nonaryTimesMonster31Is279 = refl

threeSquaredTimesMonster31Is279 :
  (3 * 3) * monsterLane31Value ≡ single279
threeSquaredTimesMonster31Is279 = refl

ternarySparseExpansionIs279 :
  243 + 27 + 9 ≡ single279
ternarySparseExpansionIs279 = refl

ternary101100ValueIs279 :
  1 * 243 + 0 * 81 + 1 * 27 + 1 * 9 + 0 * 3 + 0
  ≡ single279
ternary101100ValueIs279 = refl

------------------------------------------------------------------------
-- 2. Recover the 31 factor from existing Monster / SSP15 owners.
------------------------------------------------------------------------

nineObserverAt31RecoversMonsterLane :
  Nine.SSP15NineAtlasEntry.observedValue (Nine.ssp15NineAtlas Lane.p31)
  ≡ monsterLane31Value
nineObserverAt31RecoversMonsterLane =
  Nine.SSP15NineAtlasEntry.observedValueIsPrimeLane
    (Nine.ssp15NineAtlas Lane.p31)

nineObserverAt31Is31 :
  Nine.SSP15NineAtlasEntry.observedValue (Nine.ssp15NineAtlas Lane.p31)
  ≡ 31
nineObserverAt31Is31 = refl

p31NonaryStateIsD4 :
  Affine.primeNonaryState Lane.p31 ≡ Nonary.d4
p31NonaryStateIsD4 = refl

p31ComplementModeIs45 :
  Affine.primeComplementMode Lane.p31 ≡ Nonary.mode45
p31ComplementModeIs45 = refl

p31CanonicalRankIsR10 :
  Rank.primeToRank Lane.p31 ≡ Rank.r10
p31CanonicalRankIsR10 = refl

p31SignedFRACTRANPresentationIsMode36Neutral :
  Signed.primeToInternal Lane.p31
  ≡ (Nonary.mode36 , Harmonic.zeroTrit)
p31SignedFRACTRANPresentationIsMode36Neutral = refl


------------------------------------------------------------------------
-- 3. Independent Principia role of the same printed scalar.
------------------------------------------------------------------------

principiaCardinalKeywordHits : Nat
principiaCardinalKeywordHits =
  PM.PMVol1OCRFacts.cardinalKeywordHits PM.canonicalPMVol1OCRFacts

principiaCardinalKeywordHitsIs279 :
  principiaCardinalKeywordHits ≡ single279
principiaCardinalKeywordHitsIs279 = refl

------------------------------------------------------------------------
-- 4. Typed role separation: same scalar != same meaning.
------------------------------------------------------------------------

data Role279 : Set where
  monsterOggNonaryProductRole : Role279
  ternaryNumeralRole : Role279
  principiaCardinalKeywordCountRole : Role279

monsterRoleDistinctFromPrincipiaRole :
  monsterOggNonaryProductRole ≡ principiaCardinalKeywordCountRole → ⊥
monsterRoleDistinctFromPrincipiaRole ()

ternaryRoleDistinctFromPrincipiaRole :
  ternaryNumeralRole ≡ principiaCardinalKeywordCountRole → ⊥
ternaryRoleDistinctFromPrincipiaRole ()

monsterRoleDistinctFromTernaryNumeralRole :
  monsterOggNonaryProductRole ≡ ternaryNumeralRole → ⊥
monsterRoleDistinctFromTernaryNumeralRole ()

roleScalar : Role279 → Nat
roleScalar monsterOggNonaryProductRole = nonaryScale * monsterLane31Value
roleScalar ternaryNumeralRole = 243 + 27 + 9
roleScalar principiaCardinalKeywordCountRole = principiaCardinalKeywordHits

all279RolesShareScalar :
  (role : Role279) → roleScalar role ≡ single279
all279RolesShareScalar monsterOggNonaryProductRole = refl
all279RolesShareScalar ternaryNumeralRole = refl
all279RolesShareScalar principiaCardinalKeywordCountRole = refl

------------------------------------------------------------------------
-- 5. Consolidated non-promoting receipt.
------------------------------------------------------------------------

record Single279HubReceipt : Set where
  constructor single279-hub-receipt
  field
    scalar : Nat
    scalarIs279 : scalar ≡ 279

    monsterPrimeLane : Lane.MonsterPrimeLane
    monsterPrimeLaneIsP31 : monsterPrimeLane ≡ Lane.p31
    monsterPrimeValue : Nat
    monsterPrimeValueIs31 : monsterPrimeValue ≡ 31

    nonaryFactor : Nat
    nonaryFactorIs9 : nonaryFactor ≡ 9
    productIdentity : nonaryFactor * monsterPrimeValue ≡ scalar

    sparseTernaryIdentity : 243 + 27 + 9 ≡ scalar

    principiaObservedValue : Nat
    principiaObservedValueIsSameScalar : principiaObservedValue ≡ scalar

    scalarCoincidenceIdentifiesRoles : Bool
    scalarCoincidenceIdentifiesRolesIsFalse :
      scalarCoincidenceIdentifiesRoles ≡ false

    monsterRepresentationConstructedBy279Identity : Bool
    monsterRepresentationConstructedBy279IdentityIsFalse :
      monsterRepresentationConstructedBy279Identity ≡ false

    principiaMeaningDerivedFromMonsterArithmetic : Bool
    principiaMeaningDerivedFromMonsterArithmeticIsFalse :
      principiaMeaningDerivedFromMonsterArithmetic ≡ false

open Single279HubReceipt public

canonicalSingle279HubReceipt : Single279HubReceipt
canonicalSingle279HubReceipt =
  single279-hub-receipt
    single279
    refl
    Lane.p31
    refl
    monsterLane31Value
    refl
    nonaryScale
    refl
    refl
    refl
    principiaCardinalKeywordHits
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- 6. Human-readable provenance labels for downstream inventories.
------------------------------------------------------------------------

monster279ProvenanceLabel : String
monster279ProvenanceLabel =
  "279 = 9 * 31 on the existing nonary x Monster/Ogg p31 lane"

ternary279ProvenanceLabel : String
ternary279ProvenanceLabel =
  "279 = 243 + 27 + 9 = (101100)_3"

principia279ProvenanceLabel : String
principia279ProvenanceLabel =
  "Principia Volume-I OCR cardinalKeywordHits = 279; corpus statistic only"
