module DASHI.Wikimedia.IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact as Suzuki
import DASHI.Wikimedia.IbrahimMonster3BSuzukiQuotientDescentCorrectionExact as Descent
import DASHI.Wikimedia.IbrahimMonster3B729ExtensionFiniteFieldProducerSnowballExact as Extension729

------------------------------------------------------------------------
-- SUZUKI -> MAIN TABLE -> N(3B) -> ACTUAL MONSTER SAME-OBJECT ROUTE
--
-- This owner describes the promotion level of the executable producer
-- scripts/monster_3b_suzuki_main_quotient_match.g.
--
-- The producer is intentionally pair-level.  It can pay that the faithful
-- character families {12a,12b} and {78a,78b}, through the Barraclough--Wilson
-- degree-1458 fused Heisenberg construction, give the actual paired-phase
-- MN3B constituents occurring in the restricted Monster 196883 character.
--
-- It CANNOT by itself decide which member a/b belongs to a chosen zeta sector;
-- the outer involution fuses those phases.  That requires an additional
-- phase-resolved / quotient-kernel orientation receipt.
------------------------------------------------------------------------

baseFusedDegree : Nat
baseFusedDegree = 1458

twelveOuterPairDegree : Nat
twelveOuterPairDegree = 24

seventyEightOuterPairDegree : Nat
seventyEightOuterPairDegree = 156

baseTimesTwelvePair : Nat
baseTimesTwelvePair = baseFusedDegree * twelveOuterPairDegree

baseTimesTwelvePairIsTwo17496 : baseTimesTwelvePair ≡ 2 * 17496
baseTimesTwelvePairIsTwo17496 = refl

baseTimesSeventyEightPair : Nat
baseTimesSeventyEightPair = baseFusedDegree * seventyEightOuterPairDegree

baseTimesSeventyEightPairIsTwo113724 :
  baseTimesSeventyEightPair ≡ 2 * 113724
baseTimesSeventyEightPairIsTwo113724 = refl

------------------------------------------------------------------------
-- 1. Attribution roles.
------------------------------------------------------------------------

paperSource : Attribution.AttributedSource
paperSource = Suzuki.barracloughWilson

paperAttribution = Snowball.canonicalSourceRoleSnowballReceipt paperSource

thesisSource : Attribution.AttributedSource
thesisSource = Extension729.barracloughThesis

thesisAttribution = Snowball.canonicalSourceRoleSnowballReceipt thesisSource

supplementSource : Attribution.AttributedSource
supplementSource = Descent.supplementarySource

supplementAttribution = Snowball.canonicalSourceRoleSnowballReceipt supplementSource

ctbllibSource : Attribution.AttributedSource
ctbllibSource = Suzuki.ctbllibSource

ctbllibAttribution = Snowball.canonicalSourceRoleSnowballReceipt ctbllibSource

paperDOI : String
paperDOI = "10.1112/S1461157000001352"

record SameObjectExternalCoordinates : Set where
  constructor same-object-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasSameObjectAuthority : Bool
open SameObjectExternalCoordinates public

canonicalSameObjectExternalCoordinates : SameObjectExternalCoordinates
canonicalSameObjectExternalCoordinates =
  same-object-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 only; no OEIS sequence identifies a 6.Suz character, main-table quotient row, or Monster occurrence"
    false

------------------------------------------------------------------------
-- 2. Receipt shape produced by the executable class-function matcher.
------------------------------------------------------------------------

record SuzukiPairFamilyIdentity : Set where
  constructor suzuki-pair-family-identity
  field
    firstAtlasLabel : String
    secondAtlasLabel : String
    singleDegree : Nat
    outerPairDegree : Nat
    sixSuzToOuterRestrictionEquality : Set

open SuzukiPairFamilyIdentity public

record MainTableProductSplit : Set where
  constructor main-table-product-split
  field
    base1458MainPosition : Nat
    outerPairPosition : Nat
    firstMainPosition : Nat
    secondMainPosition : Nat
    splitByFullCharacterDecomposition : Set

open MainTableProductSplit public

record QuotientDescentMatch : Set where
  constructor quotient-descent-match
  field
    productSplit : MainTableProductSplit
    descendingMainPosition : Nat
    mn3bPosition : Nat
    fullPullbackCharacterEquality : Set
    pairedPhaseCentralTrace : Set

open QuotientDescentMatch public

record RestrictedMonsterOccurrence : Set where
  constructor restricted-monster-occurrence
  field
    descent : QuotientDescentMatch
    monsterRestrictionMultiplicity : Nat
    multiplicityPositive : Set
    sameMN3BIrreducibleObject : Set

open RestrictedMonsterOccurrence public

record SuzukiMainQuotientSameObjectReceipt : Set₁ where
  constructor suzuki-main-quotient-same-object-receipt
  field
    base1458MatchesBarracloughFusedExtension : Set

    twelveFamily : SuzukiPairFamilyIdentity
    seventyEightFamily : SuzukiPairFamilyIdentity

    twelveFamilyDegreeExact : singleDegree twelveFamily ≡ 12
    twelveOuterPairDegreeExact : outerPairDegree twelveFamily ≡ 24
    seventyEightFamilyDegreeExact : singleDegree seventyEightFamily ≡ 78
    seventyEightOuterPairDegreeExact : outerPairDegree seventyEightFamily ≡ 156

    twelveMonsterOccurrence : RestrictedMonsterOccurrence
    seventyEightMonsterOccurrence : RestrictedMonsterOccurrence

    primaryMainToMN3BQuotientMapSameObject : Set
    actualMonster196883RestrictionSameObject : Set
    pairFamilyMonsterOccurrencePaid : Set

open SuzukiMainQuotientSameObjectReceipt public

------------------------------------------------------------------------
-- 3. Individual phase orientation stays separate.
------------------------------------------------------------------------

record IndividualZetaOrientationReceipt
  (sameObject : SuzukiMainQuotientSameObjectReceipt) : Set₁ where
  field
    selectedExtraspecialZetaCharacter : Set
    selectedTwelveAtlasLabel : String
    selectedSeventyEightAtlasLabel : String
    quotientKernelCompatibilityTwelve : Set
    quotientKernelCompatibilitySeventyEight : Set
    phaseResolvedFullCharacterMatch : Set

open IndividualZetaOrientationReceipt public

------------------------------------------------------------------------
-- 4. WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data PairFamilyOccurrenceCreatesIndividualOrientation : Set where
data Degree17496CreatesMN3BCharacterIdentity : Set where
data Degree113724CreatesMN3BCharacterIdentity : Set where
data MainTableProductCreatesQuotientDescent : Set where
data QuotientDescentCreatesMonsterOccurrence : Set where

pairFamilyDoesNotCreateIndividualOrientation :
  PairFamilyOccurrenceCreatesIndividualOrientation → ⊥
pairFamilyDoesNotCreateIndividualOrientation ()

degree17496DoesNotCreateIdentity : Degree17496CreatesMN3BCharacterIdentity → ⊥
degree17496DoesNotCreateIdentity ()

degree113724DoesNotCreateIdentity : Degree113724CreatesMN3BCharacterIdentity → ⊥
degree113724DoesNotCreateIdentity ()

mainProductDoesNotCreateDescent : MainTableProductCreatesQuotientDescent → ⊥
mainProductDoesNotCreateDescent ()

quotientDescentDoesNotCreateMonsterOccurrence :
  QuotientDescentCreatesMonsterOccurrence → ⊥
quotientDescentDoesNotCreateMonsterOccurrence ()

------------------------------------------------------------------------
-- 5. Execution/payment frontier.
------------------------------------------------------------------------

record SuzukiMainSameObjectFrontier : Set where
  constructor suzuki-main-same-object-frontier
  field
    primaryPaperPaid : Bool
    primaryThesis729ProducerRoutePaid : Bool
    primarySupplementQuotientMapLocated : Bool
    ctbllibCandidateLabelProducerWritten : Bool
    mainQuotientMatcherWritten : Bool
    receiptRendererWritten : Bool
    focusedCheckerWritten : Bool
    gapExecutionObserved : Bool
    base1458MainRowPaid : Bool
    twelvePairFamilyOuterMatchPaid : Bool
    seventyEightPairFamilyOuterMatchPaid : Bool
    twelveMN3BDescentPaid : Bool
    seventyEightMN3BDescentPaid : Bool
    actualRestrictedMonsterOccurrencePaid : Bool
    individualZetaAtlasLabelOrientationPaid : Bool
    nextResidual : String
open SuzukiMainSameObjectFrontier public

currentSuzukiMainSameObjectFrontier : SuzukiMainSameObjectFrontier
currentSuzukiMainSameObjectFrontier =
  suzuki-main-same-object-frontier
    true true true true true true true
    false false false false false false false false
    "run scripts/check_monster_3b_suzuki_main_quotient_match.sh in a GAP/CTblLib environment. A successful receipt pays the fused degree-1458 main row, the 12a/b and 78a/b pair-family products, quotient descent, and actual Monster occurrence by full character equality. Do not promote individual a/b labels into W_zeta from that receipt: retain individual zeta orientation as the next separate quotient-kernel/phase-resolved leaf."
