module DASHI.Wikimedia.Base369NumberQidRoleCrosswalkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.Base369OEISWikidataTeslaSnowballExact as Snow369

------------------------------------------------------------------------
-- 3 / 6 / 9 ROLE CROSSWALK
--
-- External coordinates inspected 2026-09-10:
--   6  = Wikidata Q23488, natural number;
--   9  = Wikidata Q19108, natural number and power of three;
--   27 = Wikidata Q433353, natural number and power of three.
--
-- The internal Base369 carrier has TriTruth, HexTruth and NonaryTruth as
-- different finite types.  The triadic tower continues 3 -> 9 -> 27, while
-- HexTruth is a separate six-state cyclic carrier.  Therefore the cultural
-- label "369" must not collapse the three roles into one same-object claim.
------------------------------------------------------------------------

number6Qid : Identity.ExternalIdentityDemand
number6Qid = Identity.mkOptionalIdentityDemand
  "Base369 3/6/9 role crosswalk"
  "natural number 6 identity"
  "6"
  Identity.wikidataQid
  (Identity.verified "Q23488" "Wikidata inspected 2026-09-10")

number9Qid : Identity.ExternalIdentityDemand
number9Qid = Identity.mkOptionalIdentityDemand
  "Base369 3/6/9 role crosswalk"
  "natural number 9 identity"
  "9"
  Identity.wikidataQid
  (Identity.verified "Q19108" "Wikidata inspected 2026-09-10; item records power-of-three relation")

number27Qid : Identity.ExternalIdentityDemand
number27Qid = Snow369.number27Qid

record Base369NumberRole : Set₁ where
  constructor base369-number-role
  field
    numeral : String
    qid : String
    internalCarrier : Set
    internalRole : String
    belongsToA000244Power3Tower : Bool
    sameObjectAsOther369Roles : Bool
open Base369NumberRole public

threeRole : Base369NumberRole
threeRole = base369-number-role
  "3" "power-of-three coordinate; QID for number 3 not required by this tranche"
  Base.TriTruth
  "three-state truth/refinement carrier and C3 tower level"
  true false

sixRole : Base369NumberRole
sixRole = base369-number-role
  "6" "Q23488"
  Base.HexTruth
  "independent six-state cyclic/hexadic carrier"
  false false

nineRole : Base369NumberRole
nineRole = base369-number-role
  "9" "Q19108"
  Base.NonaryTruth
  "nine-state nonary carrier and C9 tower level"
  true false

record ThreeSixNineDecomposition : Set where
  constructor three-six-nine-decomposition
  field
    triadicPowerTowerHasThree : Bool
    triadicPowerTowerHasNine : Bool
    triadicPowerTowerHasSix : Bool
    hexadicCarrierExistsSeparately : Bool
    cultural369LabelMayIndexAllThree : Bool
    culturalLabelCreatesSingleFormalObject : Bool
    allPairsSearchMayCompareTheirProperties : Bool
open ThreeSixNineDecomposition public

canonicalThreeSixNineDecomposition : ThreeSixNineDecomposition
canonicalThreeSixNineDecomposition = three-six-nine-decomposition
  true true false true true false true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SixIsPowerOfThreeTowerLevel : Set where
data Cultural369LabelCreatesFormalProduct : Set where
data SameNumeralCreatesSameCarrier : Set where

data TeslaAttributionUnifiesNumberRoles : Set where

sixIsNotPower3TowerLevel : SixIsPowerOfThreeTowerLevel → ⊥
sixIsNotPower3TowerLevel ()

culturalLabelDoesNotCreateFormalProduct : Cultural369LabelCreatesFormalProduct → ⊥
culturalLabelDoesNotCreateFormalProduct ()

sameNumeralDoesNotCreateSameCarrier : SameNumeralCreatesSameCarrier → ⊥
sameNumeralDoesNotCreateSameCarrier ()

teslaAttributionDoesNotUnifyRoles : TeslaAttributionUnifiesNumberRoles → ⊥
teslaAttributionDoesNotUnifyRoles ()

record Base369NumberQidBoundary : Set where
  constructor base369-number-qid-boundary
  field
    number6QidRecorded : Bool
    number9QidRecorded : Bool
    number27QidReused : Bool
    sixSeparatedFromPowerOfThreeTower : Bool
    triHexNonaryCarriersRemainDistinct : Bool
    allPairsEligibilityRetained : Bool
    qidCreatesSemanticRole : Bool
open Base369NumberQidBoundary public

canonicalBase369NumberQidBoundary : Base369NumberQidBoundary
canonicalBase369NumberQidBoundary = base369-number-qid-boundary
  true true true true true true false
