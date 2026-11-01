module DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Foundations.JPlusOneScaleBridge as JLocal
import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as TwoComponent
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- IBRAHIM / BASE369 / J / OEIS / MOONSHINE SNOWBALL
--
-- Current external coordinates inspected 2026-09-10:
--   j-invariant: Wikidata Q287419; enwiki oldid 1367363754.
--   monstrous moonshine: Wikidata Q392440; enwiki oldid 1355357732.
--   mathematics: Wikidata Q395.
--   OEIS A000521: coefficients of modular j.
--   OEIS A014708: normalized Monster class-1A McKay-Thompson series.
--   OEIS A001379: dimensions of irreducible Monster representations.
--   OEIS A309510: divisors of 196883.
--
-- Current English first-body links:
--   j-invariant -> Mathematics.
--   Monstrous moonshine -> Mathematics.
-- These are current revision-sensitive navigation coordinates, not claims
-- about Ibrahim et al.'s November-2014 snapshot.
------------------------------------------------------------------------

jInvariantQid : Identity.ExternalIdentityDemand
jInvariantQid = Identity.mkOptionalIdentityDemand
  "Base369/J/OEIS/Ibrahim snowball"
  "modular j-invariant exact external identity"
  "j-invariant"
  Identity.wikidataQid
  (Identity.verified "Q287419" "Wikidata oldid 2489948105 inspected 2026-09-10")

jInvariantWikipedia : Identity.ExternalIdentityDemand
jInvariantWikipedia = Identity.mkOptionalIdentityDemand
  "Base369/J/OEIS/Ibrahim snowball"
  "j-invariant exact current Wikipedia revision"
  "J-invariant"
  Identity.canonicalURL
  (Identity.verified
    "https://en.wikipedia.org/w/index.php?title=J-invariant&oldid=1367363754"
    "permanent-link target exposed by current enwiki page on 2026-09-10")

moonshineQid : Identity.ExternalIdentityDemand
moonshineQid = Identity.mkOptionalIdentityDemand
  "Base369/J/OEIS/Ibrahim snowball"
  "monstrous moonshine exact external identity"
  "monstrous moonshine"
  Identity.wikidataQid
  (Identity.verified "Q392440" "Wikidata oldid 2465725082 inspected 2026-09-10")

moonshineWikipedia : Identity.ExternalIdentityDemand
moonshineWikipedia = Identity.mkOptionalIdentityDemand
  "Base369/J/OEIS/Ibrahim snowball"
  "monstrous moonshine exact current Wikipedia revision"
  "Monstrous moonshine"
  Identity.canonicalURL
  (Identity.verified
    "https://en.wikipedia.org/w/index.php?title=Monstrous_moonshine&oldid=1355357732"
    "permanent-link target exposed by current enwiki page on 2026-09-10")

mathematicsQid : Identity.ExternalIdentityDemand
mathematicsQid = Identity.mkOptionalIdentityDemand
  "Ibrahim current first-link parent"
  "mathematics parent identity"
  "mathematics"
  Identity.wikidataQid
  (Identity.verified "Q395" "Wikidata oldid 2535518391 inspected 2026-09-10")

record OEISCoordinate : Set where
  constructor oeis-coordinate
  field
    oeisId : String
    subject : String
    relationToRepo : String
    exactSequenceIdentity : Bool
    createsMoonshineTheorem : Bool
open OEISCoordinate public

jCoefficientOEIS : OEISCoordinate
jCoefficientOEIS = oeis-coordinate
  "A000521"
  "coefficients of modular j as a q-series"
  "contains 196884 as the first positive-q coefficient used by the repo's McKay arithmetic"
  true false

monsterRepresentationOEIS : OEISCoordinate
monsterRepresentationOEIS = oeis-coordinate
  "A001379"
  "degrees of irreducible representations of the Monster group"
  "contains 196883 as the smallest nontrivial degree used by the repo's McKay arithmetic"
  true false

class1AMcKayThompsonOEIS : OEISCoordinate
class1AMcKayThompsonOEIS = oeis-coordinate
  "A014708"
  "McKay-Thompson series of class 1A / normalized J-series"
  "external sequence coordinate for the normalized moonshine coefficient lane"
  true false

monster196883DivisorsOEIS : OEISCoordinate
monster196883DivisorsOEIS = oeis-coordinate
  "A309510"
  "divisors of 196883"
  "external arithmetic coordinate for 196883; does not explain the repo's 196830+53 decomposition"
  true false

------------------------------------------------------------------------
-- Exact repo-native arithmetic retained.
------------------------------------------------------------------------

repoMcKayPlusOne : 196883 + 1 ≡ 196884
repoMcKayPlusOne = JLocal.moonshineCoefficientIsRepresentationPlusOne

repoReduced369Dimension : TwoComponent.totalDimension TwoComponent.reducedMonsterTwoComponent ≡ 196883
repoReduced369Dimension = TwoComponent.reducedTotalIs196883

repoFull369Dimension : TwoComponent.totalDimension TwoComponent.fullWeightTwoTwoComponent ≡ 196884
repoFull369Dimension = TwoComponent.fullTotalIs196884

repoPrimary369Component : TwoComponent.primary369Component TwoComponent.reducedMonsterTwoComponent ≡ 196830
repoPrimary369Component = TwoComponent.reducedPrimaryIs196830

repoResidual53 : TwoComponent.secondary369Component TwoComponent.reducedMonsterTwoComponent ≡ 53
repoResidual53 = TwoComponent.reducedSecondaryIs53

------------------------------------------------------------------------
-- Current Ibrahim-style navigation probes.
------------------------------------------------------------------------

record CurrentFirstBodyProbe : Set where
  constructor current-first-body-probe
  field
    article : String
    revision : String
    firstBodyLink : String
    firstBodyQid : String
    observedOn : String
    equalsIbrahim2014Edge : Bool
open CurrentFirstBodyProbe public

jInvariantToMathematics : CurrentFirstBodyProbe
jInvariantToMathematics = current-first-body-probe
  "J-invariant" "1367363754" "Mathematics" "Q395" "2026-09-10" false

moonshineToMathematics : CurrentFirstBodyProbe
moonshineToMathematics = current-first-body-probe
  "Monstrous moonshine" "1355357732" "Mathematics" "Q395" "2026-09-10" false

------------------------------------------------------------------------
-- Snowball consequences.
------------------------------------------------------------------------

record JMoonshineSnowballProjection : Set where
  constructor j-moonshine-snowball-projection
  field
    localJAndModularJRemainDistinct : Bool
    modularJAndMoonshineConnectedByExternalSource : Bool
    a000521AndA001379MayMeetAtMcKayArithmetic : Bool
    a014708MayRefineNormalizedSeriesIdentity : Bool
    a309510MayRefineArithmeticFactorisation : Bool
    oeisCreatesBase369Decomposition : Bool
    sharedMathematicsFirstLinkCreatesSemanticEquivalence : Bool
    currentFirstLinkBackdatesIbrahim2014 : Bool
    failedFactorisationMaySnowballNewAxis : Bool
open JMoonshineSnowballProjection public

canonicalJMoonshineSnowballProjection : JMoonshineSnowballProjection
canonicalJMoonshineSnowballProjection = j-moonshine-snowball-projection
  true true true true true false false false true

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LocalJUnitEqualsModularJ : Set where
data OEISIdentityCreatesBase369Semantics : Set where
data SharedMathematicsParentCreatesSameObject : Set where
data Numerical196883CreatesMonsterRepresentation : Set where
data CurrentFirstLinkCreatesHistoricalIbrahimEdge : Set where

localJUnitIsNotModularJ : LocalJUnitEqualsModularJ → ⊥
localJUnitIsNotModularJ ()

oeisDoesNotCreateBase369Semantics : OEISIdentityCreatesBase369Semantics → ⊥
oeisDoesNotCreateBase369Semantics ()

sharedParentDoesNotCreateSameObject : SharedMathematicsParentCreatesSameObject → ⊥
sharedParentDoesNotCreateSameObject ()

numberDoesNotCreateRepresentation : Numerical196883CreatesMonsterRepresentation → ⊥
numberDoesNotCreateRepresentation ()

currentProbeDoesNotBackdateIbrahim : CurrentFirstLinkCreatesHistoricalIbrahimEdge → ⊥
currentProbeDoesNotBackdateIbrahim ()

record JOEISIbrahimBoundary : Set where
  constructor j-oeis-ibrahim-boundary
  field
    qidsRetained : Bool
    wikipediaRevisionsRetained : Bool
    oeisIdsRetained : Bool
    repoArithmeticRetained : Bool
    localJVsModularJSeparated : Bool
    sequenceIdentityVsSemanticMeaningSeparated : Bool
    currentTraversalVsHistoricalIbrahimSeparated : Bool
    allPairsSnowballEnabled : Bool
open JOEISIbrahimBoundary public

canonicalJOEISIbrahimBoundary : JOEISIbrahimBoundary
canonicalJOEISIbrahimBoundary =
  j-oeis-ibrahim-boundary true true true true true true true true
