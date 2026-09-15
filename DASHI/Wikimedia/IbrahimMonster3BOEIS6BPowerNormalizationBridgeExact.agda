module DASHI.Wikimedia.IbrahimMonster3BOEIS6BPowerNormalizationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact as Occurrence

------------------------------------------------------------------------
-- MONSTER 6B -> 3B POWER EDGE / OEIS NORMALIZATION BOUNDARY
--
-- Two independent facts meet here and must remain role-distinct:
--
--   ATLAS: Monster class 3B has 6B in its "Power up" list.  Since 6B has
--   order 6 and 3B has order 3, the relevant power is the square: 6B^2 -> 3B.
--
--   OEIS:
--     A121665 = 1/q + 12 + 78 q + 364 q^2 + ...
--       (class 6B, explicitly with a(0)=12),
--     A007255 = 1/q      + 78 q + 364 q^2 + ...
--       (normalized class-6B McKay--Thompson series).
--
-- OEIS itself states A121665 and A007255 agree except at n=0.  Hence 78 is
-- stable across these two presentations whereas 12 is normalization-dependent.
-- This materially weakens any attempted identification of the N(3B) 12+78
-- multiplicity split with the first two displayed numbers of A121665.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source graph.
------------------------------------------------------------------------

conwayNorton : Attribution.AttributedSource
conwayNorton = Attribution.mkDOISource
  "J. H. Conway; S. P. Norton"
  "Monstrous Moonshine"
  "Bulletin of the London Mathematical Society 11(3), 308-339"
  "1979"
  "10.1112/blms/11.3.308"
  "https://doi.org/10.1112/blms/11.3.308"
  Attribution.academicArticleSource
  "primary moonshine provenance for Monster McKay-Thompson class assignments; does not identify coefficients with N(3B) multiplicity spaces"
  Attribution.publicAttribution

atlasMonster : Attribution.AttributedSource
atlasMonster = Attribution.mkNoDOISource
  "ATLAS of Finite Group Representations"
  "Monster group M: conjugacy classes and power-up table"
  "ATLAS of Group Representations web manifestation"
  "retrieved 2026-09-15"
  "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/"
  (Attribution.namedSourceKind "finite-group class-table database")
  "authoritative class/power navigation for Monster conjugacy classes; pays the 6B-square-to-3B class edge, not any moonshine-coefficient/multiplicity identification"
  Attribution.publicAttribution

oeisA121665 : Attribution.AttributedSource
oeisA121665 = Attribution.mkNoDOISource
  "Michael Somos; OEIS contributors"
  "A121665: McKay-Thompson series of class 6B for the Monster group with a(0)=12"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A121665"
  (Attribution.namedSourceKind "integer-sequence database record")
  "source for the displayed 6B series 1/q + 12 + 78 q + ... and its explicit a(0)=12 normalization; not multiplicity-space authority"
  Attribution.publicAttribution

oeisA007255 : Attribution.AttributedSource
oeisA007255 = Attribution.mkNoDOISource
  "N. J. A. Sloane; OEIS contributors"
  "A007255: McKay-Thompson series of class 6B for Monster"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A007255"
  (Attribution.namedSourceKind "integer-sequence database record")
  "source for the normalized 6B series 1/q + 78 q + 364 q^2 + ...; explicitly agrees with A121665 apart from n=0"
  Attribution.publicAttribution

conwayNortonAttribution = Snowball.canonicalSourceRoleSnowballReceipt conwayNorton
atlasMonsterAttribution = Snowball.canonicalSourceRoleSnowballReceipt atlasMonster
a121665Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA121665
a007255Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA007255

------------------------------------------------------------------------
-- 2. Exact numerical/presentation surface.
------------------------------------------------------------------------

monsterSixBClass : String
monsterSixBClass = "Monster class 6B"

monsterThreeBClass : String
monsterThreeBClass = "Monster class 3B"

a121665ConstantTwelve : Nat
a121665ConstantTwelve = 12

a121665QCoefficientSeventyEight : Nat
a121665QCoefficientSeventyEight = 78

a007255NormalizedConstantZero : Nat
a007255NormalizedConstantZero = 0

a007255QCoefficientSeventyEight : Nat
a007255QCoefficientSeventyEight = 78

sharedQCoefficientSeventyEight :
  a121665QCoefficientSeventyEight ≡ a007255QCoefficientSeventyEight
sharedQCoefficientSeventyEight = refl

twelveIsNormalizationDependent : Bool
twelveIsNormalizationDependent = true

------------------------------------------------------------------------
-- 3. Class-power edge.  The class table pays only the element/class relation.
------------------------------------------------------------------------

record MonsterClassPowerEdge : Set where
  constructor monster-class-power-edge
  field
    sourceClass : String
    exponent : Nat
    targetClass : String
    atlasPowerUpManifestation : String
    classPowerPaid : Bool
    sameRepresentativePaid : Bool
    sameVectorSpacePaid : Bool
open MonsterClassPowerEdge public

sixBSquareLandsInThreeB : MonsterClassPowerEdge
sixBSquareLandsInThreeB = monster-class-power-edge
  monsterSixBClass 2 monsterThreeBClass
  "ATLAS Monster conjugacy table: row 3B lists 6B in Power up"
  true false false

------------------------------------------------------------------------
-- 4. Compare with the separately source-paid N(3B) degree split.
------------------------------------------------------------------------

restrictionTwelve : Nat
restrictionTwelve = 12

restrictionSeventyEight : Nat
restrictionSeventyEight = 78

sameDisplayedTwelve : a121665ConstantTwelve ≡ restrictionTwelve
sameDisplayedTwelve = refl

sameDisplayedSeventyEight : a121665QCoefficientSeventyEight ≡ restrictionSeventyEight
sameDisplayedSeventyEight = refl

restrictionTwelvePlusSeventyEight : restrictionTwelve + restrictionSeventyEight ≡ 90
restrictionTwelvePlusSeventyEight = Occurrence.multiplicityTotal

record SixBThreeBNumericalEncounter : Set where
  constructor sixb-threeb-numerical-encounter
  field
    sixBSquaresToThreeB : Bool
    a121665DisplaysTwelve : Bool
    sixBNormalizedSeriesDisplaysTwelve : Bool
    both6BPresentationsDisplaySeventyEight : Bool
    n3BRestrictionHasTwelveFactorUpstream : Bool
    n3BRestrictionHasSeventyEightFactorUpstream : Bool
    twelveCoefficientSameRolePaid : Bool
    seventyEightCoefficientSameRolePaid : Bool
    multiplicityRepresentationSameObjectPaid : Bool
open SixBThreeBNumericalEncounter public

canonicalSixBThreeBNumericalEncounter : SixBThreeBNumericalEncounter
canonicalSixBThreeBNumericalEncounter = sixb-threeb-numerical-encounter
  true true false true true true false false false

------------------------------------------------------------------------
-- 5. WrongType / non-promotion barriers.
------------------------------------------------------------------------

data SixBPowerRelationCreatesMultiplicityWeld : Set where
data SeventyEightCoefficientIdentifiesMultiplicitySeventyEight : Set where
data NormalizationTwelveIdentifiesMultiplicityTwelve : Set where
data SharedTwelveSeventyEightCreatesSameCharacter : Set where
data OEISCreatesRestrictionIntertwiner : Set where

data ConwayNortonCitationCreatesN3BAction : Set where

sixBPowerRelationDoesNotCreateMultiplicityWeld :
  SixBPowerRelationCreatesMultiplicityWeld → ⊥
sixBPowerRelationDoesNotCreateMultiplicityWeld ()

seventyEightCoefficientDoesNotIdentifyMultiplicitySeventyEight :
  SeventyEightCoefficientIdentifiesMultiplicitySeventyEight → ⊥
seventyEightCoefficientDoesNotIdentifyMultiplicitySeventyEight ()

normalizationTwelveDoesNotIdentifyMultiplicityTwelve :
  NormalizationTwelveIdentifiesMultiplicityTwelve → ⊥
normalizationTwelveDoesNotIdentifyMultiplicityTwelve ()

sharedPairDoesNotCreateSameCharacter : SharedTwelveSeventyEightCreatesSameCharacter → ⊥
sharedPairDoesNotCreateSameCharacter ()

oeisDoesNotCreateRestrictionIntertwiner : OEISCreatesRestrictionIntertwiner → ⊥
oeisDoesNotCreateRestrictionIntertwiner ()

conwayNortonCitationDoesNotCreateN3BAction : ConwayNortonCitationCreatesN3BAction → ⊥
conwayNortonCitationDoesNotCreateN3BAction ()

------------------------------------------------------------------------
-- 6. Pareto frontier.
------------------------------------------------------------------------

record OEIS6BPowerNormalizationFrontier : Set where
  constructor oeis-6b-power-normalization-frontier
  field
    conwayNortonPrimaryMoonshineSourcePaid : Bool
    atlasSixBSquareToThreeBClassEdgePaid : Bool
    a121665SixBPresentationPaid : Bool
    a007255NormalizedSixBPresentationPaid : Bool
    a121665ConstantTwelvePaid : Bool
    normalizedSixBConstantZeroPaid : Bool
    stableSixBQCoefficientSeventyEightPaid : Bool
    twelveNormalizationDependencePaid : Bool
    n3BTwelveSeventyEightDegreeOccurrencePaidUpstream : Bool
    sixBToThreeBSameMultiplicityRepresentationPaid : Bool
    nextResidual : String
open OEIS6BPowerNormalizationFrontier public

oeis6BPowerNormalizationFrontier : OEIS6BPowerNormalizationFrontier
oeis6BPowerNormalizationFrontier = oeis-6b-power-normalization-frontier
  true true true true true true true true true false
  "retain 6B^2 -> 3B as a genuine class-power snowball edge and 78 as a stable 6B McKay-Thompson coefficient, but demote the apparent 12,78 pair because 12 disappears under the standard A007255 normalization. Any theorem-level relation between the 6B trace series and the N(3B) 12/78 multiplicity spaces now requires an explicit restriction/twining/graded-trace transport on the same Monster/VOA action; coefficient equality or the class-power edge alone is insufficient."

restrictionOccurrenceFrontier : Occurrence.RestrictionOccurrenceFrontier
restrictionOccurrenceFrontier = Occurrence.currentRestrictionOccurrenceFrontier
