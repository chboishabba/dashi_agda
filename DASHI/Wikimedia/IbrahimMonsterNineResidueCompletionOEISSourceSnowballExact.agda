module DASHI.Wikimedia.IbrahimMonsterNineResidueCompletionOEISSourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Nonary
import DASHI.Moonshine.Base369MonsterTwoComponentCompletionBidiExact as Two
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine
import DASHI.Wikimedia.IbrahimMonster3BOEIS369UnifiedCrossPollinationExact as MonsterOEIS

------------------------------------------------------------------------
-- NINE-RESIDUE COMPLETION
--
-- The primary 10*3^9 bulk is already divisible by 9.  Therefore the mod-nine
-- defect of 196883 is carried entirely by the structured secondary residual:
--
--   53 = 5*9 + 8 = 6*9 - 1,
--   196883 = 21875*9 + 8 = 21876*9 - 1,
--   54 = 6*9,
--   196884 = 21876*9.
--
-- This is exact arithmetic and a useful Base369/nonary completion shadow.  It
-- does not identify the local 53 invariant-complement, the Monster residual
-- representation, and the weight-two conformal line without the existing
-- action/intertwiner obligations.
------------------------------------------------------------------------

bulkAsNineTimes21870 : 196830 ≡ 9 * 21870
bulkAsNineTimes21870 = refl

regularMultiplicityAsNineTimes7290 : 65610 ≡ 9 * 7290
regularMultiplicityAsNineTimes7290 = refl

fiftyThreeAsFiveNinesPlusEight : 53 ≡ 5 * 9 + 8
fiftyThreeAsFiveNinesPlusEight = refl

fiftyThreePlusOneClosesSixthNine : 53 + 1 ≡ 6 * 9
fiftyThreePlusOneClosesSixthNine = refl

fiftyFourAsSixNines : 54 ≡ 6 * 9
fiftyFourAsSixNines = refl

monsterAsNineTimes21875PlusEight : 196883 ≡ 9 * 21875 + 8
monsterAsNineTimes21875PlusEight = refl

monsterPlusOneClosesNine : 196883 + 1 ≡ 9 * 21876
monsterPlusOneClosesNine = refl

moonshineWeightTwoAsNineTimes21876 : 196884 ≡ 9 * 21876
moonshineWeightTwoAsNineTimes21876 = refl

monsterResidualCarriesSameNineRemainderAs53 :
  196883 ≡ 9 * 21870 + (5 * 9 + 8)
monsterResidualCarriesSameNineRemainderAs53 = refl

bulkPlusFullSecondaryIsNineDivisible :
  196830 + 54 ≡ 9 * 21876
bulkPlusFullSecondaryIsNineDivisible = refl

------------------------------------------------------------------------
-- Existing nonary owner pays the local 54 -> 53 structural reduction.
------------------------------------------------------------------------

local53IsFiveNinesPlusEight : Nonary.reducedSixByNine ≡ 53
local53IsFiveNinesPlusEight = Nonary.reducedSixByNineIsFiftyThree

local54IsSixNines : Nonary.fullSixByNine ≡ 54
local54IsSixNines = Nonary.fullSixByNineIsFiftyFour

local53To54PointedShape = Two.secondaryFiftyThreeToFiftyFourShape

globalNineStratification = Nine.currentNineStratificationFrontier

divisor369Surface = MonsterOEIS.canonicalDivisor369Surface

------------------------------------------------------------------------
-- QID / OEIS / primary-source coordinates.
------------------------------------------------------------------------

record NineResidueExternalCoordinates : Set where
  constructor nine-residue-external-coordinates
  field
    nineQid : String
    fiftyThreeQid : String
    fiftyFourQid : String
    jInvariantQid : String
    monstrousMoonshineQid : String
    powersOfThreeOEIS : String
    tenTimesPowersOfThreeOEIS : String
    divisors196884OEIS : String
    monsterIrrepDegreeOEIS : String
    exactArithmeticPaidLocally : Bool
    oeisCreatesCompletionSemantics : Bool
open NineResidueExternalCoordinates public

canonicalNineResidueExternalCoordinates : NineResidueExternalCoordinates
canonicalNineResidueExternalCoordinates = nine-residue-external-coordinates
  "Q19108" "Q712808" "Q290669" "Q287419" "Q392440"
  "A000244" "A005052" "A199014" "A001379"
  true false

conwayNortonSource : Attribution.AttributedSource
conwayNortonSource = Attribution.mkDOISource
  "John H. Conway; Simon P. Norton"
  "Monstrous Moonshine"
  "Bulletin of the London Mathematical Society 11, 308-339"
  "1979"
  "10.1112/blms/11.3.308"
  "https://doi.org/10.1112/blms/11.3.308"
  Attribution.academicArticleSource
  "primary moonshine provenance for the Monster/modular-function relationship; not a source for the internal mod-nine Base369 decomposition"
  Attribution.publicAttribution

griessSource : Attribution.AttributedSource
griessSource = Attribution.mkDOISource
  "Robert L. Griess Jr."
  "The Friendly Giant"
  "Inventiones Mathematicae 69, 1-102"
  "1982"
  "10.1007/BF01389186"
  "https://doi.org/10.1007/BF01389186"
  Attribution.academicArticleSource
  "primary Monster representation/algebra provenance; not a source for the Base369 nonary completion interpretation"
  Attribution.publicAttribution

conwayNortonAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt conwayNortonSource
griessAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt griessSource

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CongruenceCreatesRepresentation : Set where
data MinusOneModNineCreatesMoonshine : Set where
data NineDivisibilityIdentifiesInvariantLine : Set where

congruenceDoesNotCreateRepresentation : CongruenceCreatesRepresentation → ⊥
congruenceDoesNotCreateRepresentation ()

minusOneDoesNotCreateMoonshine : MinusOneModNineCreatesMoonshine → ⊥
minusOneDoesNotCreateMoonshine ()

nineDivisibilityDoesNotIdentifyInvariantLine : NineDivisibilityIdentifiesInvariantLine → ⊥
nineDivisibilityDoesNotIdentifyInvariantLine ()

record NineResidueCompletionFrontier : Set where
  constructor nine-residue-completion-frontier
  field
    bulkDivisibleByNinePaid : Bool
    residual53IsMinusOneFromSixNinesPaid : Bool
    monster196883HasRemainderEightModNinePaid : Bool
    full54DivisibleByNinePaid : Bool
    moonshine196884DivisibleByNinePaid : Bool
    localNonary53To54ReductionPaidUpstream : Bool
    exactCongruenceCreatesMonsterRepresentation : Bool
    nextResidual : String
open NineResidueCompletionFrontier public

currentNineResidueCompletionFrontier : NineResidueCompletionFrontier
currentNineResidueCompletionFrontier = nine-residue-completion-frontier
  true true true true true true false
  "compare the exact mod-nine completion with the role-indexed pointed-extension maps and the literal 3B residual action only after the same-action Residual53 bridge is recovered; retain A199014 divisibility as an external arithmetic receipt, not representation authority"
