module DASHI.Wikimedia.IbrahimMonster3BDiagonalC3QuotientOrientationSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BSuzukiQuotientDescentCorrectionExact as Descent
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact as PairMatch

------------------------------------------------------------------------
-- DIAGONAL C3 QUOTIENT / PHASE-ORIENTATION SNOWBALL
--
-- Bray--Wilson 2006 makes the central-product ambiguity completely explicit.
-- Let <t1> be the normal C3 in 6.Suz:2 and <t2> the relevant normal C3 in the
-- extraspecial-side representation.  In their modular construction, quotienting
-- by one of
--
--   < t1 t2 >      or      < t1 t2^-1 >
--
-- gives the Monster subgroup 3^(1+12).2.Suz:2, while the other gives the wrong
-- central product.  They distinguish the two using explicit generator words.
--
-- This is precisely the missing orientation leaf after a pair-family character
-- match.  It tells us that "same phase" vs "inverse phase" is not terminology;
-- it is an exact diagonal-kernel choice that must be paid by the concrete
-- quotient/representation data.
--
-- IMPORTANT WrongType boundary:
-- the paper's 12+ / 12- are modular F3 representation labels.  CTblLib's
-- complex 12a / 12b are ordinary-character labels.  They are related research
-- coordinates but are NOT definitionally the same objects.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Primary source attribution.
------------------------------------------------------------------------

brayWilsonExplicitRepresentations : Attribution.AttributedSource
brayWilsonExplicitRepresentations = Attribution.mkDOISource
  "John N. Bray; Robert A. Wilson"
  "Explicit representations of maximal subgroups of the Monster"
  "Journal of Algebra 300(2), 834-857"
  "2006"
  "10.1016/j.jalgebra.2005.12.017"
  "https://doi.org/10.1016/j.jalgebra.2005.12.017"
  Attribution.academicArticleSource
  "independent primary source for the two diagonal C3 quotient choices, the explicit generator-word discrimination of the Monster central product, and the modular 24*729=17496 representation route"
  Attribution.publicAttribution

brayWilsonExplicitAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt brayWilsonExplicitRepresentations

paperDOI : String
paperDOI = "10.1016/j.jalgebra.2005.12.017"

record DiagonalQuotientExternalCoordinates : Set where
  constructor diagonal-quotient-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasOrientationAuthority : Bool
open DiagonalQuotientExternalCoordinates public

canonicalDiagonalQuotientExternalCoordinates : DiagonalQuotientExternalCoordinates
canonicalDiagonalQuotientExternalCoordinates =
  diagonal-quotient-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "not applicable: diagonal central-product orientation is a representation/quotient identity, not an integer-sequence fact"
    false

------------------------------------------------------------------------
-- 2. Typed central-product alternatives.
------------------------------------------------------------------------

data DiagonalKernelChoice : Set where
  t1TimesT2 : DiagonalKernelChoice
  t1TimesT2Inverse : DiagonalKernelChoice

record ExplicitDiagonalQuotientTest : Set₁ where
  constructor explicit-diagonal-quotient-test
  field
    firstCentralGenerator : Set
    secondCentralGenerator : Set
    candidateKernel : DiagonalKernelChoice
    quotientRepresentation : Set
    sourceGeneratorWordsEvaluated : Set
    monsterSubgroupRecognition : Set

open ExplicitDiagonalQuotientTest public

record MonsterDiagonalOrientationReceipt : Set₁ where
  constructor monster-diagonal-orientation-receipt
  field
    firstCandidate : ExplicitDiagonalQuotientTest
    secondCandidate : ExplicitDiagonalQuotientTest
    candidatesUseOppositeKernels : Set
    exactlyOneRecognisedAsMonster : Set
    selectedMonsterKernel : DiagonalKernelChoice
    rejectedCentralProduct : Set

open MonsterDiagonalOrientationReceipt public

------------------------------------------------------------------------
-- 3. Relation to the pair-family character receipt.
------------------------------------------------------------------------

record IndividualComplexCharacterOrientation
  (pairs : PairMatch.SuzukiMainQuotientSameObjectReceipt) : Set₁ where
  field
    diagonalOrientation : MonsterDiagonalOrientationReceipt
    selectedTwelveComplexAtlasLabel : String
    selectedSeventyEightComplexAtlasLabel : String

    complexTwelveCandidateBelongsToPaidPair : Set
    complexSeventyEightCandidateBelongsToPaidPair : Set
    quotientKernelCompatibilityForTwelve : Set
    quotientKernelCompatibilityForSeventyEight : Set
    selectedZetaSectorSameObject : Set

open IndividualComplexCharacterOrientation public

------------------------------------------------------------------------
-- 4. Modular-vs-complex WrongType firewall.
------------------------------------------------------------------------

data ModularTwelvePlusEqualsComplexTwelveA : Set where
data ModularTwelveMinusEqualsComplexTwelveB : Set where
data ModularCentralProductChoiceCreatesComplexCharacterOrientation : Set where
data Degree17496CreatesDiagonalKernelIdentity : Set where

modularPlusDoesNotEqualComplexA : ModularTwelvePlusEqualsComplexTwelveA → ⊥
modularPlusDoesNotEqualComplexA ()

modularMinusDoesNotEqualComplexB : ModularTwelveMinusEqualsComplexTwelveB → ⊥
modularMinusDoesNotEqualComplexB ()

modularChoiceDoesNotCreateComplexOrientation :
  ModularCentralProductChoiceCreatesComplexCharacterOrientation → ⊥
modularChoiceDoesNotCreateComplexOrientation ()

degreeDoesNotCreateKernelIdentity : Degree17496CreatesDiagonalKernelIdentity → ⊥
degreeDoesNotCreateKernelIdentity ()

------------------------------------------------------------------------
-- 5. Exact proof-search status.
------------------------------------------------------------------------

record DiagonalOrientationFrontier : Set where
  constructor diagonal-orientation-frontier
  field
    brayWilsonPrimarySourcePaid : Bool
    brayWilsonDOIPaid : Bool
    twoDiagonalKernelChoicesSourcePaid : Bool
    exactlyOneMonsterCentralProductSourcePaid : Bool
    explicitWordDiscriminatorSourcePaid : Bool
    modularTwentyFourTimes729RouteSourcePaid : Bool
    modularVsComplexWrongTypeOwned : Bool
    pairFamilySameObjectExecutionPaid : Bool
    exactQGtoN3BKernelChoicePaid : Bool
    complexTwelveABOrientationPaid : Bool
    complexSeventyEightABOrientationPaid : Bool
    actualSelectedZetaSectorPaid : Bool
    nextResidual : String
open DiagonalOrientationFrontier public

currentDiagonalOrientationFrontier : DiagonalOrientationFrontier
currentDiagonalOrientationFrontier =
  diagonal-orientation-frontier
    true true true true true true true
    false false false false false
    "first execute the pair-family Suzuki/main quotient matcher. Then inspect the concrete kernel of the primary main->MN3B quotient map and determine whether it is the t1*t2 or t1*t2^-1 diagonal from Bray--Wilson. Use that kernel identity, not modular label analogy, to select the quotient-compatible complex 12a/b and 78a/b members for the chosen extraspecial zeta phase. A separate character equality/phase receipt must connect those complex labels to W_zeta; do not equate modular 12+/12- with complex 12a/12b by name."
