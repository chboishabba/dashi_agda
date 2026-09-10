module DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Moonshine.Base369Monster3BGlobalNineToOnePlusTwoPlusSixBidiExact as Nine
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannMultiplicityExact as SvN
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact as Rep
import DASHI.Wikimedia.IbrahimInverseZetaJCoarseFineMonsterDivisorSnowballExact as Inverse
import DASHI.Wikimedia.IbrahimC3ZetaRegularCharacterOEISQuantumGRBidiExact as Zeta

------------------------------------------------------------------------
-- MONSTER 3B / 9 = 1 + 2 + 6 / OEIS / PRIMARY-SOURCE SNOWBALL
--
-- The existing global owner already proves the exact nested shadow
--
--   10 * 3^9
--     = 3^1 * (10 * 3^2) * 3^6
--     = 3 * 90 * 729
--     = 196830.
--
-- This owner exposes the corresponding OEIS coordinates and keeps the three
-- exponent strata role-distinct:
--
--   1 : outer regular-C3 phase coordinate,
--   2 : completed trit-square multiplicity coordinate (10 * 3^2 = 90),
--   6 : finite Heisenberg / Stone-von Neumann irreducible degree 3^6 = 729.
--
-- The nontrivial zeta and inverse-zeta sectors have the literal 729 x 90
-- refinement.  The fixed phase has the same regular-bulk dimension but a
-- different representation type, so 9=1+2+6 is not a proof that all three
-- 65610 phase blocks are isomorphic as representations.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow b zero = 1
pow b (suc n) = b * pow b n

a000244 : Nat → Nat
a000244 n = pow 3 n

a005052 : Nat → Nat
a005052 n = 10 * pow 3 n

threeIsA000244Level1 : a000244 1 ≡ 3
threeIsA000244Level1 = refl

nineIsA000244Level2 : a000244 2 ≡ 9
nineIsA000244Level2 = refl

sevenTwentyNineIsA000244Level6 : a000244 6 ≡ 729
sevenTwentyNineIsA000244Level6 = refl

sixFiveSixOneIsA000244Level8 : a000244 8 ≡ 6561
sixFiveSixOneIsA000244Level8 = refl

oneNineSixEightThreeIsA000244Level9 : a000244 9 ≡ 19683
oneNineSixEightThreeIsA000244Level9 = refl

ninetyIsA005052Level2 : a005052 2 ≡ 90
ninetyIsA005052Level2 = refl

sixFiveSixOneZeroIsA005052Level8 : a005052 8 ≡ 65610
sixFiveSixOneZeroIsA005052Level8 = refl

oneNineSixEightThreeZeroIsA005052Level9 : a005052 9 ≡ 196830
oneNineSixEightThreeZeroIsA005052Level9 = refl

------------------------------------------------------------------------
-- 1 + 2 + 6 is an exponent stratification.
------------------------------------------------------------------------

nineExponentAsOnePlusTwoPlusSix : 1 + 2 + 6 ≡ 9
nineExponentAsOnePlusTwoPlusSix = refl

threePowerNineAsOneTwoSixProduct :
  a000244 9 ≡ a000244 1 * a000244 2 * a000244 6
threePowerNineAsOneTwoSixProduct = refl

completedBulkAsOneTwoSixProduct :
  a005052 9 ≡ a000244 1 * a005052 2 * a000244 6
completedBulkAsOneTwoSixProduct = refl

regularPhaseAsTwoPlusSixProduct :
  a005052 8 ≡ a005052 2 * a000244 6
regularPhaseAsTwoPlusSixProduct = refl

regularPhaseAsNinetyTimes729 : 65610 ≡ 90 * 729
regularPhaseAsNinetyTimes729 = refl

regularBulkAsThreeTimesNinetyTimes729 : 196830 ≡ 3 * 90 * 729
regularBulkAsThreeTimesNinetyTimes729 = refl

monsterAsOneTwoSixBulkPlusResidual : 196883 ≡ 3 * 90 * 729 + 53
monsterAsOneTwoSixBulkPlusResidual = refl

------------------------------------------------------------------------
-- Existing theorem-bearing owners agree with this arithmetic shadow.
------------------------------------------------------------------------

globalNineReceipt : Nine.GlobalNineStratificationBoundary
globalNineReceipt = Nine.canonicalGlobalNineStratificationBoundary

stoneVonNeumannNinetyTimes729 : 729 * 90 ≡ 65610
stoneVonNeumannNinetyTimes729 = SvN.ninetyHeisenbergDegree

representationRegularMultiplicity : Rep.regularBlockMultiplicity ≡ 65610
representationRegularMultiplicity = Rep.regularBlockMultiplicityIs65610

representationDimension : Rep.augmentation Rep.monster3BCharacter ≡ 196883
representationDimension = Rep.monster3BDimensionIs196883

representationTrace : Rep.generatorTrace Rep.monster3BCharacter ≡ 53
representationTrace = Rep.monster3BGeneratorTraceIs53

inverseZetaReceipt = Inverse.currentInverseZetaDivisorFrontier

zetaReceipt = Zeta.currentZetaBidiFrontier

------------------------------------------------------------------------
-- External graph.  These are identity/navigation coordinates, not proof.
------------------------------------------------------------------------

record NineStratificationExternalCoordinates : Set where
  constructor nine-stratification-external-coordinates
  field
    cyclicGroupQid : String
    regularRepresentationQid : String
    stoneVonNeumannTheoremQid : String
    heisenbergGroupQid : String
    rootOfUnityQid : String
    powersOfThreeOEIS : String
    tenTimesPowersOfThreeOEIS : String
    monsterRepresentationDegreeOEIS : String
    monsterDivisorOEIS : String
    oeisPaysExponentArithmeticOnly : Bool
    qidPaysRepresentationTheorem : Bool
open NineStratificationExternalCoordinates public

canonicalNineStratificationExternalCoordinates : NineStratificationExternalCoordinates
canonicalNineStratificationExternalCoordinates =
  nine-stratification-external-coordinates
    "Q245462" "Q1555242" "Q7619449" "Q1601337" "Q756747"
    "A000244" "A005052" "A001379" "A309510"
    true false

------------------------------------------------------------------------
-- Primary/source provenance.  Source identity and theorem meaning remain
-- distinct from OEIS/QID coordinates.
------------------------------------------------------------------------

barracloughWilsonSource : Attribution.AttributedSource
barracloughWilsonSource = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary Monster subgroup/character-table provenance for the 3B restriction lane; does not source the Base369 or OEIS interpretation"
  Attribution.publicAttribution

terrasSource : Attribution.AttributedSource
terrasSource = Attribution.mkDOISource
  "Audrey Terras"
  "Fourier Analysis on Finite Groups and Applications"
  "Cambridge University Press"
  "1999"
  "10.1017/CBO9780511626265"
  "https://doi.org/10.1017/CBO9780511626265"
  Attribution.academicBookSource
  "finite-group Fourier and representation-theory provenance for the C3 character decomposition; not a source for Monster-specific character values"
  Attribution.publicAttribution

serreSource : Attribution.AttributedSource
serreSource = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Springer Graduate Texts in Mathematics 42"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicBookSource
  "finite-group character/regular-representation provenance; not Monster-specific data"
  Attribution.publicAttribution

barracloughWilsonAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt barracloughWilsonSource
terrasAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt terrasSource
serreAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt serreSource

------------------------------------------------------------------------
-- Role discipline / BIDI firewalls.
------------------------------------------------------------------------

data ExponentSplitCreatesSameRepresentation : Set where
data A000244CreatesStoneVonNeumannTheorem : Set where
data A005052CreatesMonsterCharacter : Set where
data Same65610DimensionIdentifiesFixedAndNontrivialPhases : Set where
data SameNineCreatesSameJCoarseObject : Set where

exponentSplitDoesNotIdentifyRepresentations : ExponentSplitCreatesSameRepresentation → ⊥
exponentSplitDoesNotIdentifyRepresentations ()

oeisDoesNotCreateStoneVonNeumann : A000244CreatesStoneVonNeumannTheorem → ⊥
oeisDoesNotCreateStoneVonNeumann ()

a005052DoesNotCreateMonsterCharacter : A005052CreatesMonsterCharacter → ⊥
a005052DoesNotCreateMonsterCharacter ()

sameDimensionDoesNotIdentifyPhaseTypes : Same65610DimensionIdentifiesFixedAndNontrivialPhases → ⊥
sameDimensionDoesNotIdentifyPhaseTypes ()

sameNumeralNineDoesNotIdentifyJCoarse : SameNineCreatesSameJCoarseObject → ⊥
sameNumeralNineDoesNotIdentifyJCoarse ()

record NineStratificationFrontier : Set where
  constructor nine-stratification-frontier
  field
    exponentNineAsOnePlusTwoPlusSixPaid : Bool
    a000244OneTwoSixNineCoordinatesPaid : Bool
    a005052TwoEightNineCoordinatesPaid : Bool
    phase65610As90Times729Paid : Bool
    bulk196830As3Times90Times729Paid : Bool
    outerThreeHasC3CharacterMeaningUpstream : Bool
    zetaAndInverseZeta729Times90MeaningUpstream : Bool
    fixedPhaseSameStoneVonNeumannMeaning : Bool
    residual53IsExcessTrivialMultiplicityUpstream : Bool
    oeisCreatesRepresentationMeaning : Bool
    nextResidual : String
open NineStratificationFrontier public

currentNineStratificationFrontier : NineStratificationFrontier
currentNineStratificationFrontier = nine-stratification-frontier
  true true true true true true true false true false
  "lift the actual selected 3B action onto literal fixed/zeta/inverse-zeta subspaces; use the 1+2+6 stratification only where those action receipts survive, then test whether Residual53 factors through any Base369/JCoarse-Fine pointed-completion map by an explicit intertwiner rather than by shared arithmetic"
