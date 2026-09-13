module DASHI.Wikimedia.IbrahimMonster3BTwelveSeventyEightExceptionalOEISSourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as ActualSplit
import DASHI.Moonshine.Base369Monster3BSeventyEightExceptionalE6BidiExact as E6Candidate
import DASHI.Wikimedia.IbrahimMonster3BReplayStatusMultiplicitySplitSnowballExact as Replay

------------------------------------------------------------------------
-- 12 + 78 = 90 / EXCEPTIONAL E6-F4-ALBERT SNOWBALL
--
-- The live Monster 3B lane only obtains a literal 12+78 block decomposition
-- after the same actual inertia action has been attached to Fin 90.  Separately
-- the exceptional-algebra lane owns the exact dimensions
--
--   dim E6 = 78 = 52 + 26,
--   dim F4 = 52 = 26 + 26,
--   dim Albert = 27 = 1 + 26,
--   53 = 1 + 26 + 26,
--   54 = 27 + 27.
--
-- This file joins those exact arithmetic/source/OEIS/QID coordinates while
-- keeping the actual E6 recognition interface uninhabited until a same-action
-- intertwiner is supplied.
------------------------------------------------------------------------

twelvePlusSeventyEightIsNinety : 12 + 78 ≡ 90
twelvePlusSeventyEightIsNinety = refl

seventyEightIsFiftyTwoPlusTwentySix : 78 ≡ 52 + 26
seventyEightIsFiftyTwoPlusTwentySix = Exceptional.eSixIsF4PlusTracelessAlbert

fiftyTwoIsTwoTwentySixes : 52 ≡ 2 * 26
fiftyTwoIsTwoTwentySixes = Exceptional.fFourIsTwoTracelessAlbertDimensions

twentySevenIsOnePlusTwentySix : 27 ≡ 1 + 26
twentySevenIsOnePlusTwentySix = Exceptional.albertSplitsScalarPlusTraceless

fiftyThreeIsOnePlusTwoTwentySixes : 53 ≡ 1 + (26 + 26)
fiftyThreeIsOnePlusTwoTwentySixes = Exceptional.reducedAlbertPairIsOnePlusTwoTraceless

fiftyFourIsTwoTwentySevens : 54 ≡ 27 + 27
fiftyFourIsTwoTwentySevens = Exceptional.albertPairIsTwoAlbert

ninetyAsTwelvePlusE6Dimension : 90 ≡ 12 + Exceptional.eSixDimension
ninetyAsTwelvePlusE6Dimension = refl

monsterReplayMultiplicitySplit = Replay.currentReplayMultiplicityFrontier

actualSameActionSplitBoundary :
  ActualSplit.MultiplicityInertiaTwelveSeventyEightBoundary
actualSameActionSplitBoundary =
  ActualSplit.canonicalMultiplicityInertiaTwelveSeventyEightBoundary

exceptional78Boundary : E6Candidate.SeventyEightExceptionalBoundary
exceptional78Boundary = E6Candidate.canonicalSeventyEightExceptionalBoundary

------------------------------------------------------------------------
-- External identities / sequence coordinates.
------------------------------------------------------------------------

record ExceptionalExternalCoordinates : Set where
  constructor exceptional-external-coordinates
  field
    e6Qid : String
    f4Qid : String
    jordanAlgebraQid : String
    lieGroupQid : String
    simpleLieDimensionOEIS : String
    complexSimpleLieDimensionOEIS : String
    f4IrrepDimensionOEIS : String
    monsterMultiplicityOEIS : String
    e6Dimension78PaidExternally : Bool
    f4TwentySixFiftyTwoPaidExternally : Bool
    oeisIdentifiesMonster78BlockAsE6 : Bool
    qidIdentifiesMonster78BlockAsE6 : Bool
open ExceptionalExternalCoordinates public

canonicalExceptionalExternalCoordinates : ExceptionalExternalCoordinates
canonicalExceptionalExternalCoordinates = exceptional-external-coordinates
  "Q1054513" "Q869077" "Q649977" "Q622679"
  "A001066" "A263005" "A121738" "A005052"
  true true false false

------------------------------------------------------------------------
-- Primary-source provenance.
------------------------------------------------------------------------

titsExceptionalConstructionSource : Attribution.AttributedSource
titsExceptionalConstructionSource = Attribution.mkDOISource
  "Jacques Tits"
  "Algèbres alternatives, algèbres de Jordan et algèbres de Lie exceptionnelles. I. Construction"
  "Indagationes Mathematicae 28, 223-237"
  "1966"
  "10.1016/S1385-7258(66)50028-2"
  "https://doi.org/10.1016/S1385-7258(66)50028-2"
  Attribution.academicArticleSource
  "primary exceptional Lie/Jordan construction provenance; not a source for the Monster 3B 12+78 restriction output or Base369 identification"
  Attribution.publicAttribution

barracloughWilsonSource : Attribution.AttributedSource
barracloughWilsonSource = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "Monster subgroup/character-table provenance for the actual 12+78 multiplicity split; not an exceptional-E6 identification"
  Attribution.publicAttribution

titsAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt titsExceptionalConstructionSource

barracloughWilsonAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt barracloughWilsonSource

------------------------------------------------------------------------
-- BIDI boundaries.
------------------------------------------------------------------------

data Same78DimensionCreatesE6Representation : Set where
data Same26DimensionCreatesAlbertRepresentation : Set where
data TwelvePlusE6DimensionCreatesExceptionalDecomposition : Set where
data OEISLieDimensionCreatesMonsterIntertwiner : Set where

same78DoesNotCreateE6Representation : Same78DimensionCreatesE6Representation → ⊥
same78DoesNotCreateE6Representation ()

same26DoesNotCreateAlbertRepresentation : Same26DimensionCreatesAlbertRepresentation → ⊥
same26DoesNotCreateAlbertRepresentation ()

twelvePlus78DoesNotCreateExceptionalDecomposition :
  TwelvePlusE6DimensionCreatesExceptionalDecomposition → ⊥
twelvePlus78DoesNotCreateExceptionalDecomposition ()

oeisDoesNotCreateMonsterIntertwiner : OEISLieDimensionCreatesMonsterIntertwiner → ⊥
oeisDoesNotCreateMonsterIntertwiner ()

record ExceptionalSnowballFrontier : Set where
  constructor exceptional-snowball-frontier
  field
    twelvePlusSeventyEightArithmeticPaid : Bool
    seventyEightAsF4Plus26Paid : Bool
    fiftyThreeAndFiftyFourExceptionalArithmeticPaid : Bool
    e6F4JordanQidsPaid : Bool
    lieDimensionOEISCoordinatesPaid : Bool
    primaryTitsSourcePaid : Bool
    actualMonsterFin90SameActionSplitPaid : Bool
    actual78ToE6IntertwinerPaid : Bool
    actual53ToAlbertResidualIntertwinerPaid : Bool
    nextResidual : String
open ExceptionalSnowballFrontier public

currentExceptionalSnowballFrontier : ExceptionalSnowballFrontier
currentExceptionalSnowballFrontier = exceptional-snowball-frontier
  true true true true true true
  false false false
  "first recover the actual Monster multiplicity inertia action and its 12+78 stable split; only then test the 78 block against E6 and the 53 residual against 1+26+26 by explicit same-action intertwiners. Treat A001066/A263005/A121738 and Q1054513/Q869077/Q649977 as discovery/provenance coordinates, not representation authority."
