module DASHI.Wikimedia.IbrahimE6CoxeterNinetyTypedCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Multiplicity
import DASHI.Wikimedia.IbrahimExceptionalOEISHypothesisTestExact as PriorTest

------------------------------------------------------------------------
-- TYPED CORRECTION: 12 + 78 = 90 THROUGH E6 COXETER DATA
--
-- The earlier OEIS hypothesis test correctly rejected 12 as a low-dimensional
-- E6/F4 IRREP dimension.  That was a family-specific negative result, not a
-- proof that 12 has no exceptional-Lie role.
--
-- For E6 the standard root-system data are
--
--   rank(E6) = 6,
--   Coxeter number h(E6) = 12,
--   |Phi(E6)| = rank * h = 72,
--   dim(e6) = |Phi| + rank = 78.
--
-- Hence the independently occurring Monster multiplicity arithmetic
--
--   90 = 12 + 78
--
-- has the typed exceptional numerical shadow
--
--   90 = h(E6) + dim(e6) = 12 + 72 + 6.
--
-- This is stronger than an arbitrary integer coincidence but weaker than an
-- identification of the literal Monster Fin 90 inertia carrier with an E6
-- object.  In particular, 12 is a Coxeter invariant here, NOT a 12-dimensional
-- E6 representation.
------------------------------------------------------------------------

eSixRank : Nat
eSixRank = 6

eSixCoxeterNumber : Nat
eSixCoxeterNumber = 12

eSixRootCount : Nat
eSixRootCount = 72

eSixLieDimension : Nat
eSixLieDimension = 78

monsterMultiplicityDimension : Nat
monsterMultiplicityDimension = 90

rootsAsRankTimesCoxeter : eSixRank * eSixCoxeterNumber ≡ eSixRootCount
rootsAsRankTimesCoxeter = refl

eSixDimensionAsRootsPlusRank : eSixRootCount + eSixRank ≡ eSixLieDimension
eSixDimensionAsRootsPlusRank = refl

eSixDimensionMatchesExistingExceptional :
  eSixLieDimension ≡ Exceptional.eSixDimension
eSixDimensionMatchesExistingExceptional = refl

ninetyAsCoxeterPlusE6Dimension :
  eSixCoxeterNumber + eSixLieDimension ≡ monsterMultiplicityDimension
ninetyAsCoxeterPlusE6Dimension = refl

ninetyAsCoxeterRootsRank :
  eSixCoxeterNumber + eSixRootCount + eSixRank ≡ monsterMultiplicityDimension
ninetyAsCoxeterRootsRank = refl

ninetyAsSixTimesTwelvePlusSixPlusTwelve :
  eSixRank * eSixCoxeterNumber + eSixRank + eSixCoxeterNumber
  ≡ monsterMultiplicityDimension
ninetyAsSixTimesTwelvePlusSixPlusTwelve = refl

------------------------------------------------------------------------
-- External typed coordinates.  A161409 is specifically the E6 Weyl-group
-- growth/Poincare sequence and records invariant degrees 2,5,6,8,9,12.
-- A129068 is retained only as a secondary exceptional Coxeter-number index.
------------------------------------------------------------------------

record E6CoxeterExternalCoordinates : Set where
  constructor e6-coxeter-external-coordinates
  field
    e6Qid : String
    rootSystemQid : String
    weylGroupQid : String
    coxeterGroupQid : String
    coxeterElementQid : String
    e6IrrepDimensionOEIS : String
    e6WeylGrowthOEIS : String
    exceptionalCoxeterOEIS : String
    e6MolienOEIS : String
    humphreysDOI : String
    sourceDewey : String
    deweyIsBibliographicCoordinateOnly : Bool
    qidOrOEISCreatesMonsterAction : Bool
open E6CoxeterExternalCoordinates public

canonicalE6CoxeterExternalCoordinates : E6CoxeterExternalCoordinates
canonicalE6CoxeterExternalCoordinates = e6-coxeter-external-coordinates
  "Q1054513"
  "Q534131"
  "Q768074"
  "Q7874246"
  "Q5179941"
  "A121737"
  "A161409"
  "A129068"
  "A008584"
  "10.1017/CBO9780511623646"
  "512.55"
  true
  false

------------------------------------------------------------------------
-- Primary/reference provenance.  This source establishes reflection/Coxeter/
-- Weyl theory; it does not identify the Monster multiplicity representation.
------------------------------------------------------------------------

humphreysSource : Attribution.AttributedSource
humphreysSource = Attribution.mkDOISource
  "James E. Humphreys"
  "Reflection Groups and Coxeter Groups"
  "Cambridge Studies in Advanced Mathematics 29, Cambridge University Press"
  "1990"
  "10.1017/CBO9780511623646"
  "https://doi.org/10.1017/CBO9780511623646"
  Attribution.academicBookSource
  "primary/reference provenance for Coxeter, Weyl and root-system structure; does not identify the Monster Fin 90 multiplicity action with E6"
  Attribution.publicAttribution

humphreysAttribution : AttributionSnowball.SourceRoleSnowballReceipt humphreysSource
humphreysAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt humphreysSource

------------------------------------------------------------------------
-- Preserve the earlier result at its correct scope.
------------------------------------------------------------------------

priorExceptionalHypothesisBoundary : PriorTest.ExceptionalOEISHypothesisFrontier
priorExceptionalHypothesisBoundary = PriorTest.currentExceptionalOEISHypothesisFrontier

actualMultiplicityBoundary : Multiplicity.MultiplicityInertiaTwelveSeventyEightBoundary
actualMultiplicityBoundary = Multiplicity.canonicalMultiplicityInertiaTwelveSeventyEightBoundary

------------------------------------------------------------------------
-- BIDI / WrongType boundaries.
------------------------------------------------------------------------

data CoxeterTwelveCreatesTwelveDimensionalIrrep : Set where
data NinetyEqualityIdentifiesMonsterFin90WithE6 : Set where
data E6WeylOEISCreatesMonsterIntertwiner : Set where
data DeweyOrQidCreatesExceptionalTheorem : Set where

coxeterTwelveIsNotTwelveDimensionalIrrep :
  CoxeterTwelveCreatesTwelveDimensionalIrrep → ⊥
coxeterTwelveIsNotTwelveDimensionalIrrep ()

ninetyDoesNotIdentifyCarriers :
  NinetyEqualityIdentifiesMonsterFin90WithE6 → ⊥
ninetyDoesNotIdentifyCarriers ()

oeisDoesNotCreateMonsterIntertwiner :
  E6WeylOEISCreatesMonsterIntertwiner → ⊥
oeisDoesNotCreateMonsterIntertwiner ()

deweyQidDoNotCreateTheorem : DeweyOrQidCreatesExceptionalTheorem → ⊥
deweyQidDoNotCreateTheorem ()

record E6CoxeterNinetyCorrectionFrontier : Set where
  constructor e6-coxeter-ninety-correction-frontier
  field
    priorTwelveIrrepNegativeResultRetained : Bool
    e6RankSixTyped : Bool
    e6CoxeterTwelveTyped : Bool
    e6RootCountSeventyTwoTyped : Bool
    e6DimensionSeventyEightTyped : Bool
    rootsEqualRankTimesCoxeterPaidLocally : Bool
    dimensionEqualsRootsPlusRankPaidLocally : Bool
    ninetyEqualsCoxeterPlusDimensionPaidLocally : Bool
    e6SpecificA161409CoordinatePaid : Bool
    qidAndDeweyProvenancePaid : Bool
    actualMonsterFin90SameActionE6RecognitionPaid : Bool
    kernelCertifiedHere : Bool
    nextResidual : String
open E6CoxeterNinetyCorrectionFrontier public

currentE6CoxeterNinetyCorrectionFrontier : E6CoxeterNinetyCorrectionFrontier
currentE6CoxeterNinetyCorrectionFrontier = e6-coxeter-ninety-correction-frontier
  true true true true true true true true true true
  false false
  "first pay the actual Monster Fin 90 inertia attachment and stable 12+78 split; then test the literal 78 block against the E6 adjoint action and ask whether the literal 12 block carries a Coxeter/invariant-degree role from that SAME E6 structure. Do not reinterpret 12 as an irrep and do not infer a direct-sum E6 module from 90=12+78 alone."
