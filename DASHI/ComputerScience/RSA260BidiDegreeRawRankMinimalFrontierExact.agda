module DASHI.ComputerScience.RSA260BidiDegreeRawRankMinimalFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact as Digest
import DASHI.ComputerScience.RSA260BidiRawRankPrefixFrontierExact as Raw

------------------------------------------------------------------------
-- FIRST CHECKED CONTIGUOUS RAW-RANK PREFIX AFTER DEGREE
--
-- The previous owner showed that (degree, rank F2, rank F3, rank F4)
-- separates the ten current synthetic receipt identities.  Here we pay the
-- shorter-prefix attacks explicitly:
--
--   (degree, rank F2)          still collides;
--   (degree, rank F2, rank F3) still collides;
--   (degree, rank F2, rank F3, rank F4) separates the current ten.
--
-- Therefore three raw ranks are the first SEPARATING CHECKED contiguous raw
-- prefix starting at F2 once degree is retained.  This is not a theorem of
-- global minimality over arbitrary observers.
------------------------------------------------------------------------

data DegreeRawRankOne : Set where
  d17-r8 : DegreeRawRankOne
  d17-r3 : DegreeRawRankOne
  d16-r6 : DegreeRawRankOne
  d17-r7 : DegreeRawRankOne
  d16-r7 : DegreeRawRankOne
  d17-r5 : DegreeRawRankOne
  d17-r6 : DegreeRawRankOne

data DegreeRawRankPair : Set where
  d17-r8-8 : DegreeRawRankPair
  d17-r3-7 : DegreeRawRankPair
  d16-r6-7 : DegreeRawRankPair
  d17-r7-7 : DegreeRawRankPair
  d16-r7-7 : DegreeRawRankPair
  d17-r5-7 : DegreeRawRankPair
  d16-r7-6 : DegreeRawRankPair
  d17-r6-7 : DegreeRawRankPair

degreeRawRankOneObserve : Digest.AdapterWorld → DegreeRawRankOne
degreeRawRankOneObserve Digest.identityWorld = d17-r8
degreeRawRankOneObserve Digest.rotate1World = d17-r3
degreeRawRankOneObserve Digest.rotate2World = d16-r6
degreeRawRankOneObserve Digest.rotate3World = d17-r7
degreeRawRankOneObserve Digest.affine3World = d16-r7
degreeRawRankOneObserve Digest.affine5World = d17-r7
degreeRawRankOneObserve Digest.affine7World = d17-r5
degreeRawRankOneObserve Digest.affine9World = d16-r7
degreeRawRankOneObserve Digest.xor1World = d17-r6
degreeRawRankOneObserve Digest.bitrev9World = d16-r7

degreeRawRankPairObserve : Digest.AdapterWorld → DegreeRawRankPair
degreeRawRankPairObserve Digest.identityWorld = d17-r8-8
degreeRawRankPairObserve Digest.rotate1World = d17-r3-7
degreeRawRankPairObserve Digest.rotate2World = d16-r6-7
degreeRawRankPairObserve Digest.rotate3World = d17-r7-7
degreeRawRankPairObserve Digest.affine3World = d16-r7-7
degreeRawRankPairObserve Digest.affine5World = d17-r7-7
degreeRawRankPairObserve Digest.affine7World = d17-r5-7
degreeRawRankPairObserve Digest.affine9World = d16-r7-6
degreeRawRankPairObserve Digest.xor1World = d17-r6-7
degreeRawRankPairObserve Digest.bitrev9World = d16-r7-7

DegreeRawRankOneDefect : Set₁
DegreeRawRankOneDefect =
  Query.QueryAdequacyDefect
    degreeRawRankOneObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity

degreePlusOneRawRankStillCollides : DegreeRawRankOneDefect
degreePlusOneRawRankStillCollides =
  Query.queryAdequacyDefect
    Digest.rotate3World
    Digest.affine5World
    refl
    (λ ())

DegreeRawRankPairDefect : Set₁
DegreeRawRankPairDefect =
  Query.QueryAdequacyDefect
    degreeRawRankPairObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity

degreePlusTwoRawRanksStillCollide : DegreeRawRankPairDefect
degreePlusTwoRawRanksStillCollide =
  Query.queryAdequacyDefect
    Digest.rotate3World
    Digest.affine5World
    refl
    (λ ())

degreePlusOneRawRankNotAdequate :
  Query.AdequateFor
    degreeRawRankOneObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity → ⊥
degreePlusOneRawRankNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation degreePlusOneRawRankStillCollides

degreePlusTwoRawRanksNotAdequate :
  Query.AdequateFor
    degreeRawRankPairObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity → ⊥
degreePlusTwoRawRanksNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation degreePlusTwoRawRanksStillCollide

degreePlusThreeRawRanksAdequate : Raw.DegreeRawRankAdequacy
degreePlusThreeRawRanksAdequate =
  Raw.generatorReceiptFactorsThroughDegreeAndThreeRawRanks

record DegreeRawRankMinimalFrontierBoundary : Set where
  constructor degree-raw-rank-minimal-frontier-boundary
  field
    degreePlusOneRawRankCollisionPaid : Bool
    degreePlusTwoRawRanksCollisionPaid : Bool
    degreePlusThreeRawRanksSeparateCurrentTen : Bool
    threeRawRanksFirstSeparatingCheckedContiguousPrefixFromF2 : Bool
    statementIsGlobalMinimalityOverAllObservers : Bool
    statementIsCoefficientReplayTheorem : Bool
    statementIsProductionRSA260Sufficiency : Bool
open DegreeRawRankMinimalFrontierBoundary public

canonicalDegreeRawRankMinimalFrontierBoundary : DegreeRawRankMinimalFrontierBoundary
canonicalDegreeRawRankMinimalFrontierBoundary =
  degree-raw-rank-minimal-frontier-boundary
    true true true true false false false

data DegreeRawRankMinimalFrontierResidual : Set where
  crossValidateDegreeRawRankTripleOnIndependentSeedPortfolio : DegreeRawRankMinimalFrontierResidual
  attackNonContiguousSubsetsOfCurrentRawRanks : DegreeRawRankMinimalFrontierResidual
  testDifferentConsumersAgainstSameObserver : DegreeRawRankMinimalFrontierResidual
  retainExactReplayTailSeparately : DegreeRawRankMinimalFrontierResidual

firstDegreeRawRankMinimalFrontierResidual : DegreeRawRankMinimalFrontierResidual
firstDegreeRawRankMinimalFrontierResidual =
  crossValidateDegreeRawRankTripleOnIndependentSeedPortfolio
