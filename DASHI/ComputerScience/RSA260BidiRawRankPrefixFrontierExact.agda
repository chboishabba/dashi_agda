module DASHI.ComputerScience.RSA260BidiRawRankPrefixFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact as Digest
import DASHI.ComputerScience.RSA260BidiRawModeRankResidualLocalizationExact as Local

------------------------------------------------------------------------
-- RAW-RANK PREFIX FRONTIER
--
-- After localizing the rotate3/affine7 factor-structure collision to the first
-- raw layer, widen the attack to the full ten-generator synthetic portfolio.
-- Ignore the two leading factor-mode ranks and retain only ranks of F_2,F_3,F_4.
--
-- Raw ranks alone still collide:
--
--   affine5  -> (7,7,7)
--   bitrev9  -> (7,7,7)
--
-- but adding the already-owned generator degree separates all ten current
-- receipt identities:
--
--   (degree, rank F_2, rank F_3, rank F_4).
--
-- This is a smaller current receipt observer than the previous
-- (degree, ranks F_0..F_4) prefix.  It remains a finite discriminator, not a
-- replay representation or production theorem.
------------------------------------------------------------------------

data RawRankTriple : Set where
  raw8-8-7 : RawRankTriple
  raw3-7-7 : RawRankTriple
  raw6-7-7 : RawRankTriple
  raw7-7-6 : RawRankTriple
  raw7-7-8 : RawRankTriple
  raw7-7-7 : RawRankTriple
  raw5-7-8 : RawRankTriple
  raw7-6-7 : RawRankTriple
  raw6-7-8 : RawRankTriple

data DegreeRawRankTriple : Set where
  d17-raw8-8-7 : DegreeRawRankTriple
  d17-raw3-7-7 : DegreeRawRankTriple
  d16-raw6-7-7 : DegreeRawRankTriple
  d17-raw7-7-6 : DegreeRawRankTriple
  d16-raw7-7-8 : DegreeRawRankTriple
  d17-raw7-7-7 : DegreeRawRankTriple
  d17-raw5-7-8 : DegreeRawRankTriple
  d16-raw7-6-7 : DegreeRawRankTriple
  d17-raw6-7-8 : DegreeRawRankTriple
  d16-raw7-7-7 : DegreeRawRankTriple

rawRankTripleObserve : Digest.AdapterWorld -> RawRankTriple
rawRankTripleObserve Digest.identityWorld = raw8-8-7
rawRankTripleObserve Digest.rotate1World = raw3-7-7
rawRankTripleObserve Digest.rotate2World = raw6-7-7
rawRankTripleObserve Digest.rotate3World = raw7-7-6
rawRankTripleObserve Digest.affine3World = raw7-7-8
rawRankTripleObserve Digest.affine5World = raw7-7-7
rawRankTripleObserve Digest.affine7World = raw5-7-8
rawRankTripleObserve Digest.affine9World = raw7-6-7
rawRankTripleObserve Digest.xor1World = raw6-7-8
rawRankTripleObserve Digest.bitrev9World = raw7-7-7

degreeRawRankTripleObserve : Digest.AdapterWorld -> DegreeRawRankTriple
degreeRawRankTripleObserve Digest.identityWorld = d17-raw8-8-7
degreeRawRankTripleObserve Digest.rotate1World = d17-raw3-7-7
degreeRawRankTripleObserve Digest.rotate2World = d16-raw6-7-7
degreeRawRankTripleObserve Digest.rotate3World = d17-raw7-7-6
degreeRawRankTripleObserve Digest.affine3World = d16-raw7-7-8
degreeRawRankTripleObserve Digest.affine5World = d17-raw7-7-7
degreeRawRankTripleObserve Digest.affine7World = d17-raw5-7-8
degreeRawRankTripleObserve Digest.affine9World = d16-raw7-6-7
degreeRawRankTripleObserve Digest.xor1World = d17-raw6-7-8
degreeRawRankTripleObserve Digest.bitrev9World = d16-raw7-7-7

------------------------------------------------------------------------
-- Raw ranks alone fail.
------------------------------------------------------------------------

RawRankTripleAdequacyDefect : Set₁
RawRankTripleAdequacyDefect =
  Query.QueryAdequacyDefect
    rawRankTripleObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity

rawRanksAloneCannotDetermineReceipt : RawRankTripleAdequacyDefect
rawRanksAloneCannotDetermineReceipt =
  Query.queryAdequacyDefect
    Digest.affine5World
    Digest.bitrev9World
    refl
    (λ ())

rawRanksAloneNotAdequate :
  Query.AdequateFor
    rawRankTripleObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity -> ⊥
rawRanksAloneNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    rawRanksAloneCannotDetermineReceipt

------------------------------------------------------------------------
-- Degree + three raw ranks separate the current portfolio.
------------------------------------------------------------------------

answerFromDegreeRawRanks : DegreeRawRankTriple -> Digest.GeneratorReceiptAnswer
answerFromDegreeRawRanks d17-raw8-8-7 = Digest.identityReceipt
answerFromDegreeRawRanks d17-raw3-7-7 = Digest.rotate1Receipt
answerFromDegreeRawRanks d16-raw6-7-7 = Digest.rotate2Receipt
answerFromDegreeRawRanks d17-raw7-7-6 = Digest.rotate3Receipt
answerFromDegreeRawRanks d16-raw7-7-8 = Digest.affine3Receipt
answerFromDegreeRawRanks d17-raw7-7-7 = Digest.affine5Receipt
answerFromDegreeRawRanks d17-raw5-7-8 = Digest.affine7Receipt
answerFromDegreeRawRanks d16-raw7-6-7 = Digest.affine9Receipt
answerFromDegreeRawRanks d17-raw6-7-8 = Digest.xor1Receipt
answerFromDegreeRawRanks d16-raw7-7-7 = Digest.bitrev9Receipt

degreeRawRankFactorisation :
  (world : Digest.AdapterWorld) ->
  Digest.generatorReceiptAnswer Digest.recoveredGeneratorReceiptIdentity world
  ≡ answerFromDegreeRawRanks (degreeRawRankTripleObserve world)
degreeRawRankFactorisation Digest.identityWorld = refl
degreeRawRankFactorisation Digest.rotate1World = refl
degreeRawRankFactorisation Digest.rotate2World = refl
degreeRawRankFactorisation Digest.rotate3World = refl
degreeRawRankFactorisation Digest.affine3World = refl
degreeRawRankFactorisation Digest.affine5World = refl
degreeRawRankFactorisation Digest.affine7World = refl
degreeRawRankFactorisation Digest.affine9World = refl
degreeRawRankFactorisation Digest.xor1World = refl
degreeRawRankFactorisation Digest.bitrev9World = refl

DegreeRawRankAdequacy : Set₁
DegreeRawRankAdequacy =
  Query.AdequateFor
    degreeRawRankTripleObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity

generatorReceiptFactorsThroughDegreeAndThreeRawRanks : DegreeRawRankAdequacy
generatorReceiptFactorsThroughDegreeAndThreeRawRanks =
  Query.factorsForQuery answerFromDegreeRawRanks degreeRawRankFactorisation

------------------------------------------------------------------------
-- Link back to the localized rotate3/affine7 witness.
------------------------------------------------------------------------

rotate3LocalizedFirstRawRank : Local.FirstRawLayerRank
rotate3LocalizedFirstRawRank = Local.firstRawLayerRank Local.rotate3RawWorld

affine7LocalizedFirstRawRank : Local.FirstRawLayerRank
affine7LocalizedFirstRawRank = Local.firstRawLayerRank Local.affine7RawWorld

------------------------------------------------------------------------
-- Boundary / next residual.
------------------------------------------------------------------------

record RawRankPrefixFrontierBoundary : Set where
  constructor raw-rank-prefix-frontier-boundary
  field
    localizedFirstRawRankInherited : Bool
    rawRanksF2F3F4IgnoreLeadingFactorRanks : Bool
    rawRankTripleAloneCollides : Bool
    affine5Bitrev9RawTripleCollisionPaid : Bool
    degreePlusThreeRawRanksSeparatesCurrentTenReceipts : Bool
    previousFiveLayerRankObserverCanBeReducedForReceiptConsumer : Bool
    degreePlusRawRanksReplayCoefficientMatrices : Bool
    degreePlusRawRanksAlgebraicallyIdentifyGenerator : Bool
    degreePlusRawRanksProductionSufficient : Bool
    degreePlusRawRanksGloballyMinimal : Bool
open RawRankPrefixFrontierBoundary public

canonicalRawRankPrefixFrontierBoundary : RawRankPrefixFrontierBoundary
canonicalRawRankPrefixFrontierBoundary =
  raw-rank-prefix-frontier-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

data RawRankPrefixResidual : Set where
  attackShorterDegreeRawRankPrefixes : RawRankPrefixResidual
  crossValidateDegreeRawRanksOnIndependentSeedPortfolio : RawRankPrefixResidual
  testConsumerTerminalAgainstNonReceiptConsumers : RawRankPrefixResidual
  retainReplayTailSeparately : RawRankPrefixResidual
  recurseIfNewCollisionAppears : RawRankPrefixResidual

firstRawRankPrefixResidual : RawRankPrefixResidual
firstRawRankPrefixResidual = attackShorterDegreeRawRankPrefixes
