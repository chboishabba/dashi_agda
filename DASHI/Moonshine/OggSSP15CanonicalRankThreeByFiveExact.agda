module DASHI.Moonshine.OggSSP15CanonicalRankThreeByFiveExact where

------------------------------------------------------------------------
-- CANONICAL OGG RANK -> 5 x 3 SSP15 PRESENTATION
--
-- DASHI CONTRIBUTION
--
-- The existing chosen Ogg/internal mapping groups the canonical increasing
-- Ogg-prime list in consecutive triples.  This file makes that fact explicit.
--
-- Rank15 is the ordinal carrier of the repository's canonical Ogg lane list:
--
--   0:p2, 1:p3, 2:p5, ..., 14:p71.
--
-- The rank decomposes exactly as
--
--   rank = 3 * block5 + phaseResidue3,
--
-- and the existing primeToInternal map factors through this rank chart.
--
-- This removes "arbitrary 15-case enumeration" as an implementation concern:
-- the chart is reproducible from the repository's canonical Ogg ordering.
--
-- It still does NOT prove that block5/phase3 are intrinsic modular or
-- supersingular arithmetic invariants, nor that they are a local formula of
-- the exact nonary address (q,r).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Chosen
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion

------------------------------------------------------------------------
-- 1. Canonical 15-position rank carrier.
------------------------------------------------------------------------

data Rank15 : Set where
  r00 r01 r02 r03 r04 r05 r06 r07 : Rank15
  r08 r09 r10 r11 r12 r13 r14 : Rank15

canonicalRankOrder : List Rank15
canonicalRankOrder =
  r00 ∷ r01 ∷ r02 ∷ r03 ∷ r04
  ∷ r05 ∷ r06 ∷ r07 ∷ r08 ∷ r09
  ∷ r10 ∷ r11 ∷ r12 ∷ r13 ∷ r14 ∷ []

rankToPrime : Rank15 -> Lane.MonsterPrimeLane
rankToPrime r00 = Lane.p2
rankToPrime r01 = Lane.p3
rankToPrime r02 = Lane.p5
rankToPrime r03 = Lane.p7
rankToPrime r04 = Lane.p11
rankToPrime r05 = Lane.p13
rankToPrime r06 = Lane.p17
rankToPrime r07 = Lane.p19
rankToPrime r08 = Lane.p23
rankToPrime r09 = Lane.p29
rankToPrime r10 = Lane.p31
rankToPrime r11 = Lane.p41
rankToPrime r12 = Lane.p47
rankToPrime r13 = Lane.p59
rankToPrime r14 = Lane.p71

primeToRank : Lane.MonsterPrimeLane -> Rank15
primeToRank Lane.p2 = r00
primeToRank Lane.p3 = r01
primeToRank Lane.p5 = r02
primeToRank Lane.p7 = r03
primeToRank Lane.p11 = r04
primeToRank Lane.p13 = r05
primeToRank Lane.p17 = r06
primeToRank Lane.p19 = r07
primeToRank Lane.p23 = r08
primeToRank Lane.p29 = r09
primeToRank Lane.p31 = r10
primeToRank Lane.p41 = r11
primeToRank Lane.p47 = r12
primeToRank Lane.p59 = r13
primeToRank Lane.p71 = r14

primeRankRoundTrip :
  (prime : Lane.MonsterPrimeLane) ->
  rankToPrime (primeToRank prime) ≡ prime
primeRankRoundTrip Lane.p2 = refl
primeRankRoundTrip Lane.p3 = refl
primeRankRoundTrip Lane.p5 = refl
primeRankRoundTrip Lane.p7 = refl
primeRankRoundTrip Lane.p11 = refl
primeRankRoundTrip Lane.p13 = refl
primeRankRoundTrip Lane.p17 = refl
primeRankRoundTrip Lane.p19 = refl
primeRankRoundTrip Lane.p23 = refl
primeRankRoundTrip Lane.p29 = refl
primeRankRoundTrip Lane.p31 = refl
primeRankRoundTrip Lane.p41 = refl
primeRankRoundTrip Lane.p47 = refl
primeRankRoundTrip Lane.p59 = refl
primeRankRoundTrip Lane.p71 = refl

rankPrimeRoundTrip :
  (rank : Rank15) ->
  primeToRank (rankToPrime rank) ≡ rank
rankPrimeRoundTrip r00 = refl
rankPrimeRoundTrip r01 = refl
rankPrimeRoundTrip r02 = refl
rankPrimeRoundTrip r03 = refl
rankPrimeRoundTrip r04 = refl
rankPrimeRoundTrip r05 = refl
rankPrimeRoundTrip r06 = refl
rankPrimeRoundTrip r07 = refl
rankPrimeRoundTrip r08 = refl
rankPrimeRoundTrip r09 = refl
rankPrimeRoundTrip r10 = refl
rankPrimeRoundTrip r11 = refl
rankPrimeRoundTrip r12 = refl
rankPrimeRoundTrip r13 = refl
rankPrimeRoundTrip r14 = refl

canonicalRankOrderMapsToCanonicalOggList :
  map rankToPrime canonicalRankOrder
  ≡ Lane.canonicalMonsterPrimeLane
canonicalRankOrderMapsToCanonicalOggList = refl

------------------------------------------------------------------------
-- 2. Rank arithmetic: 15 = five blocks x three phase residues.
------------------------------------------------------------------------

rankNat : Rank15 -> Nat
rankNat r00 = 0
rankNat r01 = 1
rankNat r02 = 2
rankNat r03 = 3
rankNat r04 = 4
rankNat r05 = 5
rankNat r06 = 6
rankNat r07 = 7
rankNat r08 = 8
rankNat r09 = 9
rankNat r10 = 10
rankNat r11 = 11
rankNat r12 = 12
rankNat r13 = 13
rankNat r14 = 14

block5Nat : Rank15 -> Nat
block5Nat r00 = 0
block5Nat r01 = 0
block5Nat r02 = 0
block5Nat r03 = 1
block5Nat r04 = 1
block5Nat r05 = 1
block5Nat r06 = 2
block5Nat r07 = 2
block5Nat r08 = 2
block5Nat r09 = 3
block5Nat r10 = 3
block5Nat r11 = 3
block5Nat r12 = 4
block5Nat r13 = 4
block5Nat r14 = 4

phaseResidueNat : Rank15 -> Nat
phaseResidueNat r00 = 0
phaseResidueNat r01 = 1
phaseResidueNat r02 = 2
phaseResidueNat r03 = 0
phaseResidueNat r04 = 1
phaseResidueNat r05 = 2
phaseResidueNat r06 = 0
phaseResidueNat r07 = 1
phaseResidueNat r08 = 2
phaseResidueNat r09 = 0
phaseResidueNat r10 = 1
phaseResidueNat r11 = 2
phaseResidueNat r12 = 0
phaseResidueNat r13 = 1
phaseResidueNat r14 = 2

rankThreeByFiveArithmetic :
  (rank : Rank15) ->
  rankNat rank ≡ 3 * block5Nat rank + phaseResidueNat rank
rankThreeByFiveArithmetic r00 = refl
rankThreeByFiveArithmetic r01 = refl
rankThreeByFiveArithmetic r02 = refl
rankThreeByFiveArithmetic r03 = refl
rankThreeByFiveArithmetic r04 = refl
rankThreeByFiveArithmetic r05 = refl
rankThreeByFiveArithmetic r06 = refl
rankThreeByFiveArithmetic r07 = refl
rankThreeByFiveArithmetic r08 = refl
rankThreeByFiveArithmetic r09 = refl
rankThreeByFiveArithmetic r10 = refl
rankThreeByFiveArithmetic r11 = refl
rankThreeByFiveArithmetic r12 = refl
rankThreeByFiveArithmetic r13 = refl
rankThreeByFiveArithmetic r14 = refl

------------------------------------------------------------------------
-- 3. Rank-derived internal SSP15 presentation.
------------------------------------------------------------------------

rankMode : Rank15 -> Completion.ComplementMode5
rankMode r00 = Completion.mode09
rankMode r01 = Completion.mode09
rankMode r02 = Completion.mode09
rankMode r03 = Completion.mode18
rankMode r04 = Completion.mode18
rankMode r05 = Completion.mode18
rankMode r06 = Completion.mode27
rankMode r07 = Completion.mode27
rankMode r08 = Completion.mode27
rankMode r09 = Completion.mode36
rankMode r10 = Completion.mode36
rankMode r11 = Completion.mode36
rankMode r12 = Completion.mode45
rankMode r13 = Completion.mode45
rankMode r14 = Completion.mode45

rankPhase : Rank15 -> Harmonic.BalancedTrit
rankPhase r00 = Harmonic.negativeTrit
rankPhase r01 = Harmonic.zeroTrit
rankPhase r02 = Harmonic.positiveTrit
rankPhase r03 = Harmonic.negativeTrit
rankPhase r04 = Harmonic.zeroTrit
rankPhase r05 = Harmonic.positiveTrit
rankPhase r06 = Harmonic.negativeTrit
rankPhase r07 = Harmonic.zeroTrit
rankPhase r08 = Harmonic.positiveTrit
rankPhase r09 = Harmonic.negativeTrit
rankPhase r10 = Harmonic.zeroTrit
rankPhase r11 = Harmonic.positiveTrit
rankPhase r12 = Harmonic.negativeTrit
rankPhase r13 = Harmonic.zeroTrit
rankPhase r14 = Harmonic.positiveTrit

rankToInternal :
  Rank15 ->
  Internal.SSP15InternalLane
rankToInternal rank =
  rankMode rank , rankPhase rank

existingPrimeToInternalFactorsThroughCanonicalRank :
  (prime : Lane.MonsterPrimeLane) ->
  Chosen.primeToInternal prime
  ≡ rankToInternal (primeToRank prime)
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p2 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p3 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p5 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p7 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p11 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p13 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p17 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p19 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p23 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p29 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p31 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p41 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p47 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p59 = refl
existingPrimeToInternalFactorsThroughCanonicalRank Lane.p71 = refl

------------------------------------------------------------------------
-- 4. Phase/block numeric decoders.
------------------------------------------------------------------------

modeBlockNat : Completion.ComplementMode5 -> Nat
modeBlockNat Completion.mode09 = 0
modeBlockNat Completion.mode18 = 1
modeBlockNat Completion.mode27 = 2
modeBlockNat Completion.mode36 = 3
modeBlockNat Completion.mode45 = 4

phaseToResidue : Harmonic.BalancedTrit -> Nat
phaseToResidue Harmonic.negativeTrit = 0
phaseToResidue Harmonic.zeroTrit = 1
phaseToResidue Harmonic.positiveTrit = 2

rankModeBlockAgrees :
  (rank : Rank15) ->
  modeBlockNat (rankMode rank) ≡ block5Nat rank
rankModeBlockAgrees r00 = refl
rankModeBlockAgrees r01 = refl
rankModeBlockAgrees r02 = refl
rankModeBlockAgrees r03 = refl
rankModeBlockAgrees r04 = refl
rankModeBlockAgrees r05 = refl
rankModeBlockAgrees r06 = refl
rankModeBlockAgrees r07 = refl
rankModeBlockAgrees r08 = refl
rankModeBlockAgrees r09 = refl
rankModeBlockAgrees r10 = refl
rankModeBlockAgrees r11 = refl
rankModeBlockAgrees r12 = refl
rankModeBlockAgrees r13 = refl
rankModeBlockAgrees r14 = refl

rankPhaseResidueAgrees :
  (rank : Rank15) ->
  phaseToResidue (rankPhase rank) ≡ phaseResidueNat rank
rankPhaseResidueAgrees r00 = refl
rankPhaseResidueAgrees r01 = refl
rankPhaseResidueAgrees r02 = refl
rankPhaseResidueAgrees r03 = refl
rankPhaseResidueAgrees r04 = refl
rankPhaseResidueAgrees r05 = refl
rankPhaseResidueAgrees r06 = refl
rankPhaseResidueAgrees r07 = refl
rankPhaseResidueAgrees r08 = refl
rankPhaseResidueAgrees r09 = refl
rankPhaseResidueAgrees r10 = refl
rankPhaseResidueAgrees r11 = refl
rankPhaseResidueAgrees r12 = refl
rankPhaseResidueAgrees r13 = refl
rankPhaseResidueAgrees r14 = refl

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data CanonicalRankChartIsIntrinsicModularInvariant : Set where
data CanonicalRankChartIsLocalNonaryAddressFormula : Set where
data PrimeMagnitudeOrderCreatesGroupAction : Set where

rankChartNotPromotedToIntrinsicModularInvariant :
  CanonicalRankChartIsIntrinsicModularInvariant -> ⊥
rankChartNotPromotedToIntrinsicModularInvariant ()

rankChartNotPromotedToLocalAddressFormula :
  CanonicalRankChartIsLocalNonaryAddressFormula -> ⊥
rankChartNotPromotedToLocalAddressFormula ()

primeOrderNotPromotedToGroupAction :
  PrimeMagnitudeOrderCreatesGroupAction -> ⊥
primeOrderNotPromotedToGroupAction ()

record OggSSP15CanonicalRankThreeByFiveBoundary : Set where
  constructor ogg-ssp15-canonical-rank-three-by-five-boundary
  field
    rankPrimeBidiPaid : Bool
    rankOrderMatchesCanonicalOggList : Bool
    rankSplitsAsThreeTimesBlockPlusResidue : Bool
    existingPrimeInternalFactorsThroughRank : Bool
    fiveBlocksOfThreeRecovered : Bool
    canonicalRelativeToRepositoryOrder : Bool
    intrinsicModularInvariantClaimed : Bool
    localNonaryAddressFormulaClaimed : Bool

canonicalOggSSP15CanonicalRankThreeByFiveBoundary :
  OggSSP15CanonicalRankThreeByFiveBoundary
canonicalOggSSP15CanonicalRankThreeByFiveBoundary =
  ogg-ssp15-canonical-rank-three-by-five-boundary
    true true true true true true false false
