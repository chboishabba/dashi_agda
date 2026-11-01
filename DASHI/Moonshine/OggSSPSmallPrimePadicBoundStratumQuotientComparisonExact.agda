module DASHI.Moonshine.OggSSPSmallPrimePadicBoundStratumQuotientComparisonExact where

------------------------------------------------------------------------
-- CMT p-ADIC ORDER-BOUND vs LOCAL-STRATUM / QUOTIENT COMPARISON
--
-- This owner cross-compares independently defined observables.
--
-- p=2
--   CMT diagonal order bound      = 46
--   Duncan--Swisher baseline      = 36
--   bound excess                  = 10
--   Monster-local residual        = 10
--   rigidified canonical magnitude= 10
--
-- p=3
--   CMT diagonal order bound      = 21
--   Duncan--Swisher baseline      = 18
--   bound excess                  = 3
--   raw Deligne--Rapoport strata  = 3
--     {Frobenius branch, node, Verschiebung branch}
--   C2 orbit sectors              = 2
--     {node, branch pair}
--   Monster-local residual        = 2
--   unrigidified Hasse weight     = 2
--
-- Thus at p=3 the CMT bound excess agrees with the UNQUOTIENTED local
-- incidence rank, while the Monster residual agrees with the symmetry-quotient
-- rank.  This is an exact structural comparison, not a proof that taking the
-- C2 quotient is the analytic operation lowering the CMT bound by one.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.OggSSPSmallPrimePadicMoonshineOrderBoundComparisonExact as CMT
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3
import DASHI.Moonshine.OggSSPSmallCharacteristicWildCanonicalCoefficientComparisonExact as Canonical
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Rank observables.
------------------------------------------------------------------------

p2CMTBoundExcess : Nat
p2CMTBoundExcess = 10

p3CMTBoundExcess : Nat
p3CMTBoundExcess = 3

p3RawLocalStratumRank : Nat
p3RawLocalStratumRank = 3

p3LocalOrbitRank : Nat
p3LocalOrbitRank = 2

p2CMTBoundExcessIsTen :
  p2CMTBoundExcess ≡ 10
p2CMTBoundExcessIsTen = refl

p3CMTBoundExcessIsThree :
  p3CMTBoundExcess ≡ 3
p3CMTBoundExcessIsThree = refl

------------------------------------------------------------------------
-- 2. p=2 triple coincidence.
------------------------------------------------------------------------

p2CMTExcessMatchesLocalResidual :
  p2CMTBoundExcess ≡ Local.p2LocalCentralizerResidual
p2CMTExcessMatchesLocalResidual = refl

p2CMTExcessMatchesWildCanonicalMagnitude :
  p2CMTBoundExcess
  ≡ Canonical.p2RigidifiedCanonicalCoefficientMagnitude
p2CMTExcessMatchesWildCanonicalMagnitude = refl

p2CMTBoundReconstructsMonsterExponentNumerically :
  CMT.cmtDiagonalOrderBound CMT.pTwo
  ≡
  CMT.duncanSwisherBaseline CMT.pTwo + p2CMTBoundExcess
p2CMTBoundReconstructsMonsterExponentNumerically = refl

------------------------------------------------------------------------
-- 3. p=3 raw-stratum vs quotient-rank split.
------------------------------------------------------------------------

p3CMTExcessMatchesRawLocalStratumRank :
  p3CMTBoundExcess ≡ p3RawLocalStratumRank
p3CMTExcessMatchesRawLocalStratumRank = refl

p3MonsterResidualMatchesLocalOrbitRank :
  Local.p3LocalCentralizerResidual ≡ p3LocalOrbitRank
p3MonsterResidualMatchesLocalOrbitRank = refl

p3MonsterResidualMatchesHasseWeight :
  Local.p3LocalCentralizerResidual
  ≡ Canonical.p3UnrigidifiedHasseWeight
p3MonsterResidualMatchesHasseWeight = refl

p3RawStrataSplitAsOrbitRankPlusOne :
  p3RawLocalStratumRank ≡ p3LocalOrbitRank + 1
p3RawStrataSplitAsOrbitRankPlusOne = refl

p3CMTExcessIsNotMonsterResidual :
  p3CMTBoundExcess ≡ Local.p3LocalCentralizerResidual -> ⊥
p3CMTExcessIsNotMonsterResidual ()

------------------------------------------------------------------------
-- 4. Typed witness that the rank-3 carrier is the literal DR local carrier.
------------------------------------------------------------------------

data P3RawStratumWitness : Set where
  rawFrobeniusBranch :
    P3RawStratumWitness
  rawSupersingularNode :
    P3RawStratumWitness
  rawVerschiebungBranch :
    P3RawStratumWitness

rawWitnessToLocalStratum :
  P3RawStratumWitness ->
  P3.P3LocalStratum
rawWitnessToLocalStratum rawFrobeniusBranch =
  P3.frobeniusBranch
rawWitnessToLocalStratum rawSupersingularNode =
  P3.supersingularNode
rawWitnessToLocalStratum rawVerschiebungBranch =
  P3.verschiebungBranch

------------------------------------------------------------------------
-- 5. Mechanism firewalls.
------------------------------------------------------------------------

data CMTBoundCountsLocalStrataTheorem : Set where
data BranchExchangeQuotientAnalyticallyLowersCMTBoundByOne : Set where
data P2TripleCoincidenceCreatesValuationMechanism : Set where
data SameObservableUsedAtBothPrimes : Set where

cmtBoundNotPromotedToLocalStratumCountingTheorem :
  CMTBoundCountsLocalStrataTheorem -> ⊥
cmtBoundNotPromotedToLocalStratumCountingTheorem ()

branchExchangeQuotientNotYetAnalyticOneUnitCorrection :
  BranchExchangeQuotientAnalyticallyLowersCMTBoundByOne -> ⊥
branchExchangeQuotientNotYetAnalyticOneUnitCorrection ()

p2TripleCoincidenceDoesNotCreateValuationMechanism :
  P2TripleCoincidenceCreatesValuationMechanism -> ⊥
p2TripleCoincidenceDoesNotCreateValuationMechanism ()

sameObservableNotAssertedAcrossBothPrimes :
  SameObservableUsedAtBothPrimes -> ⊥
sameObservableNotAssertedAcrossBothPrimes ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record PadicBoundStratumQuotientComparisonBoundary : Set where
  constructor padic-bound-stratum-quotient-comparison-boundary
  field
    p2CMTExcessTen : Bool
    p2CMTExcessMatchesMonsterResidual : Bool
    p2CMTExcessMatchesWildCanonicalMagnitude : Bool
    p3CMTExcessThree : Bool
    p3CMTExcessMatchesThreeRawLocalStrata : Bool
    p3MonsterResidualMatchesTwoOrbitSectors : Bool
    p3MonsterResidualMatchesHasseWeight : Bool
    p3RawToOrbitRankDropsOne : Bool
    cmtBoundPromotedToStratumCountTheorem : Bool
    c2QuotientPromotedToAnalyticBoundCorrection : Bool
    oneUniformObservableAsserted : Bool
    attributionFirewallPreserved : Bool

canonicalPadicBoundStratumQuotientComparisonBoundary :
  PadicBoundStratumQuotientComparisonBoundary
canonicalPadicBoundStratumQuotientComparisonBoundary =
  padic-bound-stratum-quotient-comparison-boundary
    true true true true true true true true
    false false false true
