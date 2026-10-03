module DASHI.Moonshine.Monster196883BabyBranchPrimeSupportExact where

------------------------------------------------------------------------
-- MONSTER 196883 -> 2.B BRANCHING PRIME-SUPPORT ATLAS
--
-- Attribution / provenance:
-- * JMD prompted the explicit comparison between the Monster 196883-degree
--   representation and the Baby Monster 4371-degree representation.
-- * The actual 2.B restriction benchmark consumed below is already sourced in
--   MonsterSubgroupBranchingBenchmarksExact from Conway / Wilson / BMW.
-- * The factorizations below are exact arithmetic observations only.
-- * Shared prime support does NOT explain the representation restriction and
--   does NOT construct the selected 2B Tate Q10 used elsewhere in DASHI.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_^_)

import DASHI.Biology.MonsterSubgroupBranchingBenchmarksExact as Branching
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Representation-degree prompt, with source boundary.
------------------------------------------------------------------------

record JMDMonsterBabyRepresentationPrompt : Set where
  constructor jmd-monster-baby-representation-prompt
  field
    creditedName : String
    monsterDegree : Nat
    babyMonsterDegree : Nat
    degreeComparisonPromptCredited : Bool
    actualComplexRepresentationsConstructedHere : Bool

canonicalJMDMonsterBabyRepresentationPrompt :
  JMDMonsterBabyRepresentationPrompt
canonicalJMDMonsterBabyRepresentationPrompt =
  jmd-monster-baby-representation-prompt
    "JMD"
    196883
    4371
    true
    false

------------------------------------------------------------------------
-- 2. Consume the genuine 2.B restriction benchmark already in the repo.
------------------------------------------------------------------------

babyMonsterBranchingExact :
  Branching.ambientDimension Branching.babyMonsterCentralizerBenchmark
  ≡ Branching.firstPiece Branching.babyMonsterCentralizerBenchmark
    + Branching.secondPiece Branching.babyMonsterCentralizerBenchmark
    + Branching.thirdPiece Branching.babyMonsterCentralizerBenchmark
    + Branching.fourthPiece Branching.babyMonsterCentralizerBenchmark
babyMonsterBranchingExact =
  Branching.babyMonsterRestrictionDimensionExact

babyMonsterBranchingLiteral :
  196883 ≡ 1 + 4371 + 96255 + 96256
babyMonsterBranchingLiteral = refl

------------------------------------------------------------------------
-- 3. Exact arithmetic prime-support atlas.
------------------------------------------------------------------------

monster196883OggFactorization :
  196883
  ≡ Lane.monsterPrimeLaneToNat Lane.p47
    * Lane.monsterPrimeLaneToNat Lane.p59
    * Lane.monsterPrimeLaneToNat Lane.p71
monster196883OggFactorization = refl

babyMonster4371Factorization :
  4371
  ≡ Lane.monsterPrimeLaneToNat Lane.p3
    * Lane.monsterPrimeLaneToNat Lane.p31
    * Lane.monsterPrimeLaneToNat Lane.p47
babyMonster4371Factorization = refl

branch96255Factorization :
  96255
  ≡ (Lane.monsterPrimeLaneToNat Lane.p3 ^ 3)
    * Lane.monsterPrimeLaneToNat Lane.p5
    * Lane.monsterPrimeLaneToNat Lane.p23
    * Lane.monsterPrimeLaneToNat Lane.p31
branch96255Factorization = refl

branch96256Factorization :
  96256
  ≡ (2 ^ 11) * Lane.monsterPrimeLaneToNat Lane.p47
branch96256Factorization = refl

reducedTwoLocalResidual299Factorization :
  299
  ≡ Lane.monsterPrimeLaneToNat Lane.p13
    * Lane.monsterPrimeLaneToNat Lane.p23
reducedTwoLocalResidual299Factorization = refl

branchPrimeSupportAtlasCloses :
  Lane.monsterPrimeLaneToNat Lane.p47
    * Lane.monsterPrimeLaneToNat Lane.p59
    * Lane.monsterPrimeLaneToNat Lane.p71
  ≡ 1
    + (Lane.monsterPrimeLaneToNat Lane.p3
       * Lane.monsterPrimeLaneToNat Lane.p31
       * Lane.monsterPrimeLaneToNat Lane.p47)
    + ((Lane.monsterPrimeLaneToNat Lane.p3 ^ 3)
       * Lane.monsterPrimeLaneToNat Lane.p5
       * Lane.monsterPrimeLaneToNat Lane.p23
       * Lane.monsterPrimeLaneToNat Lane.p31)
    + ((2 ^ 11) * Lane.monsterPrimeLaneToNat Lane.p47)
branchPrimeSupportAtlasCloses = refl

------------------------------------------------------------------------
-- 4. Typed overlap observations.
------------------------------------------------------------------------

babyBranchSharesP47WithMonsterProduct :
  Lane.monsterPrimeLaneToNat Lane.p47 ≡ 47
babyBranchSharesP47WithMonsterProduct = refl

babyBranchContainsP31Lane :
  Lane.monsterPrimeLaneToNat Lane.p31 ≡ 31
babyBranchContainsP31Lane = refl

monsterProductContainsP59Lane :
  Lane.monsterPrimeLaneToNat Lane.p59 ≡ 59
monsterProductContainsP59Lane = refl

monsterProductContainsP71Lane :
  Lane.monsterPrimeLaneToNat Lane.p71 ≡ 71
monsterProductContainsP71Lane = refl

------------------------------------------------------------------------
-- 5. Promotion firewalls.
------------------------------------------------------------------------

data PrimeSupportExplainsRepresentationBranching : Set where

data BabyMonsterBranchSelectsTwoBTateQ10 : Set where

data Factor4371ExplainsBabyMonsterRepresentation : Set where

branchPrimeSupportDoesNotExplainBranching :
  PrimeSupportExplainsRepresentationBranching → ⊥
branchPrimeSupportDoesNotExplainBranching ()

babyMonsterBranchDoesNotSelectTwoBTateQ10 :
  BabyMonsterBranchSelectsTwoBTateQ10 → ⊥
babyMonsterBranchDoesNotSelectTwoBTateQ10 ()

factorizationDoesNotExplain4371Representation :
  Factor4371ExplainsBabyMonsterRepresentation → ⊥
factorizationDoesNotExplain4371Representation ()

record BabyBranchPrimeSupportBoundary : Set where
  constructor baby-branch-prime-support-boundary
  field
    jmdDegreePromptCredited : Bool
    sourced2BRestrictionConsumed : Bool
    monster196883FactorizationPaid : Bool
    baby4371FactorizationPaid : Bool
    branch96255FactorizationPaid : Bool
    branch96256FactorizationPaid : Bool
    residual299FactorizationPaid : Bool
    primeSupportExplainsRestriction : Bool
    babyBranchIdentifiedWithTwoBTateQ10 : Bool

canonicalBabyBranchPrimeSupportBoundary :
  BabyBranchPrimeSupportBoundary
canonicalBabyBranchPrimeSupportBoundary =
  baby-branch-prime-support-boundary
    true true true true true true true false false
