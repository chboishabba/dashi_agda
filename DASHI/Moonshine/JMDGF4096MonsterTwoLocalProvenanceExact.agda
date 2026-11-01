module DASHI.Moonshine.JMDGF4096MonsterTwoLocalProvenanceExact where

------------------------------------------------------------------------
-- 4096 DUAL-ROLE PROVENANCE HUB
--
-- JMD's GF(4096)=GF(2^12) Frobenius diagrams prompted this comparison.
-- Independently, the existing sourced Monster 2-local branching benchmark
-- contains a genuine 4096 * 24 tensor factor.
--
-- The shared scalar is exact.  The meanings are deliberately not identified:
-- a finite-field cardinality does not construct the Monster 2-local module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_^_)

import DASHI.Biology.MonsterSubgroupBranchingBenchmarksExact as Branching
import DASHI.Moonshine.JMDFrobeniusThreeTateTraceCrossPollinationExact as JMD

------------------------------------------------------------------------
-- 1. Finite-field cardinality role.
------------------------------------------------------------------------

gf4096CardinalityRole : Nat
gf4096CardinalityRole = 4096

gf4096CardinalityIsTwoPowTwelve :
  gf4096CardinalityRole ≡ 2 ^ 12
gf4096CardinalityIsTwoPowTwelve = refl

gf4096OrbitSpectrumStillPaid :
  4096 ≡ 2 * 1 + 1 * 2 + 2 * 3 + 3 * 4 + 9 * 6 + 335 * 12
gf4096OrbitSpectrumStillPaid =
  JMD.gf4096OrbitSpectrumCloses

------------------------------------------------------------------------
-- 2. Monster 2-local branching-dimension role.
------------------------------------------------------------------------

monsterTwoLocal4096Role : Nat
monsterTwoLocal4096Role =
  Branching.tensorLeft Branching.conwayTwoLocalReducedBenchmark

monsterTwoLocal4096RoleIs4096 :
  monsterTwoLocal4096Role ≡ 4096
monsterTwoLocal4096RoleIs4096 = refl

monsterTwoLocalReducedBranchingExact :
  Branching.ambientTensorDimension Branching.conwayTwoLocalReducedBenchmark
  ≡ Branching.tensorLeft Branching.conwayTwoLocalReducedBenchmark
      * Branching.tensorRight Branching.conwayTwoLocalReducedBenchmark
    + Branching.residualFirst Branching.conwayTwoLocalReducedBenchmark
    + Branching.residualSecond Branching.conwayTwoLocalReducedBenchmark
monsterTwoLocalReducedBranchingExact =
  Branching.conwayTwoLocalReducedDimensionExact

monsterTwoLocalReducedBranchingLiteral :
  196883 ≡ 4096 * 24 + 98280 + 299
monsterTwoLocalReducedBranchingLiteral = refl

monsterTwoLocalUnreducedBranchingLiteral :
  196884 ≡ 4096 * 24 + 98280 + 300
monsterTwoLocalUnreducedBranchingLiteral = refl

------------------------------------------------------------------------
-- 3. Same printed scalar, two typed roles.
------------------------------------------------------------------------

sameScalar4096 :
  gf4096CardinalityRole ≡ monsterTwoLocal4096Role
sameScalar4096 = refl

record Scalar4096Role : Set where
  constructor scalar4096-role
  field
    roleName : String
    sourceOwner : String
    exactScalar : Nat
    meaning : String

finiteField4096Role : Scalar4096Role
finiteField4096Role =
  scalar4096-role
    "GF(2^12) cardinality"
    "JMD Frobenius prompt / standard finite-field arithmetic"
    4096
    "number of elements of GF(2^12)"

monsterBranch4096Role : Scalar4096Role
monsterBranch4096Role =
  scalar4096-role
    "Monster 2-local tensor factor"
    "MonsterSubgroupBranchingBenchmarksExact"
    4096
    "left tensor dimension in the sourced 196883 = 4096*24 + 98280 + 299 benchmark"

------------------------------------------------------------------------
-- 4. Promotion firewalls.
------------------------------------------------------------------------

data SameScalar4096IdentifiesRoles : Set where

data GF4096ConstructsMonsterTwoLocalModule : Set where

data GF4096SelectsTwoBTateQ10 : Set where

sameScalarDoesNotIdentify4096Roles :
  SameScalar4096IdentifiesRoles → ⊥
sameScalarDoesNotIdentify4096Roles ()

gf4096DoesNotConstructMonsterTwoLocalModule :
  GF4096ConstructsMonsterTwoLocalModule → ⊥
gf4096DoesNotConstructMonsterTwoLocalModule ()

gf4096DoesNotSelectTwoBTateQ10 :
  GF4096SelectsTwoBTateQ10 → ⊥
gf4096DoesNotSelectTwoBTateQ10 ()

------------------------------------------------------------------------
-- 5. Recognition frontier.
------------------------------------------------------------------------

record GF4096MonsterTwoLocalBoundary : Set where
  constructor gf4096-monster-two-local-boundary
  field
    jmdGF4096PromptCredited : Bool
    finiteFieldCardinalityRolePaid : Bool
    finiteFieldFrobeniusSpectrumPaid : Bool
    monsterTwoLocal4096RolePaid : Bool
    sameScalarPaid : Bool
    actualModuleIdentificationPaid : Bool
    actualActionIntertwinerPaid : Bool
    selectedTwoBTateQ10DerivedFrom4096 : Bool

canonicalGF4096MonsterTwoLocalBoundary :
  GF4096MonsterTwoLocalBoundary
canonicalGF4096MonsterTwoLocalBoundary =
  gf4096-monster-two-local-boundary
    true true true true true false false false
