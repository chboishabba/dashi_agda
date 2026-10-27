module DASHI.Moonshine.OggSSP2BMonsterGF2RepresentationSourceExact where

------------------------------------------------------------------------
-- EXPLICIT MONSTER REPRESENTATION OVER GF(2): SOURCE AUTHORITY BOUNDARY
--
-- Wilson and collaborators constructed the Monster on a 196882-dimensional
-- vector space over GF(2); standard generators and vector-action routines were
-- computed in the 3-local construction.  This is the correct characteristic
-- for resolving the post-Brauer 2B extension/action problem.
--
-- The repository does not currently contain those sparse generator/action
-- programs or an explicit restriction of that module to the sourced 2B-local
-- M22:2 stabilizer.  Therefore the external construction is a concrete source
-- route, but it does NOT itself pay:
--
--   * identification with Hhat0(2B,V^natural_2),
--   * an explicit N <= S stable subquotient,
--   * the outer J2^5 action on that same quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

monsterGF2Dimension : Nat
monsterGF2Dimension = 196882

monsterGF2DimensionExact : monsterGF2Dimension ≡ 196882
monsterGF2DimensionExact = refl

record MonsterGF2RepresentationSourceStatus : Set where
  constructor monster-gf2-representation-source-status
  field
    explicitMonsterGF2RepresentationSourced : Bool
    standardGeneratorsComputedExternally : Bool
    vectorActionProgramsKnownExternally : Bool
    actionProgramsPresentInRepository : Bool
    twoBLocalRestrictionMatricesPresent : Bool
    actualTate276IdentificationPaid : Bool
    stableQ10SubquotientPaid : Bool
    outerJ2x5OnSameQPaid : Bool

canonicalMonsterGF2RepresentationSourceStatus : MonsterGF2RepresentationSourceStatus
canonicalMonsterGF2RepresentationSourceStatus =
  monster-gf2-representation-source-status
    true true true false false false false false

data ExternalGF2MonsterRepresentationIsTwoBTateHead : Set where

data ExistenceOfGF2RepresentationConstructsStableQ10 : Set where

externalGF2RepresentationDoesNotIdentifyTwoBTateHead :
  ExternalGF2MonsterRepresentationIsTwoBTateHead → ⊥
externalGF2RepresentationDoesNotIdentifyTwoBTateHead ()

existenceDoesNotConstructStableQ10 :
  ExistenceOfGF2RepresentationConstructsStableQ10 → ⊥
existenceDoesNotConstructStableQ10 ()
