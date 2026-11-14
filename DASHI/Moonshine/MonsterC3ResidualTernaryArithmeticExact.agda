module DASHI.Moonshine.MonsterC3ResidualTernaryArithmeticExact where

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_^_; _∸_)

import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as Monster3B
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as PrimeLane

------------------------------------------------------------------------
-- Two neighbouring ternary arithmetic constructions have distinct repo roles.
--
--   (3 + 3) * 3^(3-1) - 1             = 53
--   (3 + 3 + (3-1)) * 3^(3-1) - 1     = 71
--
-- 53 is already the certified residual multiplicity of the Monster 3B
-- restriction.  71 is already a tracked Ogg / supersingular Monster prime.
-- The numerical formulas below are exact arithmetic only; their physical or
-- representation-theoretic meanings come from the imported owners.
------------------------------------------------------------------------

ternarySquare : Nat
ternarySquare = 3 ^ 2

ternaryPairCoefficient : Nat
ternaryPairCoefficient = 3 + 3

extendedTernaryCoefficient : Nat
extendedTernaryCoefficient = 3 + 3 + (3 ∸ 1)

residual53FromTernaryNeighbour : Nat
residual53FromTernaryNeighbour =
  (ternaryPairCoefficient * ternarySquare) ∸ 1

residual53FromTernaryNeighbourIs53 :
  residual53FromTernaryNeighbour ≡ 53
residual53FromTernaryNeighbourIs53 = refl

ogg71FromExtendedTernaryNeighbour : Nat
ogg71FromExtendedTernaryNeighbour =
  (extendedTernaryCoefficient * ternarySquare) ∸ 1

ogg71FromExtendedTernaryNeighbourIs71 :
  ogg71FromExtendedTernaryNeighbour ≡ 71
ogg71FromExtendedTernaryNeighbourIs71 = refl

certifiedMonster3BResidual : Nat
certifiedMonster3BResidual =
  Monster3B.residualMultiplicity Monster3B.monster3BResidualRegularCarrier

certifiedMonster3BResidualIs53 : certifiedMonster3BResidual ≡ 53
certifiedMonster3BResidualIs53 = refl

residual53ArithmeticMatchesCertified3BResidual :
  residual53FromTernaryNeighbour ≡ certifiedMonster3BResidual
residual53ArithmeticMatchesCertified3BResidual = refl

trackedOgg71 : Nat
trackedOgg71 = PrimeLane.monsterPrimeLaneToNat PrimeLane.p71

trackedOgg71Is71 : trackedOgg71 ≡ 71
trackedOgg71Is71 = refl

extendedTernaryArithmeticMatchesTrackedOgg71 :
  ogg71FromExtendedTernaryNeighbour ≡ trackedOgg71
extendedTernaryArithmeticMatchesTrackedOgg71 = refl

oggTripleProduct : Nat
oggTripleProduct = 47 * 59 * 71

oggTripleProductIsMonsterDegree : oggTripleProduct ≡ 196883
oggTripleProductIsMonsterDegree = refl

monster3BResidualPlusRegularFibres : Nat
monster3BResidualPlusRegularFibres =
  certifiedMonster3BResidual + 3 * Monster3B.monster3BRegularMultiplicity

monster3BResidualPlusRegularFibresIsMonsterDegree :
  monster3BResidualPlusRegularFibres ≡ 196883
monster3BResidualPlusRegularFibresIsMonsterDegree
  rewrite Monster3B.monster3BRegularMultiplicityIs65610 = refl

------------------------------------------------------------------------
-- The same target integer can have multiple typed derivations.  Equality of
-- values is not equality of provenance, action, grading or interpretation.
------------------------------------------------------------------------

data ArithmeticRole : Set where
  ternaryResidualArithmetic : ArithmeticRole
  monster3BRepresentationResidual : ArithmeticRole
  oggPrimeLaneArithmetic : ArithmeticRole
  monsterDegreeFactorArithmetic : ArithmeticRole

record TernaryResidualBoundary : Set where
  constructor ternaryResidualBoundary
  field
    arithmeticIdentityProvesRepresentationMeaning : Bool
    arithmeticIdentityProvesRepresentationMeaningIsFalse :
      arithmeticIdentityProvesRepresentationMeaning ≡ false

    arithmeticIdentityProvesOggClassification : Bool
    arithmeticIdentityProvesOggClassificationIsFalse :
      arithmeticIdentityProvesOggClassification ≡ false

    arithmeticIdentityProvesMonsterModuleIntertwiner : Bool
    arithmeticIdentityProvesMonsterModuleIntertwinerIsFalse :
      arithmeticIdentityProvesMonsterModuleIntertwiner ≡ false

    arithmeticIdentityProvesGravity : Bool
    arithmeticIdentityProvesGravityIsFalse :
      arithmeticIdentityProvesGravity ≡ false

    certified3BResidualRoleImportedSeparately : Bool
    certified3BResidualRoleImportedSeparatelyIsTrue :
      certified3BResidualRoleImportedSeparately ≡ true

    trackedOgg71RoleImportedSeparately : Bool
    trackedOgg71RoleImportedSeparatelyIsTrue :
      trackedOgg71RoleImportedSeparately ≡ true

canonicalTernaryResidualBoundary : TernaryResidualBoundary
canonicalTernaryResidualBoundary =
  ternaryResidualBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
