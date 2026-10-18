module DASHI.Moonshine.OggSSPSmallCharacteristicWildCanonicalCoefficientComparisonExact where

------------------------------------------------------------------------
-- WILD CANONICAL-COEFFICIENT COMPARISON
--
-- EXTERNAL GEOMETRIC INPUT
--
-- Kobin--Zureick-Brown compute the rigidified level-1 wild modular stack:
--
--   characteristic 3:
--     K_{X(1)^rig} = -5 [0:1],
--     K_{X(1)^rig} + Delta = 1 [0:1].
--
--   characteristic 2:
--     K_{X(1)^rig} = -10 [0:1],
--     K_{X(1)^rig} + Delta = 2 [0:1].
--
-- DASHI COMPARISON
--
-- The p=2 canonical coefficient magnitude 10 independently matches the
-- Duncan--Swisher/Monster exceptional gap 10.
--
-- The analogous p=3 canonical magnitude is 5, not 2, so a UNIFORM
-- "Monster gap = absolute wild canonical coefficient" law is false.
--
-- The p=3 log-canonical coefficient is 1 on the rigidified stack; the
-- unrigidified modular-form grading is doubled, giving the familiar weight-2
-- Hasse generator.  This is recorded as geometric context only, not as a
-- Monster-valuation theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Sourced finite geometric coefficients.
------------------------------------------------------------------------

p2RigidifiedCanonicalCoefficientMagnitude : Nat
p2RigidifiedCanonicalCoefficientMagnitude = 10

p3RigidifiedCanonicalCoefficientMagnitude : Nat
p3RigidifiedCanonicalCoefficientMagnitude = 5

p2RigidifiedLogCanonicalCoefficient : Nat
p2RigidifiedLogCanonicalCoefficient = 2

p3RigidifiedLogCanonicalCoefficient : Nat
p3RigidifiedLogCanonicalCoefficient = 1

p3UnrigidifiedHasseWeight : Nat
p3UnrigidifiedHasseWeight = 2

------------------------------------------------------------------------
-- 2. Compare to exact exceptional Monster gaps.
------------------------------------------------------------------------

p2MonsterExceptionalGap : Nat
p2MonsterExceptionalGap =
  Wild.wildGeometricSectorCount Wild.primeTwo

p3MonsterExceptionalGap : Nat
p3MonsterExceptionalGap =
  Wild.wildGeometricSectorCount Wild.primeThree

p2CanonicalMagnitudeMatchesMonsterGap :
  p2RigidifiedCanonicalCoefficientMagnitude
  ≡ p2MonsterExceptionalGap
p2CanonicalMagnitudeMatchesMonsterGap = refl

p3CanonicalMagnitudeDoesNotMatchMonsterGap :
  p3RigidifiedCanonicalCoefficientMagnitude
  ≡ p3MonsterExceptionalGap
  ->
  ⊥
p3CanonicalMagnitudeDoesNotMatchMonsterGap ()

p3HasseWeightMatchesGapNumerically :
  p3UnrigidifiedHasseWeight
  ≡ p3MonsterExceptionalGap
p3HasseWeightMatchesGapNumerically = refl

------------------------------------------------------------------------
-- 3. Mechanism firewalls.
------------------------------------------------------------------------

data UniformCanonicalCoefficientCorrectionLaw : Set where
data P2CanonicalMagnitudeIsMonsterValuationTerm : Set where
data P3HasseWeightIsMonsterValuationTerm : Set where
data NumericalMatchCreatesAnalyticFourthTerm : Set where

uniformCanonicalCoefficientLawFails :
  UniformCanonicalCoefficientCorrectionLaw -> ⊥
uniformCanonicalCoefficientLawFails ()

p2CanonicalMagnitudeNotYetMonsterValuationTerm :
  P2CanonicalMagnitudeIsMonsterValuationTerm -> ⊥
p2CanonicalMagnitudeNotYetMonsterValuationTerm ()

p3HasseWeightNotYetMonsterValuationTerm :
  P3HasseWeightIsMonsterValuationTerm -> ⊥
p3HasseWeightNotYetMonsterValuationTerm ()

numericalMatchDoesNotCreateAnalyticFourthTerm :
  NumericalMatchCreatesAnalyticFourthTerm -> ⊥
numericalMatchDoesNotCreateAnalyticFourthTerm ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record WildCanonicalCoefficientComparisonBoundary : Set where
  constructor wild-canonical-coefficient-comparison-boundary
  field
    p2CanonicalMagnitudeTenSourced : Bool
    p3CanonicalMagnitudeFiveSourced : Bool
    p2LogCanonicalCoefficientTwoSourced : Bool
    p3LogCanonicalCoefficientOneSourced : Bool
    p3UnrigidifiedHasseWeightTwoSourced : Bool
    p2CanonicalMagnitudeMatchesGap : Bool
    p3CanonicalMagnitudeMatchesGap : Bool
    p3HasseWeightMatchesGapNumerically : Bool
    uniformCanonicalCorrectionLawSurvives : Bool
    analyticFourthTermConstructed : Bool
    attributionFirewallPreserved : Bool

canonicalWildCanonicalCoefficientComparisonBoundary :
  WildCanonicalCoefficientComparisonBoundary
canonicalWildCanonicalCoefficientComparisonBoundary =
  wild-canonical-coefficient-comparison-boundary
    true true true true true
    true false true
    false false true
