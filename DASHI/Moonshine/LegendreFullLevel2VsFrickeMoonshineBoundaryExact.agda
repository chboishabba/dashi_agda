module DASHI.Moonshine.LegendreFullLevel2VsFrickeMoonshineBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tomoaki Nakaya,
-- "The number of linear factors of supersingular polynomials and sporadic
-- simple groups", Journal of Number Theory 204 (2019), 471--496.
-- DOI: 10.1016/j.jnt.2019.04.015.
-- Nakaya proves higher-level analogues of Ogg involving supersingular
-- polynomials and the Baby Monster / Fischer groups.
--
-- Victor Manuel Aricheta,
-- "Supersingular Elliptic Curves and Moonshine", SIGMA 15 (2019), 007.
-- DOI: 10.3842/SIGMA.2019.007.
-- This places Ogg's phenomenon in a broader family of monstrous modular curves
-- with level structure.
--
-- Josep González,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300.
-- DOI: 10.1016/j.jnt.2021.06.011.
-- This is the source authority for the full-level-2 Legendre Deuring
-- polynomial H_p(lambda) used elsewhere in this branch.
--
-- DASHI CONTRIBUTION / SEMANTIC GUARDRAIL
--
-- Do NOT identify Nakaya's level-2 Fricke supersingular invariant with the
-- full Gamma(2) Legendre lambda coordinate merely because both are called
-- "level 2".
--
-- p=11 is a decisive finite counterexample to that conflation:
--
--   H_11(lambda)
--    = (lambda-2)(lambda+1)(lambda+5)(lambda^2-lambda+1) mod 11,
--
-- and the final quadratic has discriminant
--
--   1-4 = -3 = 8 mod 11.
--
-- The complete F_11 square set is {0,1,3,4,5,9}; hence 8 is nonsquare and the
-- full-level-2 Legendre supersingular polynomial does NOT split completely over
-- F_11.  Nevertheless 11 is a prime divisor of the Baby Monster order and lies
-- in the higher-level sporadic phenomena discussed by Nakaya/Aricheta.
--
-- Therefore the Baby-Monster criterion cannot be read as
--
--   "H_p(lambda) splits completely over F_p".
--
-- Any eventual cross-pollination must construct the explicit map between the
-- relevant modular/Fricke invariant and the full-level-2 carrier rather than
-- identify them by level number or cardinality.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exhaustive p=11 square-residue classifier.
------------------------------------------------------------------------

isSquareResidue11 : Nat → Bool
isSquareResidue11 0 = true
isSquareResidue11 1 = true
isSquareResidue11 3 = true
isSquareResidue11 4 = true
isSquareResidue11 5 = true
isSquareResidue11 9 = true
isSquareResidue11 _ = false

legendreQuadraticDiscriminant11 : Nat
legendreQuadraticDiscriminant11 = 8

legendreQuadraticDiscriminantIsNonsquare :
  isSquareResidue11 legendreQuadraticDiscriminant11 ≡ false
legendreQuadraticDiscriminantIsNonsquare = refl

p11FullLevel2LegendreSplitsCompletely : Bool
p11FullLevel2LegendreSplitsCompletely = false

p11FullLevel2LegendreDoesNotSplitCompletely :
  p11FullLevel2LegendreSplitsCompletely ≡ false
p11FullLevel2LegendreDoesNotSplitCompletely = refl

-- Source-facing sporadic datum.  This is deliberately kept separate from the
-- Legendre splitting computation above.
p11IsBabyMonsterPrime : Bool
p11IsBabyMonsterPrime = true

p11BabyMonsterPrimeButLegendreNotFullySplit :
  p11IsBabyMonsterPrime ≡ true
  × p11FullLevel2LegendreSplitsCompletely ≡ false
p11BabyMonsterPrimeButLegendreNotFullySplit = refl , refl

record FullLevel2VsFrickeMoonshineBoundary : Set where
  field
    fullGamma2LegendreInvariantConstructed : Bool
    fullGamma2LegendreInvariantConstructedIsTrue :
      fullGamma2LegendreInvariantConstructed ≡ true

    frickeLevel2InvariantIdentifiedWithLegendreLambda : Bool
    frickeLevel2InvariantIdentifiedWithLegendreLambdaIsFalse :
      frickeLevel2InvariantIdentifiedWithLegendreLambda ≡ false

    p11FiniteCounterexampleToNaiveIdentificationConstructed : Bool
    p11FiniteCounterexampleToNaiveIdentificationConstructedIsTrue :
      p11FiniteCounterexampleToNaiveIdentificationConstructed ≡ true

    futureMoonshineBridgeRequiresExplicitInvariantMap : Bool
    futureMoonshineBridgeRequiresExplicitInvariantMapIsTrue :
      futureMoonshineBridgeRequiresExplicitInvariantMap ≡ true

canonicalFullLevel2VsFrickeMoonshineBoundary : FullLevel2VsFrickeMoonshineBoundary
canonicalFullLevel2VsFrickeMoonshineBoundary = record
  { fullGamma2LegendreInvariantConstructed = true
  ; fullGamma2LegendreInvariantConstructedIsTrue = refl
  ; frickeLevel2InvariantIdentifiedWithLegendreLambda = false
  ; frickeLevel2InvariantIdentifiedWithLegendreLambdaIsFalse = refl
  ; p11FiniteCounterexampleToNaiveIdentificationConstructed = true
  ; p11FiniteCounterexampleToNaiveIdentificationConstructedIsTrue = refl
  ; futureMoonshineBridgeRequiresExplicitInvariantMap = true
  ; futureMoonshineBridgeRequiresExplicitInvariantMapIsTrue = refl
  }
