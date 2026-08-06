module DASHI.Physics.Closure.NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Author: Runlong Yu.
-- Title: "A Structural Audit of Navier-Stokes Obstruction Calculus".
-- DOI: 10.48550/arXiv.2606.25341.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact algebraic core of K7 without ever
-- differentiating the singular normalized direction xi = omega/|omega|.
-- For two vorticity vectors a,b with increments A,B it proves
--
--   (a+hA) cross (b+hB)
--     = a cross b
--       + h (A cross b + a cross B)
--       + h^2 (A cross B),
--
-- and the complete fourth-order polynomial expansion of its squared norm.
-- The coefficient linear in h is exactly
--
--   2 (a cross b) dot (A cross b + a cross B).
--
-- Derivative pairs are then summed recursively, proving an exact five-source
-- split for advection, stretching, subgrid, kernel and tail contributions.
-- The physical PDE estimates and the dissipative sign remain open producers;
-- the product rule and source bookkeeping are no longer assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram

vecAdd : Gram.Vec3 → Gram.Vec3 → Gram.Vec3
vecAdd left right =
  Gram.vec3
    (Gram.x left + Gram.x right)
    (Gram.y left + Gram.y right)
    (Gram.z left + Gram.z right)

scaleVec : ℚ → Gram.Vec3 → Gram.Vec3
scaleVec scalar vector =
  Gram.vec3
    (scalar * Gram.x vector)
    (scalar * Gram.y vector)
    (scalar * Gram.z vector)

vecExt :
  ∀ {left right : Gram.Vec3} →
  Gram.x left ≡ Gram.x right →
  Gram.y left ≡ Gram.y right →
  Gram.z left ≡ Gram.z right →
  left ≡ right
vecExt
  {left = Gram.vec3 lx ly lz}
  {right = Gram.vec3 .lx .ly .lz}
  refl refl refl = refl

crossFirstVariation :
  Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → Gram.Vec3
crossFirstVariation left right leftRate rightRate =
  vecAdd
    (Gram.cross leftRate right)
    (Gram.cross left rightRate)

crossSecondVariation : Gram.Vec3 → Gram.Vec3 → Gram.Vec3
crossSecondVariation = Gram.cross

crossPerturbationExpansion :
  ∀ h left right leftRate rightRate →
  Gram.cross
    (vecAdd left (scaleVec h leftRate))
    (vecAdd right (scaleVec h rightRate))
  ≡
  vecAdd
    (Gram.cross left right)
    (vecAdd
      (scaleVec h
        (crossFirstVariation left right leftRate rightRate))
      (scaleVec (h * h)
        (crossSecondVariation leftRate rightRate)))
crossPerturbationExpansion h left right leftRate rightRate =
  vecExt (solve values) (solve values) (solve values)
  where
  values =
    h
    ∷ Gram.x left ∷ Gram.y left ∷ Gram.z left
    ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right
    ∷ Gram.x leftRate ∷ Gram.y leftRate ∷ Gram.z leftRate
    ∷ Gram.x rightRate ∷ Gram.y rightRate ∷ Gram.z rightRate
    ∷ []

crossDefectFirstVariation :
  Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → ℚ
crossDefectFirstVariation left right leftRate rightRate =
  2 * Gram.dot
    (Gram.cross left right)
    (crossFirstVariation left right leftRate rightRate)

crossDefectSecondCoefficient :
  Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → ℚ
crossDefectSecondCoefficient left right leftRate rightRate =
  Gram.normSquared
    (crossFirstVariation left right leftRate rightRate)
  + 2 * Gram.dot
      (Gram.cross left right)
      (crossSecondVariation leftRate rightRate)

crossDefectThirdCoefficient :
  Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → ℚ
crossDefectThirdCoefficient left right leftRate rightRate =
  2 * Gram.dot
    (crossFirstVariation left right leftRate rightRate)
    (crossSecondVariation leftRate rightRate)

crossDefectFourthCoefficient : Gram.Vec3 → Gram.Vec3 → ℚ
crossDefectFourthCoefficient leftRate rightRate =
  Gram.normSquared (crossSecondVariation leftRate rightRate)

crossDefectPerturbationExpansion :
  ∀ h left right leftRate rightRate →
  Gram.crossNormSquared
    (vecAdd left (scaleVec h leftRate))
    (vecAdd right (scaleVec h rightRate))
  ≡
  Gram.crossNormSquared left right
  + h * crossDefectFirstVariation left right leftRate rightRate
  + (h * h)
      * crossDefectSecondCoefficient left right leftRate rightRate
  + (h * h * h)
      * crossDefectThirdCoefficient left right leftRate rightRate
  + (h * h * h * h)
      * crossDefectFourthCoefficient leftRate rightRate
crossDefectPerturbationExpansion h left right leftRate rightRate =
  solve values
  where
  values =
    h
    ∷ Gram.x left ∷ Gram.y left ∷ Gram.z left
    ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right
    ∷ Gram.x leftRate ∷ Gram.y leftRate ∷ Gram.z leftRate
    ∷ Gram.x rightRate ∷ Gram.y rightRate ∷ Gram.z rightRate
    ∷ []

record DerivativePair : Set where
  constructor derivativePair
  field
    leftRate rightRate : Gram.Vec3

open DerivativePair public

zeroVec : Gram.Vec3
zeroVec = Gram.vec3 0ℚ 0ℚ 0ℚ

zeroDerivativePair : DerivativePair
zeroDerivativePair = derivativePair zeroVec zeroVec

addDerivativePair : DerivativePair → DerivativePair → DerivativePair
addDerivativePair first second =
  derivativePair
    (vecAdd (leftRate first) (leftRate second))
    (vecAdd (rightRate first) (rightRate second))

sumDerivativePairs : List DerivativePair → DerivativePair
sumDerivativePairs [] = zeroDerivativePair
sumDerivativePairs (pair ∷ pairs) =
  addDerivativePair pair (sumDerivativePairs pairs)

defectRate : Gram.Vec3 → Gram.Vec3 → DerivativePair → ℚ
defectRate left right pair =
  crossDefectFirstVariation
    left right (leftRate pair) (rightRate pair)

defectRateAdditive :
  ∀ left right first second →
  defectRate left right (addDerivativePair first second)
  ≡ defectRate left right first + defectRate left right second
defectRateAdditive left right first second =
  solve
    ( Gram.x left ∷ Gram.y left ∷ Gram.z left
    ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right
    ∷ Gram.x (leftRate first) ∷ Gram.y (leftRate first)
    ∷ Gram.z (leftRate first)
    ∷ Gram.x (rightRate first) ∷ Gram.y (rightRate first)
    ∷ Gram.z (rightRate first)
    ∷ Gram.x (leftRate second) ∷ Gram.y (leftRate second)
    ∷ Gram.z (leftRate second)
    ∷ Gram.x (rightRate second) ∷ Gram.y (rightRate second)
    ∷ Gram.z (rightRate second)
    ∷ [])

sumDefectRates :
  Gram.Vec3 → Gram.Vec3 → List DerivativePair → ℚ
sumDefectRates left right [] = 0ℚ
sumDefectRates left right (pair ∷ pairs) =
  defectRate left right pair + sumDefectRates left right pairs

defectRateFiniteSourceSplit :
  ∀ left right pairs →
  defectRate left right (sumDerivativePairs pairs)
  ≡ sumDefectRates left right pairs
defectRateFiniteSourceSplit left right [] = solve []
defectRateFiniteSourceSplit left right (pair ∷ pairs) =
  trans
    (defectRateAdditive left right pair (sumDerivativePairs pairs))
    (cong
      (λ tailRate → defectRate left right pair + tailRate)
      (defectRateFiniteSourceSplit left right pairs))

record FiveSourceDefectJet : Set where
  constructor fiveSourceDefectJet
  field
    leftVorticity rightVorticity : Gram.Vec3
    advection stretching subgrid kernel tail : DerivativePair

open FiveSourceDefectJet public

fiveSourcePairs : FiveSourceDefectJet → List DerivativePair
fiveSourcePairs jet =
  advection jet
  ∷ stretching jet
  ∷ subgrid jet
  ∷ kernel jet
  ∷ tail jet
  ∷ []

fiveSourceDefectEvolutionSplit :
  ∀ jet →
  defectRate
    (leftVorticity jet)
    (rightVorticity jet)
    (sumDerivativePairs (fiveSourcePairs jet))
  ≡
  defectRate (leftVorticity jet) (rightVorticity jet) (advection jet)
  + defectRate (leftVorticity jet) (rightVorticity jet) (stretching jet)
  + defectRate (leftVorticity jet) (rightVorticity jet) (subgrid jet)
  + defectRate (leftVorticity jet) (rightVorticity jet) (kernel jet)
  + defectRate (leftVorticity jet) (rightVorticity jet) (tail jet)
fiveSourceDefectEvolutionSplit jet =
  defectRateFiniteSourceSplit
    (leftVorticity jet)
    (rightVorticity jet)
    (fiveSourcePairs jet)

record CrossDefectEvolutionAuthorityBoundary : Set where
  constructor crossDefectEvolutionAuthorityBoundary
  field
    fullPerturbationPolynomialProved : Set
    firstVariationIdentified : Set
    finiteFiveSourceSplitProved : Set
    filteredNavierStokesSourcesInstantiated : Set
    dissipativeDefectInequalityProved : Set

canonicalCrossDefectEvolutionAuthorityBoundary :
  CrossDefectEvolutionAuthorityBoundary
canonicalCrossDefectEvolutionAuthorityBoundary =
  crossDefectEvolutionAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
