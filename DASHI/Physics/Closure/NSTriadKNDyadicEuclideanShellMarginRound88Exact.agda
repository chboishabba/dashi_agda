module DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND88 / CANONICAL DYADIC MAX-NORM -> EUCLIDEAN-SQUARE WELD
--
-- The canonical shell index is built from ||k||_infinity, whereas the literal
-- viscous coefficient uses |k|_2^2.  This file closes the finite lattice seam:
--
--   ||k||_infinity^2 <= |k|_2^2 <= 3 ||k||_infinity^2.
--
-- Combining the right inequality with the already-proved ceil-log shell upper
-- bound gives, for shellIndex(k) <= K,
--
--   |k|_2^2 <= 3 * (2^K)^2.
--
-- The left inequality is the matching lower bridge needed for a separated high
-- leg.  No continuum norm equivalence, asymptotic notation, or hidden constant
-- is used: this is exact Nat arithmetic on the integer Fourier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Ceil

natSquare : Nat → Nat
natSquare n = n * n

integerMagnitudeIsAbs : ∀ z → Cube.integerMagnitude z ≡ ∣ z ∣
integerMagnitudeIsAbs (+ n) = refl
integerMagnitudeIsAbs (-[1+ n ]) = refl

modeNatNormAsAbsoluteSquares : ∀ k →
  ModeNorm.modeNatNormSquared k
  ≡ natSquare (∣ Z3.kx k ∣)
      + (natSquare (∣ Z3.ky k ∣) + natSquare (∣ Z3.kz k ∣))
modeNatNormAsAbsoluteSquares (Z3.mode x y z)
  rewrite integerMagnitudeIsAbs x
        | integerMagnitudeIsAbs y
        | integerMagnitudeIsAbs z = refl

squareMonotone : ∀ {a b} → a ≤ b → natSquare a ≤ natSquare b
squareMonotone bound = Nat.*-mono-≤ bound bound

selectedSquareBelowTripleSumX : ∀ x y z →
  natSquare x ≤ natSquare x + (natSquare y + natSquare z)
selectedSquareBelowTripleSumX x y z =
  Nat.m≤m+n (natSquare x) (natSquare y + natSquare z)

selectedSquareBelowTripleSumY : ∀ x y z →
  natSquare y ≤ natSquare x + (natSquare y + natSquare z)
selectedSquareBelowTripleSumY x y z =
  Nat.≤-trans
    (Nat.m≤m+n (natSquare y) (natSquare z))
    (Nat.m≤n+m (natSquare y + natSquare z) (natSquare x))

selectedSquareBelowTripleSumZ : ∀ x y z →
  natSquare z ≤ natSquare x + (natSquare y + natSquare z)
selectedSquareBelowTripleSumZ x y z =
  Nat.≤-trans
    (Nat.m≤n+m (natSquare z) (natSquare y))
    (Nat.m≤n+m (natSquare y + natSquare z) (natSquare x))

max3SquareBelowSumSquares : ∀ x y z →
  natSquare (Infinity.max3 x y z)
  ≤ natSquare x + (natSquare y + natSquare z)
max3SquareBelowSumSquares x y z with Nat.≤-total x y
... | inj₁ x≤y
  rewrite Nat.m≤n⇒m⊔n≡n x≤y
  with Nat.≤-total y z
...   | inj₁ y≤z
      rewrite Nat.m≤n⇒m⊔n≡n y≤z =
      selectedSquareBelowTripleSumZ x y z
...   | inj₂ z≤y
      rewrite Nat.m≥n⇒m⊔n≡m z≤y =
      selectedSquareBelowTripleSumY x y z
... | inj₂ y≤x
  rewrite Nat.m≥n⇒m⊔n≡m y≤x
  with Nat.≤-total x z
...   | inj₁ x≤z
      rewrite Nat.m≤n⇒m⊔n≡n x≤z =
      selectedSquareBelowTripleSumZ x y z
...   | inj₂ z≤x
      rewrite Nat.m≥n⇒m⊔n≡m z≤x =
      selectedSquareBelowTripleSumX x y z

threeTimesSquare : ∀ n →
  3 * natSquare n
  ≡ natSquare n + (natSquare n + natSquare n)
threeTimesSquare n =
  trans
    (cong (λ tail → natSquare n + (natSquare n + tail))
      (Nat.*-zeroʳ (natSquare n)))
    refl

sumSquaresBelowThreeMaxSquare : ∀ x y z →
  natSquare x + (natSquare y + natSquare z)
  ≤ 3 * natSquare (Infinity.max3 x y z)
sumSquaresBelowThreeMaxSquare x y z =
  let
    M = Infinity.max3 x y z
    xSquare = squareMonotone (Infinity.first≤max3 x y z)
    ySquare = squareMonotone (Infinity.second≤max3 x y z)
    zSquare = squareMonotone (Infinity.third≤max3 x y z)
    summed = Nat.+-mono-≤ xSquare (Nat.+-mono-≤ ySquare zSquare)
  in
  subst
    (λ upper →
      natSquare x + (natSquare y + natSquare z) ≤ upper)
    (sym (threeTimesSquare M))
    summed

infinitySquareBelowModeNatNorm : ∀ k →
  natSquare (Infinity.infinityNorm k) ≤ ModeNorm.modeNatNormSquared k
infinitySquareBelowModeNatNorm (Z3.mode x y z) =
  subst
    (natSquare (Infinity.infinityNorm (Z3.mode x y z)) ≤_)
    (sym (modeNatNormAsAbsoluteSquares (Z3.mode x y z)))
    (max3SquareBelowSumSquares (∣ x ∣) (∣ y ∣) (∣ z ∣))

modeNatNormBelowThreeInfinitySquare : ∀ k →
  ModeNorm.modeNatNormSquared k ≤ 3 * natSquare (Infinity.infinityNorm k)
modeNatNormBelowThreeInfinitySquare (Z3.mode x y z) =
  subst
    (_≤ 3 * natSquare (Infinity.infinityNorm (Z3.mode x y z)))
    (sym (modeNatNormAsAbsoluteSquares (Z3.mode x y z)))
    (sumSquaresBelowThreeMaxSquare (∣ x ∣) (∣ y ∣) (∣ z ∣))

pow2Monotone : ∀ {j k} → j ≤ k → Shell.pow2 j ≤ Shell.pow2 k
pow2Monotone = Nat.^-monoʳ-≤ 2

modeInfinityBelowShellCeiling : ∀ k →
  Infinity.infinityNorm k ≤ Shell.pow2 (Shell.shellIndex k)
modeInfinityBelowShellCeiling k =
  Ceil.ceilLogShellUpperMagnitude (Infinity.infinityNorm k)

modeInfinityBelowHigherShellCeiling : ∀ {k K} →
  Shell.shellIndex k ≤ K →
  Infinity.infinityNorm k ≤ Shell.pow2 K
modeInfinityBelowHigherShellCeiling {k} {K} shell≤ =
  Nat.≤-trans
    (modeInfinityBelowShellCeiling k)
    (pow2Monotone shell≤)

modeNatNormBelowPacketThreeSquare : ∀ {k K} →
  Shell.shellIndex k ≤ K →
  ModeNorm.modeNatNormSquared k ≤ 3 * natSquare (Shell.pow2 K)
modeNatNormBelowPacketThreeSquare {k} {K} shell≤ =
  let
    infinitySquare≤ = squareMonotone (modeInfinityBelowHigherShellCeiling shell≤)
    scaled = Nat.*-mono-≤ Nat.≤-refl infinitySquare≤
  in
  Nat.≤-trans
    (modeNatNormBelowThreeInfinitySquare k)
    scaled

round88InfinityEuclideanSquareComparisonClosed : Bool
round88InfinityEuclideanSquareComparisonClosed = true

round88PacketEuclideanUpperThreeDyadicSquareClosed : Bool
round88PacketEuclideanUpperThreeDyadicSquareClosed = true

round88SeparatedHighEuclideanLowerNeedsOnlyShellExponentArithmetic : Bool
round88SeparatedHighEuclideanLowerNeedsOnlyShellExponentArithmetic = true

round88InfinityEuclideanSquareComparisonClosedIsTrue :
  round88InfinityEuclideanSquareComparisonClosed ≡ true
round88InfinityEuclideanSquareComparisonClosedIsTrue = refl
