module DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact where

------------------------------------------------------------------------
-- NATIVE BALANCED-TERNARY END SPACE, not lossy ternary OBSERVER.
-- K3 = C3 x {-1,0,+1}^N is inverse limit of 3 x Trit^n.
-- K2 = C3 x {left,right}^N is Hatcher's binary address limit.
--
-- Source: Alexander 1924, Hatcher AT 2B.2 (BINARY horns), classical
-- Cantor product topology and finite projective systems.
-- Reuse existing DASHI: RecursiveFibreTower.FibreTower/InverseLimitPoint,
-- BalancedTernary, Base369BinaryTernaryRefinement; #1414 polynomial
-- S3/C3 quaternion, #1254 prefix code, independent unmerged owners.
-- Nothing here asserts ambient wild embedding or Z2=Z3 as groups.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn
import DASHI.Cognition.RecursiveFibreTower as Tower

snoc : ∀ {A : Set} {n : Nat} → Vec A n → A → Vec A (suc n)
snoc [] x = x ∷ []
snoc (a ∷ xs) x = a ∷ snoc xs x

dropLast : ∀ {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
dropLast {n = zero} (_ ∷ []) = []
dropLast {n = suc n} (a ∷ xs) = a ∷ dropLast xs

dropLastSnoc : ∀ {A : Set} {n : Nat} (xs : Vec A n) (x : A) →
  dropLast (snoc xs x) ≡ xs
dropLastSnoc [] x = refl
dropLastSnoc (a ∷ xs) x =
  cong (a ∷_) (dropLastSnoc xs x)

mapVec : ∀ {A B : Set} {n : Nat} →
  (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

mapDropLast : ∀ {A B : Set} {n : Nat} (f : A → B)
  (xs : Vec A (suc n)) →
  dropLast (mapVec f xs) ≡ mapVec f (dropLast xs)
mapDropLast f (_ ∷ []) = refl
mapDropLast f (x ∷ y ∷ xs) =
  cong (f x ∷_) (mapDropLast f (y ∷ xs))

BinaryLevel : Nat → Set
BinaryLevel n = C3.C3 × Vec Horn.Bit n

BalancedLevel : Nat → Set
BalancedLevel n = C3.C3 × Vec Trit.Trit n

binaryProjection : ∀ n → BinaryLevel (suc n) → BinaryLevel n
binaryProjection n (c , xs) = c , dropLast xs

balancedProjection : ∀ n → BalancedLevel (suc n) → BalancedLevel n
balancedProjection n (c , xs) = c , dropLast xs

binaryEndTower : Tower.FibreTower
binaryEndTower = record
  { Level = BinaryLevel
  ; project = binaryProjection
  }

balancedEndTower : Tower.FibreTower
balancedEndTower = record
  { Level = BalancedLevel
  ; project = balancedProjection
  }

BinaryEndPoint : Set
BinaryEndPoint = Tower.InverseLimitPoint binaryEndTower

BalancedEndPoint : Set
BalancedEndPoint = Tower.InverseLimitPoint balancedEndTower

zeroWord : (n : Nat) → Vec Trit.Trit n
zeroWord zero = []
zeroWord (suc n) = snoc (zeroWord n) Trit.zero

zeroWordProjects : ∀ n →
  dropLast (zeroWord (suc n)) ≡ zeroWord n
zeroWordProjects n = dropLastSnoc (zeroWord n) Trit.zero

zeroEnd : C3.C3 → BalancedEndPoint
zeroEnd c = record
  { stateAt = λ n → (c , zeroWord n)
  ; coherent = λ n → cong (λ xs → (c , xs)) (zeroWordProjects n)
  }

rotateBinaryLevel : ∀ n → BinaryLevel n → BinaryLevel n
rotateBinaryLevel n (c , xs) = Horn.rotateSector c , xs

rotateBalancedLevel : ∀ n → BalancedLevel n → BalancedLevel n
rotateBalancedLevel n (c , xs) = Horn.rotateSector c , xs

rotateBinaryProjectionSquare : ∀ n (x : BinaryLevel (suc n)) →
  binaryProjection n (rotateBinaryLevel (suc n) x) ≡
    rotateBinaryLevel n (binaryProjection n x)
rotateBinaryProjectionSquare n (c , xs) = refl

rotateBalancedProjectionSquare : ∀ n (x : BalancedLevel (suc n)) →
  balancedProjection n (rotateBalancedLevel (suc n) x) ≡
    rotateBalancedLevel n (balancedProjection n x)
rotateBalancedProjectionSquare n (c , xs) = refl

balancedRotationCubed : ∀ n (x : BalancedLevel n) →
  rotateBalancedLevel n
   (rotateBalancedLevel n (rotateBalancedLevel n x)) ≡ x
balancedRotationCubed n (c , xs) =
  cong (λ sector → (sector , xs)) (Horn.rotateSectorCubed c)

reflectBalancedLevel : ∀ n → BalancedLevel n → BalancedLevel n
reflectBalancedLevel n (c , xs) = c , mapVec Trit.negate xs

rotateReflectCommute : ∀ n (x : BalancedLevel n) →
  rotateBalancedLevel n (reflectBalancedLevel n x) ≡
    reflectBalancedLevel n (rotateBalancedLevel n x)
rotateReflectCommute n (c , xs) = refl

-- A depth-two THREE-SECTOR ternary end partition has 3*3^2=27 cells.
threeSectorDepthTwoPrefixes : 3 * Tower.pow 3 2 ≡ 27
threeSectorDepthTwoPrefixes = refl

-- ONE trit label assigned to EACH of the 27 cells: 3^27 = 3↑↑3.
-- This configuration count is NOT a count of geometric depth-3 horns.
ternaryConfigurationTetration :
  Tower.pow 3 (3 * Tower.pow 3 2) ≡ Tower.tetration 3 3
ternaryConfigurationTetration
  rewrite threeSectorDepthTwoPrefixes =
  sym Tower.triadicTetrationThree


------------------------------------------------------------------------
-- PR #1414 ROOT-MONODROMY S3/C3 CONNECTION, TYPED AT TERNARY ENDS.
-- The internal three-symbol cycle and external three-SECTOR rotation
-- are two INDEPENDENT commuting C3 actions. Reflection on trits
-- conjugates the internal cycle to its INVERSE, as in S3, but it does
-- NOT invert the external sector rotation.
-- This DOES NOT identify a polynomial's analytic root monodromy with
-- the chosen Alexander exterior's geometric rotation.
------------------------------------------------------------------------

rotateDigit : Trit.Trit → Trit.Trit
rotateDigit Trit.neg = Trit.zero
rotateDigit Trit.zero = Trit.pos
rotateDigit Trit.pos = Trit.neg

rotateDigitCubed : ∀ t →
  rotateDigit (rotateDigit (rotateDigit t)) ≡ t
rotateDigitCubed Trit.neg = refl
rotateDigitCubed Trit.zero = refl
rotateDigitCubed Trit.pos = refl

digitReflectionConjugatesRotation : ∀ t →
  Trit.negate (rotateDigit (Trit.negate t)) ≡
    rotateDigit (rotateDigit t)
digitReflectionConjugatesRotation Trit.neg = refl
digitReflectionConjugatesRotation Trit.zero = refl
digitReflectionConjugatesRotation Trit.pos = refl

rotateDigits : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
rotateDigits = mapVec rotateDigit

reflectDigits : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
reflectDigits = mapVec Trit.negate

rotateDigitsCubed : ∀ {n} (xs : Vec Trit.Trit n) →
  rotateDigits (rotateDigits (rotateDigits xs)) ≡ xs
rotateDigitsCubed [] = refl
rotateDigitsCubed (t ∷ ts) =
  cong₂ _∷_ (rotateDigitCubed t) (rotateDigitsCubed ts)

import Relation.Binary.PropositionalEquality as Eq using (cong₂)

reflectConjugatesDigitCycle : ∀ {n} (xs : Vec Trit.Trit n) →
  reflectDigits (rotateDigits (reflectDigits xs)) ≡
    rotateDigits (rotateDigits xs)
reflectConjugatesDigitCycle [] = refl
reflectConjugatesDigitCycle (t ∷ ts) =
  Eq.cong₂ _∷_ (digitReflectionConjugatesRotation t)
    (reflectConjugatesDigitCycle ts)

rotateInternalLevel : ∀ n → BalancedLevel n → BalancedLevel n
rotateInternalLevel n (c , xs) = c , rotateDigits xs

rotateInternalProjectionSquare : ∀ n (x : BalancedLevel (suc n)) →
  balancedProjection n (rotateInternalLevel (suc n) x) ≡
    rotateInternalLevel n (balancedProjection n x)
rotateInternalProjectionSquare n (c , xs) =
  cong (λ ys → (c , ys)) (mapDropLast rotateDigit xs)

externalInternalC3Commute : ∀ n (x : BalancedLevel n) →
  rotateBalancedLevel n (rotateInternalLevel n x) ≡
    rotateInternalLevel n (rotateBalancedLevel n x)
externalInternalC3Commute n (c , xs) = refl

internalRotationCubed : ∀ n (x : BalancedLevel n) →
  rotateInternalLevel n
    (rotateInternalLevel n (rotateInternalLevel n x)) ≡ x
internalRotationCubed n (c , xs) =
  Eq.cong₂ _,_ refl (rotateDigitsCubed xs)

-- These independent actions are the direct-product source of an
-- *abstract* C3_sector × S3_digit on this finite address carrier.
-- They do not license a same-object polynomial braid or wild
-- pi1 representation, despite identical 3-cycle fingerprints.
