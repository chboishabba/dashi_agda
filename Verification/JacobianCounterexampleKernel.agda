module Verification.JacobianCounterexampleKernel where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Core.OperatorTypes using (Invertible)

------------------------------------------------------------------------
-- Logical kernel.

¬_ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

collisionImpliesNotInjective :
  ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≢ y →
  f x ≡ f y →
  ¬ Injective f
collisionImpliesNotInjective f x≢y fx≡fy injective =
  x≢y (injective fx≡fy)

invertibleImpliesInjective :
  ∀ {A : Set} {f : A → A} →
  Invertible f →
  Injective f
invertibleImpliesInjective inverseWitness {x} {y} fx≡fy =
  trans
    (sym (Invertible.left inverseWitness x))
    (trans
      (cong (Invertible.inv inverseWitness) fx≡fy)
      (Invertible.left inverseWitness y))

------------------------------------------------------------------------
-- A small exact three-variable polynomial language.
--
-- The derivative and determinant below are ordinary Agda functions.  The
-- final identity is discharged by the standard-library rational ring tactic,
-- so the polynomial differentiation and normalization are checked by Agda.

infixl 6 _+P_ _-P_
infixl 7 _*P_

data Axis : Set where
  xAxis yAxis zAxis : Axis

data Poly3 : Set where
  constant : ℚ → Poly3
  xVar yVar zVar : Poly3
  _+P_ _*P_ : Poly3 → Poly3 → Poly3
  negP : Poly3 → Poly3

_-P_ : Poly3 → Poly3 → Poly3
p -P q = p +P negP q

powP : Poly3 → Nat → Poly3
powP p zero = constant 1ℚ
powP p (suc n) = p *P powP p n

evalP : Poly3 → ℚ → ℚ → ℚ → ℚ
evalP (constant c) x y z = c
evalP xVar x y z = x
evalP yVar x y z = y
evalP zVar x y z = z
evalP (p +P q) x y z = evalP p x y z + evalP q x y z
evalP (p *P q) x y z = evalP p x y z * evalP q x y z
evalP (negP p) x y z = - evalP p x y z

diffP : Axis → Poly3 → Poly3
diffP axis (constant c) = constant 0ℚ
diffP xAxis xVar = constant 1ℚ
diffP yAxis xVar = constant 0ℚ
diffP zAxis xVar = constant 0ℚ
diffP xAxis yVar = constant 0ℚ
diffP yAxis yVar = constant 1ℚ
diffP zAxis yVar = constant 0ℚ
diffP xAxis zVar = constant 0ℚ
diffP yAxis zVar = constant 0ℚ
diffP zAxis zVar = constant 1ℚ
diffP axis (p +P q) = diffP axis p +P diffP axis q
diffP axis (p *P q) =
  (diffP axis p *P q) +P (p *P diffP axis q)
diffP axis (negP p) = negP (diffP axis p)

oneQ twoQ threeQ fourQ minusTwoQ quarterQ minusQuarterQ : ℚ
oneQ = 1ℚ
twoQ = + 2 / 1
threeQ = + 3 / 1
fourQ = + 4 / 1
minusTwoQ = - twoQ
quarterQ = + 1 / 4
minusQuarterQ = - quarterQ

uP vP : Poly3
uP = constant oneQ +P (xVar *P yVar)
vP = constant fourQ +P (constant threeQ *P (xVar *P yVar))

firstP secondP thirdP : Poly3
firstP =
  (powP uP 3 *P zVar) +P
  ((powP yVar 2 *P uP) *P vP)
secondP =
  yVar +P
  ((constant threeQ *P xVar) *P (powP uP 2 *P zVar)) +P
  ((constant threeQ *P xVar) *P (powP yVar 2 *P vP))
thirdP =
  (constant twoQ *P xVar) -P
  ((constant threeQ *P powP xVar 2) *P yVar) -P
  (powP xVar 3 *P zVar)

record PolynomialMap3 : Set where
  constructor polynomialMap3
  field
    firstCoordinate secondCoordinate thirdCoordinate : Poly3

open PolynomialMap3 public

alpogePolynomialMap : PolynomialMap3
alpogePolynomialMap = polynomialMap3 firstP secondP thirdP

record Point3 : Set where
  constructor point3
  field
    xCoordinate yCoordinate zCoordinate : ℚ

open Point3 public

applyPolynomialMap3 : PolynomialMap3 → Point3 → Point3
applyPolynomialMap3 m (point3 x y z) =
  point3
    (evalP (firstCoordinate m) x y z)
    (evalP (secondCoordinate m) x y z)
    (evalP (thirdCoordinate m) x y z)

F : Point3 → Point3
F = applyPolynomialMap3 alpogePolynomialMap

det3P :
  Poly3 → Poly3 → Poly3 →
  Poly3 → Poly3 → Poly3 →
  Poly3 → Poly3 → Poly3 →
  Poly3
det3P a b c d e f g h i =
  (a *P ((e *P i) -P (f *P h))) -P
  (b *P ((d *P i) -P (f *P g))) +P
  (c *P ((d *P h) -P (e *P g)))

jacobianDeterminantPolynomial : PolynomialMap3 → Poly3
jacobianDeterminantPolynomial m =
  det3P
    (diffP xAxis (firstCoordinate m))
    (diffP yAxis (firstCoordinate m))
    (diffP zAxis (firstCoordinate m))
    (diffP xAxis (secondCoordinate m))
    (diffP yAxis (secondCoordinate m))
    (diffP zAxis (secondCoordinate m))
    (diffP xAxis (thirdCoordinate m))
    (diffP yAxis (thirdCoordinate m))
    (diffP zAxis (thirdCoordinate m))

jacobianDeterminantAt : PolynomialMap3 → Point3 → ℚ
jacobianDeterminantAt m (point3 x y z) =
  evalP (jacobianDeterminantPolynomial m) x y z

jacobianDeterminantF :
  (p : Point3) →
  jacobianDeterminantAt alpogePolynomialMap p ≡ minusTwoQ
jacobianDeterminantF (point3 x y z) = solve-∀

minusTwoNonzero : minusTwoQ ≢ 0ℚ
minusTwoNonzero ()

jacobianEverywhereNonzero :
  (p : Point3) →
  jacobianDeterminantAt alpogePolynomialMap p ≢ 0ℚ
jacobianEverywhereNonzero p det≡zero =
  minusTwoNonzero (trans (sym (jacobianDeterminantF p)) det≡zero)

------------------------------------------------------------------------
-- Exact rational fibre.

zeroQ oneR minusOneR threeHalves minusThreeHalves thirteenHalves : ℚ
zeroQ = 0ℚ
oneR = 1ℚ
minusOneR = - 1ℚ
threeHalves = + 3 / 2
minusThreeHalves = - threeHalves
thirteenHalves = + 13 / 2

pZero pPositive pNegative target : Point3
pZero = point3 zeroQ zeroQ minusQuarterQ
pPositive = point3 oneR minusThreeHalves thirteenHalves
pNegative = point3 minusOneR threeHalves thirteenHalves
target = point3 minusQuarterQ zeroQ zeroQ

point3-ext :
  ∀ {x x' y y' z z' : ℚ} →
  x ≡ x' → y ≡ y' → z ≡ z' →
  point3 x y z ≡ point3 x' y' z'
point3-ext refl refl refl = refl

pZeroImage : F pZero ≡ target
pZeroImage = point3-ext solve-∀ solve-∀ solve-∀

pPositiveImage : F pPositive ≡ target
pPositiveImage = point3-ext solve-∀ solve-∀ solve-∀

pNegativeImage : F pNegative ≡ target
pNegativeImage = point3-ext solve-∀ solve-∀ solve-∀

zeroNotOne : zeroQ ≢ oneR
zeroNotOne ()

zeroNotMinusOne : zeroQ ≢ minusOneR
zeroNotMinusOne ()

pZeroNotPositive : pZero ≢ pPositive
pZeroNotPositive equality = zeroNotOne (cong xCoordinate equality)

pZeroNotNegative : pZero ≢ pNegative
pZeroNotNegative equality = zeroNotMinusOne (cong xCoordinate equality)

pZeroPositiveCollision : F pZero ≡ F pPositive
pZeroPositiveCollision = trans pZeroImage (sym pPositiveImage)

pZeroNegativeCollision : F pZero ≡ F pNegative
pZeroNegativeCollision = trans pZeroImage (sym pNegativeImage)

F-notInjective : ¬ Injective F
F-notInjective =
  collisionImpliesNotInjective F pZeroNotPositive pZeroPositiveCollision

------------------------------------------------------------------------
-- Keller-map and conjecture surfaces.

record KellerMap3 : Set where
  constructor kellerMap3
  field
    polynomial : PolynomialMap3
    determinantConstant : ℚ
    determinantNonzero : determinantConstant ≢ 0ℚ
    determinantIdentity :
      (p : Point3) →
      jacobianDeterminantAt polynomial p ≡ determinantConstant

open KellerMap3 public

alpogeKellerMap : KellerMap3
alpogeKellerMap =
  kellerMap3
    alpogePolynomialMap
    minusTwoQ
    minusTwoNonzero
    jacobianDeterminantF

JacobianConjectureDimension3 : Set
JacobianConjectureDimension3 =
  (K : KellerMap3) →
  Invertible (applyPolynomialMap3 (polynomial K))

jacobianConjectureDimension3False :
  ¬ JacobianConjectureDimension3
jacobianConjectureDimension3False conjecture =
  F-notInjective
    (invertibleImpliesInjective (conjecture alpogeKellerMap))

------------------------------------------------------------------------
-- Padding by untouched coordinates.

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

zeroTail : (n : Nat) → Vec ℚ n
zeroTail zero = []
zeroTail (suc n) = zeroQ ∷ zeroTail n

PaddedPoint : Nat → Set
PaddedPoint n = Point3 × Vec ℚ n

padF : (n : Nat) → PaddedPoint n → PaddedPoint n
padF n (p , tail) = F p , tail

pair-ext :
  ∀ {A B : Set} {a a' : A} {b b' : B} →
  a ≡ a' → b ≡ b' →
  (a , b) ≡ (a' , b')
pair-ext refl refl = refl

paddedZero paddedPositive : (n : Nat) → PaddedPoint n
paddedZero n = pZero , zeroTail n
paddedPositive n = pPositive , zeroTail n

paddedDistinct :
  (n : Nat) →
  paddedZero n ≢ paddedPositive n
paddedDistinct n equality = pZeroNotPositive (cong proj₁ equality)

paddedCollision :
  (n : Nat) →
  padF n (paddedZero n) ≡ padF n (paddedPositive n)
paddedCollision n = pair-ext pZeroPositiveCollision refl

paddedF-notInjective :
  (n : Nat) →
  ¬ Injective (padF n)
paddedF-notInjective n =
  collisionImpliesNotInjective
    (padF n)
    (paddedDistinct n)
    (paddedCollision n)

record PaddedKellerMap (tailDimension : Nat) : Set where
  constructor paddedKellerMap
  field
    baseMap : KellerMap3
    paddedMap : PaddedPoint tailDimension → PaddedPoint tailDimension
    isBaseTimesIdentity :
      (p : Point3) (tail : Vec ℚ tailDimension) →
      paddedMap (p , tail) ≡
      (applyPolynomialMap3 (polynomial baseMap) p , tail)
    blockDeterminantConstant : ℚ
    blockDeterminantNonzero : blockDeterminantConstant ≢ 0ℚ
    blockDeterminantInherited :
      blockDeterminantConstant ≡ determinantConstant baseMap

alpogePaddedKellerMap : (n : Nat) → PaddedKellerMap n
alpogePaddedKellerMap n =
  paddedKellerMap
    alpogeKellerMap
    (padF n)
    (λ p tail → refl)
    minusTwoQ
    minusTwoNonzero
    refl

JacobianConjectureDimensionThreePlus : Nat → Set
JacobianConjectureDimensionThreePlus n =
  (K : PaddedKellerMap n) →
  Invertible (PaddedKellerMap.paddedMap K)

jacobianConjectureDimensionThreePlusFalse :
  (n : Nat) →
  ¬ JacobianConjectureDimensionThreePlus n
jacobianConjectureDimensionThreePlusFalse n conjecture =
  paddedF-notInjective n
    (invertibleImpliesInjective (conjecture (alpogePaddedKellerMap n)))

------------------------------------------------------------------------
-- Historical/provenance boundary for the separate plane case.

record DimensionTwoStatus : Set where
  constructor dimensionTwoStatus
  field
    checkedDate : String
    settledByThisConstruction : Bool
    interpretation : String

jacobianConjectureDimension2Status : DimensionTwoStatus
jacobianConjectureDimension2Status =
  dimensionTwoStatus
    "2026-07-21"
    false
    "the three-variable map and identity-coordinate padding do not settle the separate two-variable Jacobian conjecture"

record KernelCounterexampleReceipt : Set where
  constructor kernelCounterexampleReceipt
  field
    polynomialSyntaxChecked : Bool
    symbolicDifferentiationChecked : Bool
    determinantIdentityKernelChecked : Bool
    threeExactPreimagesKernelChecked : Bool
    collisionImpliesNoninjectivityKernelChecked : Bool
    dimensionThreeConjectureRefuted : Bool
    paddingToEveryThreePlusTailChecked : Bool
    dimensionTwoClaimedSettled : Bool
    dimensionTwoClaimedSettledIsFalse : dimensionTwoClaimedSettled ≡ false

kernelCounterexampleReceipt : KernelCounterexampleReceipt
kernelCounterexampleReceipt =
  kernelCounterexampleReceipt
    true true true true true true true false refl
