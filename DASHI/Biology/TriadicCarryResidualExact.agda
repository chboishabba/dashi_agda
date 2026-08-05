module DASHI.Biology.TriadicCarryResidualExact where

open import DASHI.Core.Prelude
open import DASHI.Biology.TriadicKernelLiftQuotientExact

------------------------------------------------------------------------
-- Carryless cyclic addition and carry-aware balanced ternary are distinct.
-- The first is the exact finite-group analogue of bitwise XOR.  The second is
-- the hierarchical transducer in which unresolved local excess is transported
-- to the next digit depth.

data TriResidue : Set where
  residue0 : TriResidue
  residue1 : TriResidue
  residue2 : TriResidue

cyclicAdd3 : TriResidue → TriResidue → TriResidue
cyclicAdd3 residue0 residue0 = residue0
cyclicAdd3 residue0 residue1 = residue1
cyclicAdd3 residue0 residue2 = residue2
cyclicAdd3 residue1 residue0 = residue1
cyclicAdd3 residue1 residue1 = residue2
cyclicAdd3 residue1 residue2 = residue0
cyclicAdd3 residue2 residue0 = residue2
cyclicAdd3 residue2 residue1 = residue0
cyclicAdd3 residue2 residue2 = residue1

cyclicAdd3Commutative :
  (a b : TriResidue) → cyclicAdd3 a b ≡ cyclicAdd3 b a
cyclicAdd3Commutative residue0 residue0 = refl
cyclicAdd3Commutative residue0 residue1 = refl
cyclicAdd3Commutative residue0 residue2 = refl
cyclicAdd3Commutative residue1 residue0 = refl
cyclicAdd3Commutative residue1 residue1 = refl
cyclicAdd3Commutative residue1 residue2 = refl
cyclicAdd3Commutative residue2 residue0 = refl
cyclicAdd3Commutative residue2 residue1 = refl
cyclicAdd3Commutative residue2 residue2 = refl

cyclicAdd3Associative :
  (a b c : TriResidue) →
  cyclicAdd3 (cyclicAdd3 a b) c ≡ cyclicAdd3 a (cyclicAdd3 b c)
cyclicAdd3Associative residue0 residue0 residue0 = refl
cyclicAdd3Associative residue0 residue0 residue1 = refl
cyclicAdd3Associative residue0 residue0 residue2 = refl
cyclicAdd3Associative residue0 residue1 residue0 = refl
cyclicAdd3Associative residue0 residue1 residue1 = refl
cyclicAdd3Associative residue0 residue1 residue2 = refl
cyclicAdd3Associative residue0 residue2 residue0 = refl
cyclicAdd3Associative residue0 residue2 residue1 = refl
cyclicAdd3Associative residue0 residue2 residue2 = refl
cyclicAdd3Associative residue1 residue0 residue0 = refl
cyclicAdd3Associative residue1 residue0 residue1 = refl
cyclicAdd3Associative residue1 residue0 residue2 = refl
cyclicAdd3Associative residue1 residue1 residue0 = refl
cyclicAdd3Associative residue1 residue1 residue1 = refl
cyclicAdd3Associative residue1 residue1 residue2 = refl
cyclicAdd3Associative residue1 residue2 residue0 = refl
cyclicAdd3Associative residue1 residue2 residue1 = refl
cyclicAdd3Associative residue1 residue2 residue2 = refl
cyclicAdd3Associative residue2 residue0 residue0 = refl
cyclicAdd3Associative residue2 residue0 residue1 = refl
cyclicAdd3Associative residue2 residue0 residue2 = refl
cyclicAdd3Associative residue2 residue1 residue0 = refl
cyclicAdd3Associative residue2 residue1 residue1 = refl
cyclicAdd3Associative residue2 residue1 residue2 = refl
cyclicAdd3Associative residue2 residue2 residue0 = refl
cyclicAdd3Associative residue2 residue2 residue1 = refl
cyclicAdd3Associative residue2 residue2 residue2 = refl

cyclicAdd3DoesNotSelfCancel :
  cyclicAdd3 residue1 residue1 ≡ residue2
cyclicAdd3DoesNotSelfCancel = refl

------------------------------------------------------------------------
-- Differentiable/probabilistic semantics are represented algebraically by
-- cyclic convolution of three nonnegative masses.  Exact one-hot inputs return
-- the hard residue sum.

record Mass3 : Set where
  constructor mass3
  field
    mass0 : Nat
    mass1 : Nat
    mass2 : Nat

open Mass3 public

basisMass : TriResidue → Mass3
basisMass residue0 = mass3 1 0 0
basisMass residue1 = mass3 0 1 0
basisMass residue2 = mass3 0 0 1

cyclicConvolution : Mass3 → Mass3 → Mass3
cyclicConvolution p q =
  mass3
    ((mass0 p * mass0 q) + (mass1 p * mass2 q) + (mass2 p * mass1 q))
    ((mass0 p * mass1 q) + (mass1 p * mass0 q) + (mass2 p * mass2 q))
    ((mass0 p * mass2 q) + (mass1 p * mass1 q) + (mass2 p * mass0 q))

basisConvolutionExact :
  (a b : TriResidue) →
  cyclicConvolution (basisMass a) (basisMass b)
  ≡
  basisMass (cyclicAdd3 a b)
basisConvolutionExact residue0 residue0 = refl
basisConvolutionExact residue0 residue1 = refl
basisConvolutionExact residue0 residue2 = refl
basisConvolutionExact residue1 residue0 = refl
basisConvolutionExact residue1 residue1 = refl
basisConvolutionExact residue1 residue2 = refl
basisConvolutionExact residue2 residue0 = refl
basisConvolutionExact residue2 residue1 = refl
basisConvolutionExact residue2 residue2 = refl

------------------------------------------------------------------------
-- Seven possible integer totals of three balanced digits.

data Total7 : Set where
  totalMinus3 : Total7
  totalMinus2 : Total7
  totalMinus1 : Total7
  totalZero : Total7
  totalPlus1 : Total7
  totalPlus2 : Total7
  totalPlus3 : Total7

sumThreeTrits : KernelTrit → KernelTrit → KernelTrit → Total7
sumThreeTrits negativeTrit negativeTrit negativeTrit = totalMinus3
sumThreeTrits negativeTrit negativeTrit zeroTrit = totalMinus2
sumThreeTrits negativeTrit negativeTrit positiveTrit = totalMinus1
sumThreeTrits negativeTrit zeroTrit negativeTrit = totalMinus2
sumThreeTrits negativeTrit zeroTrit zeroTrit = totalMinus1
sumThreeTrits negativeTrit zeroTrit positiveTrit = totalZero
sumThreeTrits negativeTrit positiveTrit negativeTrit = totalMinus1
sumThreeTrits negativeTrit positiveTrit zeroTrit = totalZero
sumThreeTrits negativeTrit positiveTrit positiveTrit = totalPlus1
sumThreeTrits zeroTrit negativeTrit negativeTrit = totalMinus2
sumThreeTrits zeroTrit negativeTrit zeroTrit = totalMinus1
sumThreeTrits zeroTrit negativeTrit positiveTrit = totalZero
sumThreeTrits zeroTrit zeroTrit negativeTrit = totalMinus1
sumThreeTrits zeroTrit zeroTrit zeroTrit = totalZero
sumThreeTrits zeroTrit zeroTrit positiveTrit = totalPlus1
sumThreeTrits zeroTrit positiveTrit negativeTrit = totalZero
sumThreeTrits zeroTrit positiveTrit zeroTrit = totalPlus1
sumThreeTrits zeroTrit positiveTrit positiveTrit = totalPlus2
sumThreeTrits positiveTrit negativeTrit negativeTrit = totalMinus1
sumThreeTrits positiveTrit negativeTrit zeroTrit = totalZero
sumThreeTrits positiveTrit negativeTrit positiveTrit = totalPlus1
sumThreeTrits positiveTrit zeroTrit negativeTrit = totalZero
sumThreeTrits positiveTrit zeroTrit zeroTrit = totalPlus1
sumThreeTrits positiveTrit zeroTrit positiveTrit = totalPlus2
sumThreeTrits positiveTrit positiveTrit negativeTrit = totalPlus1
sumThreeTrits positiveTrit positiveTrit zeroTrit = totalPlus2
sumThreeTrits positiveTrit positiveTrit positiveTrit = totalPlus3

normalizeTotal : Total7 → KernelTrit × KernelTrit
normalizeTotal totalMinus3 = zeroTrit , negativeTrit
normalizeTotal totalMinus2 = positiveTrit , negativeTrit
normalizeTotal totalMinus1 = negativeTrit , zeroTrit
normalizeTotal totalZero = zeroTrit , zeroTrit
normalizeTotal totalPlus1 = positiveTrit , zeroTrit
normalizeTotal totalPlus2 = negativeTrit , positiveTrit
normalizeTotal totalPlus3 = zeroTrit , positiveTrit

recomposeDigitCarry : KernelTrit → KernelTrit → Total7
recomposeDigitCarry zeroTrit negativeTrit = totalMinus3
recomposeDigitCarry positiveTrit negativeTrit = totalMinus2
recomposeDigitCarry negativeTrit zeroTrit = totalMinus1
recomposeDigitCarry zeroTrit zeroTrit = totalZero
recomposeDigitCarry positiveTrit zeroTrit = totalPlus1
recomposeDigitCarry negativeTrit positiveTrit = totalPlus2
recomposeDigitCarry zeroTrit positiveTrit = totalPlus3
recomposeDigitCarry negativeTrit negativeTrit = totalMinus3
recomposeDigitCarry positiveTrit positiveTrit = totalPlus3

addCarry3 : KernelTrit → KernelTrit → KernelTrit → KernelTrit × KernelTrit
addCarry3 x y carry = normalizeTotal (sumThreeTrits x y carry)

carryReconstruction :
  (x y carry : KernelTrit) →
  recomposeDigitCarry
    (proj₁ (addCarry3 x y carry))
    (proj₂ (addCarry3 x y carry))
  ≡
  sumThreeTrits x y carry
carryReconstruction negativeTrit negativeTrit negativeTrit = refl
carryReconstruction negativeTrit negativeTrit zeroTrit = refl
carryReconstruction negativeTrit negativeTrit positiveTrit = refl
carryReconstruction negativeTrit zeroTrit negativeTrit = refl
carryReconstruction negativeTrit zeroTrit zeroTrit = refl
carryReconstruction negativeTrit zeroTrit positiveTrit = refl
carryReconstruction negativeTrit positiveTrit negativeTrit = refl
carryReconstruction negativeTrit positiveTrit zeroTrit = refl
carryReconstruction negativeTrit positiveTrit positiveTrit = refl
carryReconstruction zeroTrit negativeTrit negativeTrit = refl
carryReconstruction zeroTrit negativeTrit zeroTrit = refl
carryReconstruction zeroTrit negativeTrit positiveTrit = refl
carryReconstruction zeroTrit zeroTrit negativeTrit = refl
carryReconstruction zeroTrit zeroTrit zeroTrit = refl
carryReconstruction zeroTrit zeroTrit positiveTrit = refl
carryReconstruction zeroTrit positiveTrit negativeTrit = refl
carryReconstruction zeroTrit positiveTrit zeroTrit = refl
carryReconstruction zeroTrit positiveTrit positiveTrit = refl
carryReconstruction positiveTrit negativeTrit negativeTrit = refl
carryReconstruction positiveTrit negativeTrit zeroTrit = refl
carryReconstruction positiveTrit negativeTrit positiveTrit = refl
carryReconstruction positiveTrit zeroTrit negativeTrit = refl
carryReconstruction positiveTrit zeroTrit zeroTrit = refl
carryReconstruction positiveTrit zeroTrit positiveTrit = refl
carryReconstruction positiveTrit positiveTrit negativeTrit = refl
carryReconstruction positiveTrit positiveTrit zeroTrit = refl
carryReconstruction positiveTrit positiveTrit positiveTrit = refl

negateDigitCarry : KernelTrit × KernelTrit → KernelTrit × KernelTrit
negateDigitCarry (digit , carry) = negateTrit digit , negateTrit carry

addCarryNegationEquivariant :
  (x y carry : KernelTrit) →
  addCarry3 (negateTrit x) (negateTrit y) (negateTrit carry)
  ≡
  negateDigitCarry (addCarry3 x y carry)
addCarryNegationEquivariant negativeTrit negativeTrit negativeTrit = refl
addCarryNegationEquivariant negativeTrit negativeTrit zeroTrit = refl
addCarryNegationEquivariant negativeTrit negativeTrit positiveTrit = refl
addCarryNegationEquivariant negativeTrit zeroTrit negativeTrit = refl
addCarryNegationEquivariant negativeTrit zeroTrit zeroTrit = refl
addCarryNegationEquivariant negativeTrit zeroTrit positiveTrit = refl
addCarryNegationEquivariant negativeTrit positiveTrit negativeTrit = refl
addCarryNegationEquivariant negativeTrit positiveTrit zeroTrit = refl
addCarryNegationEquivariant negativeTrit positiveTrit positiveTrit = refl
addCarryNegationEquivariant zeroTrit negativeTrit negativeTrit = refl
addCarryNegationEquivariant zeroTrit negativeTrit zeroTrit = refl
addCarryNegationEquivariant zeroTrit negativeTrit positiveTrit = refl
addCarryNegationEquivariant zeroTrit zeroTrit negativeTrit = refl
addCarryNegationEquivariant zeroTrit zeroTrit zeroTrit = refl
addCarryNegationEquivariant zeroTrit zeroTrit positiveTrit = refl
addCarryNegationEquivariant zeroTrit positiveTrit negativeTrit = refl
addCarryNegationEquivariant zeroTrit positiveTrit zeroTrit = refl
addCarryNegationEquivariant zeroTrit positiveTrit positiveTrit = refl
addCarryNegationEquivariant positiveTrit negativeTrit negativeTrit = refl
addCarryNegationEquivariant positiveTrit negativeTrit zeroTrit = refl
addCarryNegationEquivariant positiveTrit negativeTrit positiveTrit = refl
addCarryNegationEquivariant positiveTrit zeroTrit negativeTrit = refl
addCarryNegationEquivariant positiveTrit zeroTrit zeroTrit = refl
addCarryNegationEquivariant positiveTrit zeroTrit positiveTrit = refl
addCarryNegationEquivariant positiveTrit positiveTrit negativeTrit = refl
addCarryNegationEquivariant positiveTrit positiveTrit zeroTrit = refl
addCarryNegationEquivariant positiveTrit positiveTrit positiveTrit = refl

positiveOverflowLifts :
  addCarry3 positiveTrit positiveTrit zeroTrit
  ≡
  (negativeTrit , positiveTrit)
positiveOverflowLifts = refl

negativeOverflowLifts :
  addCarry3 negativeTrit negativeTrit zeroTrit
  ≡
  (positiveTrit , negativeTrit)
negativeOverflowLifts = refl

record TriadicCarryBoundary : Set where
  constructor triadicCarryBoundary
  field
    residueTwoIntrinsicallyMeansBothTrue : Bool
    residueTwoIntrinsicallyMeansBothTrueIsFalse :
      residueTwoIntrinsicallyMeansBothTrue ≡ false

    carrylessAdditionEqualsThreeAdicAddition : Bool
    carrylessAdditionEqualsThreeAdicAdditionIsFalse :
      carrylessAdditionEqualsThreeAdicAddition ≡ false

    carryRecordsCrossDepthResidual : Bool
    carryRecordsCrossDepthResidualIsTrue :
      carryRecordsCrossDepthResidual ≡ true

open TriadicCarryBoundary public

canonicalTriadicCarryBoundary : TriadicCarryBoundary
canonicalTriadicCarryBoundary =
  triadicCarryBoundary false refl false refl true refl
