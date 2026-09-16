module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4PermutationCharacterKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4CharacterBridgeExact as Runtime

------------------------------------------------------------------------
-- KERNEL-VISIBLE D4 PERMUTATION CHARACTER ON THE FIVE INNER ORBITS
--
-- The phase-preserving ternary-27 reduction keeps one outer trit and sends the
-- inner nine-state sheet to Triadic.NineOrbit.  This owner writes the next
-- finite theorem candidate directly in Agda: the ordinary square symmetries
-- act on those five orbit constructors with fixed-point character
--
--   e, r^2, {r,r^3}, axis reflections, diagonal reflections
--   5,   5,       1,                3,                    3.
--
-- The Python owner already discovered that this character decomposes as
-- 3 A1 + B1 + B2.  This file intentionally stops one step earlier: it writes
-- the permutation action/character as Agda source, but does not promote source
-- to an observed kernel receipt, does not import the Python decomposition as a
-- kernel theorem, and does not create Monster-42d action authority.
------------------------------------------------------------------------

data D4Element : Set where
  identity : D4Element
  quarterTurn : D4Element
  halfTurn : D4Element
  threeQuarterTurn : D4Element
  reflectX : D4Element
  reflectY : D4Element
  reflectDiagonal : D4Element
  reflectAntiDiagonal : D4Element

actOrbit : D4Element → Triadic.NineOrbit → Triadic.NineOrbit
actOrbit identity o = o
actOrbit halfTurn o = o

actOrbit quarterTurn Triadic.zeroOrbit = Triadic.zeroOrbit
actOrbit quarterTurn Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
actOrbit quarterTurn Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
actOrbit quarterTurn Triadic.equalSignOrbit = Triadic.oppositeSignOrbit
actOrbit quarterTurn Triadic.oppositeSignOrbit = Triadic.equalSignOrbit

actOrbit threeQuarterTurn Triadic.zeroOrbit = Triadic.zeroOrbit
actOrbit threeQuarterTurn Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
actOrbit threeQuarterTurn Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
actOrbit threeQuarterTurn Triadic.equalSignOrbit = Triadic.oppositeSignOrbit
actOrbit threeQuarterTurn Triadic.oppositeSignOrbit = Triadic.equalSignOrbit

actOrbit reflectX Triadic.zeroOrbit = Triadic.zeroOrbit
actOrbit reflectX Triadic.firstAxisOrbit = Triadic.firstAxisOrbit
actOrbit reflectX Triadic.secondAxisOrbit = Triadic.secondAxisOrbit
actOrbit reflectX Triadic.equalSignOrbit = Triadic.oppositeSignOrbit
actOrbit reflectX Triadic.oppositeSignOrbit = Triadic.equalSignOrbit

actOrbit reflectY Triadic.zeroOrbit = Triadic.zeroOrbit
actOrbit reflectY Triadic.firstAxisOrbit = Triadic.firstAxisOrbit
actOrbit reflectY Triadic.secondAxisOrbit = Triadic.secondAxisOrbit
actOrbit reflectY Triadic.equalSignOrbit = Triadic.oppositeSignOrbit
actOrbit reflectY Triadic.oppositeSignOrbit = Triadic.equalSignOrbit

actOrbit reflectDiagonal Triadic.zeroOrbit = Triadic.zeroOrbit
actOrbit reflectDiagonal Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
actOrbit reflectDiagonal Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
actOrbit reflectDiagonal Triadic.equalSignOrbit = Triadic.equalSignOrbit
actOrbit reflectDiagonal Triadic.oppositeSignOrbit = Triadic.oppositeSignOrbit

actOrbit reflectAntiDiagonal Triadic.zeroOrbit = Triadic.zeroOrbit
actOrbit reflectAntiDiagonal Triadic.firstAxisOrbit = Triadic.secondAxisOrbit
actOrbit reflectAntiDiagonal Triadic.secondAxisOrbit = Triadic.firstAxisOrbit
actOrbit reflectAntiDiagonal Triadic.equalSignOrbit = Triadic.equalSignOrbit
actOrbit reflectAntiDiagonal Triadic.oppositeSignOrbit = Triadic.oppositeSignOrbit

orbitEq : Triadic.NineOrbit → Triadic.NineOrbit → Bool
orbitEq Triadic.zeroOrbit Triadic.zeroOrbit = true
orbitEq Triadic.firstAxisOrbit Triadic.firstAxisOrbit = true
orbitEq Triadic.secondAxisOrbit Triadic.secondAxisOrbit = true
orbitEq Triadic.equalSignOrbit Triadic.equalSignOrbit = true
orbitEq Triadic.oppositeSignOrbit Triadic.oppositeSignOrbit = true
orbitEq _ _ = false

boolNat : Bool → Nat
boolNat false = zero
boolNat true = suc zero

isFixed : D4Element → Triadic.NineOrbit → Bool
isFixed g o = orbitEq (actOrbit g o) o

fixedOrbitCount : D4Element → Nat
fixedOrbitCount g =
  boolNat (isFixed g Triadic.zeroOrbit)
  + boolNat (isFixed g Triadic.firstAxisOrbit)
  + boolNat (isFixed g Triadic.secondAxisOrbit)
  + boolNat (isFixed g Triadic.equalSignOrbit)
  + boolNat (isFixed g Triadic.oppositeSignOrbit)

identityFixedOrbitCount : Nat
identityFixedOrbitCount = fixedOrbitCount identity

halfTurnFixedOrbitCount : Nat
halfTurnFixedOrbitCount = fixedOrbitCount halfTurn

quarterTurnFixedOrbitCount : Nat
quarterTurnFixedOrbitCount = fixedOrbitCount quarterTurn

threeQuarterTurnFixedOrbitCount : Nat
threeQuarterTurnFixedOrbitCount = fixedOrbitCount threeQuarterTurn

axisReflectionFixedOrbitCount : Nat
axisReflectionFixedOrbitCount = fixedOrbitCount reflectX

yAxisReflectionFixedOrbitCount : Nat
yAxisReflectionFixedOrbitCount = fixedOrbitCount reflectY

diagonalReflectionFixedOrbitCount : Nat
diagonalReflectionFixedOrbitCount = fixedOrbitCount reflectDiagonal

antiDiagonalReflectionFixedOrbitCount : Nat
antiDiagonalReflectionFixedOrbitCount = fixedOrbitCount reflectAntiDiagonal

identityFixedOrbitCountIsFive : identityFixedOrbitCount ≡ 5
identityFixedOrbitCountIsFive = refl

halfTurnFixedOrbitCountIsFive : halfTurnFixedOrbitCount ≡ 5
halfTurnFixedOrbitCountIsFive = refl

quarterTurnFixedOrbitCountIsOne : quarterTurnFixedOrbitCount ≡ 1
quarterTurnFixedOrbitCountIsOne = refl

threeQuarterTurnFixedOrbitCountIsOne : threeQuarterTurnFixedOrbitCount ≡ 1
threeQuarterTurnFixedOrbitCountIsOne = refl

axisReflectionFixedOrbitCountIsThree : axisReflectionFixedOrbitCount ≡ 3
axisReflectionFixedOrbitCountIsThree = refl

yAxisReflectionFixedOrbitCountIsThree : yAxisReflectionFixedOrbitCount ≡ 3
yAxisReflectionFixedOrbitCountIsThree = refl

diagonalReflectionFixedOrbitCountIsThree : diagonalReflectionFixedOrbitCount ≡ 3
diagonalReflectionFixedOrbitCountIsThree = refl

antiDiagonalReflectionFixedOrbitCountIsThree : antiDiagonalReflectionFixedOrbitCount ≡ 3
antiDiagonalReflectionFixedOrbitCountIsThree = refl

permutationCharacter : List Nat
permutationCharacter =
  identityFixedOrbitCount
  ∷ halfTurnFixedOrbitCount
  ∷ quarterTurnFixedOrbitCount
  ∷ axisReflectionFixedOrbitCount
  ∷ diagonalReflectionFixedOrbitCount
  ∷ []

runtimeBridgeBoundary : Runtime.FiveOrbitD4CharacterBoundary
runtimeBridgeBoundary = Runtime.currentFiveOrbitD4CharacterBoundary

reductionBoundary : Reduction.Ternary27PhasePreservingReductionBoundary
reductionBoundary = Reduction.currentTernary27PhasePreservingReductionBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data KernelPermutationCharacterCreatesIrrepDecomposition : Set where
data KernelPermutationCharacterCreatesMonster42dAction : Set where

kernelPermutationCharacterDoesNotCreateIrrepDecomposition :
  KernelPermutationCharacterCreatesIrrepDecomposition → ⊥
kernelPermutationCharacterDoesNotCreateIrrepDecomposition ()

kernelPermutationCharacterDoesNotCreateMonster42dAction :
  KernelPermutationCharacterCreatesMonster42dAction → ⊥
kernelPermutationCharacterDoesNotCreateMonster42dAction ()

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

record FiveOrbitD4PermutationKernelBoundary : Set where
  constructor five-orbit-d4-permutation-kernel-boundary
  field
    phasePreservingThreeTimesFiveReductionSourcePaid : Bool
    explicitFiveOrbitD4ActionWritten : Bool
    agdaKernelPermutationCharacterSourceWritten : Bool
    agdaKernelPermutationCharacterObserved : Bool
    runtimeIrrepDecompositionRetained : Bool
    agdaKernelIrrepDecompositionObserved : Bool
    characterBridgeCreatesMonster42dAction : Bool
    nextResidual : String
open FiveOrbitD4PermutationKernelBoundary public

currentFiveOrbitD4PermutationKernelBoundary : FiveOrbitD4PermutationKernelBoundary
currentFiveOrbitD4PermutationKernelBoundary =
  five-orbit-d4-permutation-kernel-boundary
    true true true false true false false
    "Run the Agda validation to obtain a kernel receipt for the explicit five-orbit D4 action and permutation character (5,5,1,3,3). Separately kernelize the signed D4 character arithmetic proving irreducible multiplicities 3*A1 + B1 + B2 and zero A2/E. Keep the orbit constructors distinct from irrep labels, and keep all Monster class-42d action/representation identification separately unpaid."
