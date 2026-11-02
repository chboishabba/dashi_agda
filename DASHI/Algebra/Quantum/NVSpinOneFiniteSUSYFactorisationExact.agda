module DASHI.Algebra.Quantum.NVSpinOneFiniteSUSYFactorisationExact where

-- FINITE SUSY QUANTUM MECHANICS, NOT SPACETIME SUSY.
-- Reuses the existing spin-one label chart, C3 carrier and Sz² profile.
-- Conventional algebra: H = {Q, Q†}, Q² = (Q†)² = 0,
-- with a grading where the two positive-energy levels form one
-- opposite-parity pair and the unique zero-energy level is unpaired.
--
-- This factorisation is a mathematical *choice* of supercharge for an
-- idealized D Sz² operator. It does not establish physical SUSY of a
-- diamond NV centre, nor a superpartner in the Standard Model.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.Quantum.NVSpinOneC3HamiltonianObstructionExact as NV
import DASHI.Physics.QFT.WittenIndexSUSYBoundarySurface as QFTBoundary

Level : Set
Level = C3.C3

-- Finite 3x3 natural-matrix kernel, with row = output, col = input.
Matrix : Set
Matrix = Level → Level → Nat

q : Matrix
q C3.c2 C3.c0 = 1
q _ _ = 0

qDagger : Matrix
qDagger C3.c0 C3.c2 = 1
qDagger _ _ = 0

-- Finite index summation over the exact, existing three-element carrier.
product : Matrix → Matrix → Matrix
product a b i j =
  a i C3.c0 * b C3.c0 j +
  a i C3.c1 * b C3.c1 j +
  a i C3.c2 * b C3.c2 j

zeroMatrix : Matrix
zeroMatrix _ _ = 0

anticommutator : Matrix
anticommutator i j = product q qDagger i j + product qDagger q i j

szSquaredDiagonal : Matrix
szSquaredDiagonal C3.c0 C3.c0 = 1
szSquaredDiagonal C3.c2 C3.c2 = 1
szSquaredDiagonal _ _ = 0

-- Nilpotent supercharges; finite enumeration proves every matrix entry.
qNilpotent : ∀ i j → product q q i j ≡ zeroMatrix i j
qNilpotent C3.c0 C3.c0 = refl
qNilpotent C3.c0 C3.c1 = refl
qNilpotent C3.c0 C3.c2 = refl
qNilpotent C3.c1 C3.c0 = refl
qNilpotent C3.c1 C3.c1 = refl
qNilpotent C3.c1 C3.c2 = refl
qNilpotent C3.c2 C3.c0 = refl
qNilpotent C3.c2 C3.c1 = refl
qNilpotent C3.c2 C3.c2 = refl

qDaggerNilpotent : ∀ i j →
  product qDagger qDagger i j ≡ zeroMatrix i j
qDaggerNilpotent C3.c0 C3.c0 = refl
qDaggerNilpotent C3.c0 C3.c1 = refl
qDaggerNilpotent C3.c0 C3.c2 = refl
qDaggerNilpotent C3.c1 C3.c0 = refl
qDaggerNilpotent C3.c1 C3.c1 = refl
qDaggerNilpotent C3.c1 C3.c2 = refl
qDaggerNilpotent C3.c2 C3.c0 = refl
qDaggerNilpotent C3.c2 C3.c1 = refl
qDaggerNilpotent C3.c2 C3.c2 = refl

-- This is the EXACT 3-by-3 matrix equality {Q,Q†} = Sz².
susyHamiltonianEqualsSzSquared : ∀ i j →
  anticommutator i j ≡ szSquaredDiagonal i j
susyHamiltonianEqualsSzSquared C3.c0 C3.c0 = refl
susyHamiltonianEqualsSzSquared C3.c0 C3.c1 = refl
susyHamiltonianEqualsSzSquared C3.c0 C3.c2 = refl
susyHamiltonianEqualsSzSquared C3.c1 C3.c0 = refl
susyHamiltonianEqualsSzSquared C3.c1 C3.c1 = refl
susyHamiltonianEqualsSzSquared C3.c1 C3.c2 = refl
susyHamiltonianEqualsSzSquared C3.c2 C3.c0 = refl
susyHamiltonianEqualsSzSquared C3.c2 C3.c1 = refl
susyHamiltonianEqualsSzSquared C3.c2 C3.c2 = refl

-- Explicit Z2 grading: c0,c1 even; c2 odd.
even : Level → Bool
even C3.c0 = true
even C3.c1 = true
even C3.c2 = false

-- Positive-energy spectrum: c0 and c2 form a paired doublet.
-- c1 is an even zero-energy state. Hence n_even_zero=1,
-- n_odd_zero=0, and the finite Witten index is +1.
evenZeroModes : Nat
evenZeroModes = 1

oddZeroModes : Nat
oddZeroModes = 0

wittenIndexFinite : Nat
wittenIndexFinite = 1

finiteIndexWitness :
  evenZeroModes ≡ suc oddZeroModes
finiteIndexWitness = refl

-- The existing QFT SUSY boundary is intentionally NOT instantiated:
-- its postulated background/spin structures and field-theoretic targets
-- cannot be discharged by a 3-level quantum-mechanical factorisation.

-- Exact *Zeeman term* obstruction (dimensionless spin eigenvalues 1,0,-1
-- encoded with a shifted nonnegative profile 2,1,0).
-- An additive constant does not affect commutation with Q, and the
-- following explicit pair is enough to refute a universal commutator law.
zeemanShifted : Matrix
zeemanShifted C3.c0 C3.c0 = 2
zeemanShifted C3.c1 C3.c1 = 1
zeemanShifted _ _ = 0

zeemanTimesQAtMinusPlus :
  product zeemanShifted q C3.c2 C3.c0 ≡ 0
zeemanTimesQAtMinusPlus = refl

qTimesZeemanAtMinusPlus :
  product q zeemanShifted C3.c2 C3.c0 ≡ 2
qTimesZeemanAtMinusPlus = refl

-- A nonzero axial Zeeman splitting spoils conservation of this Q.
notEveryAxialZeemanCommutesWithQ :
  (∀ i j → product zeemanShifted q i j ≡ product q zeemanShifted i j)
  → (0 ≡ 2)
notEveryAxialZeemanCommutesWithQ commute =
  commute C3.c2 C3.c0
