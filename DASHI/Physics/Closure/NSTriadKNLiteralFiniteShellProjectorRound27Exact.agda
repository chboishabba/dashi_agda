module DASHI.Physics.Closure.NSTriadKNLiteralFiniteShellProjectorRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Audrey Terras.
-- Title: "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Construct the sharp finite shell selectors needed before differentiating a
-- filtered Galerkin trajectory.  The coefficient is the Kronecker indicator
-- of the repository's literal dyadic shell index.  We prove pointwise
-- idempotence, pairwise disjointness for unequal shell labels, finite identity
-- resolution inside a declared maximum shell, covariance under every mode map
-- preserving shell index, and commutation with arbitrary diagonal rational
-- multipliers.
--
-- This is a sharp finite projector algebra.  It does not claim the smooth
-- Littlewood--Paley multiplier bounds or continuum norm equivalence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc right) = false
natEqual (suc left) zero = false
natEqual (suc left) (suc right) = natEqual left right

natEqualRefl : ∀ value → natEqual value value ≡ true
natEqualRefl zero = refl
natEqualRefl (suc value) = natEqualRefl value

boolCoefficient : Bool → Nat
boolCoefficient false = 0
boolCoefficient true = 1

shellProjectorCoefficient : Nat → Z3.FourierMode → Nat
shellProjectorCoefficient shell mode =
  boolCoefficient (natEqual shell (Shell.shellIndex mode))

shellProjectorIdempotent : ∀ shell mode →
  shellProjectorCoefficient shell mode
  * shellProjectorCoefficient shell mode
  ≡ shellProjectorCoefficient shell mode
shellProjectorIdempotent shell mode
  with natEqual shell (Shell.shellIndex mode)
... | false = refl
... | true = refl

deltaDisjoint : ∀ left right selected →
  natEqual left right ≡ false →
  boolCoefficient (natEqual left selected)
  * boolCoefficient (natEqual right selected)
  ≡ 0
deltaDisjoint zero zero selected ()
deltaDisjoint zero (suc right) zero proof = refl
deltaDisjoint zero (suc right) (suc selected) proof = refl
deltaDisjoint (suc left) zero zero proof = refl
deltaDisjoint (suc left) zero (suc selected) proof = refl
deltaDisjoint (suc left) (suc right) zero proof = refl
deltaDisjoint (suc left) (suc right) (suc selected) proof =
  deltaDisjoint left right selected proof

shellProjectorDisjointOutsideShell : ∀ left right mode →
  natEqual left right ≡ false →
  shellProjectorCoefficient left mode
  * shellProjectorCoefficient right mode
  ≡ 0
shellProjectorDisjointOutsideShell left right mode =
  deltaDisjoint left right (Shell.shellIndex mode)

shellProjectorOwnShell : ∀ mode →
  shellProjectorCoefficient (Shell.shellIndex mode) mode ≡ 1
shellProjectorOwnShell mode
  rewrite natEqualRefl (Shell.shellIndex mode) = refl

------------------------------------------------------------------------
-- Finite resolution coefficient for the shell labels 0,...,maximum.
------------------------------------------------------------------------

shellResolutionCoefficient : Nat → Nat → Nat
shellResolutionCoefficient zero zero = 1
shellResolutionCoefficient zero (suc shell) = 0
shellResolutionCoefficient (suc maximum) zero = 1
shellResolutionCoefficient (suc maximum) (suc shell) =
  shellResolutionCoefficient maximum shell

shellResolutionInsideMaximum : ∀ {shell maximum} →
  shell ≤ maximum →
  shellResolutionCoefficient maximum shell ≡ 1
shellResolutionInsideMaximum {zero} {zero} proof = refl
shellResolutionInsideMaximum {zero} {suc maximum} proof = refl
shellResolutionInsideMaximum {suc shell} {zero} ()
shellResolutionInsideMaximum {suc shell} {suc maximum} (s≤s proof) =
  shellResolutionInsideMaximum proof

finiteShellProjectorResolution : ∀ maximum mode →
  Shell.shellIndex mode ≤ maximum →
  shellResolutionCoefficient maximum (Shell.shellIndex mode) ≡ 1
finiteShellProjectorResolution maximum mode = shellResolutionInsideMaximum

------------------------------------------------------------------------
-- Covariance under any mode transformation preserving the literal shell.
-- The theorem is directly reusable for Fourier reality once shell-index
-- invariance under k ↦ -k is supplied by the lattice geometry layer.
------------------------------------------------------------------------

record ShellIndexPreservingMap : Set where
  constructor shell-index-preserving-map
  field
    transform : Z3.FourierMode → Z3.FourierMode
    preservesShellIndex : ∀ mode →
      Shell.shellIndex (transform mode) ≡ Shell.shellIndex mode

open ShellIndexPreservingMap public

shellProjectorCovariant :
  (map : ShellIndexPreservingMap) →
  ∀ shell mode →
  shellProjectorCoefficient shell (transform map mode)
  ≡ shellProjectorCoefficient shell mode
shellProjectorCovariant map shell mode
  rewrite preservesShellIndex map mode = refl

shellProjectorRealityCovariant :
  (negationLaw : ∀ mode →
    Shell.shellIndex (Z3.negateMode mode) ≡ Shell.shellIndex mode) →
  ∀ shell mode →
  shellProjectorCoefficient shell (Z3.negateMode mode)
  ≡ shellProjectorCoefficient shell mode
shellProjectorRealityCovariant negationLaw shell mode
  rewrite negationLaw mode = refl

------------------------------------------------------------------------
-- A sharp shell selector is a diagonal multiplier, hence commutes exactly
-- with every other diagonal multiplier.  This is the finite coefficient-level
-- precursor of commutation with the Laplacian and Leray symbols.
------------------------------------------------------------------------

zeroQ oneQ : ℚ
zeroQ = Int.+ 0 / 1
oneQ = Int.+ 1 / 1

shellProjectorScalar : Nat → Z3.FourierMode → ℚ
shellProjectorScalar shell mode
  with natEqual shell (Shell.shellIndex mode)
... | false = zeroQ
... | true = oneQ

shellProjectorCommutesWithDiagonalMultiplier :
  ∀ shell mode multiplier value →
  shellProjectorScalar shell mode * (multiplier * value)
  ≡ multiplier * (shellProjectorScalar shell mode * value)
shellProjectorCommutesWithDiagonalMultiplier shell mode multiplier value
  with natEqual shell (Shell.shellIndex mode)
... | false = solve (multiplier ∷ value ∷ [])
... | true = solve (multiplier ∷ value ∷ [])

literalSharpShellProjectorAlgebraClosed : Bool
literalSharpShellProjectorAlgebraClosed = true

smoothLittlewoodPaleyOperatorBoundsClosed : Bool
smoothLittlewoodPaleyOperatorBoundsClosed = false
