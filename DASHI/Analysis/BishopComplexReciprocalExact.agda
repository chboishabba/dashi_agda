module DASHI.Analysis.BishopComplexReciprocalExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE RECIPROCAL ON THE BISHOP COMPLEX SETOID
--
-- A Bishop complex number is certified nonzero by strict positivity of its
-- norm square.  The reciprocal is the usual conjugate divided by normSq:
--
--     z^{-1} = conjugate(z) / normSq(z).
--
-- This keeps the proof witness out of semantic identity and stays entirely on
-- the same Bishop complex carrier used by the Eisenstein q-series theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Product using (_,_)
open import Data.Rational.Unnormalised using (_/_)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

conjugateC : Complex.BishopComplex → Complex.BishopComplex
conjugateC (Complex.complex a b) =
  Complex.complex a (BishopReal.- b)

record BishopComplexNonzero (z : Complex.BishopComplex) : Set where
  field
    normSquarePositive :
      BishopReal._<_ BishopReal.0ℝ (Norm.normSqC z)

open BishopComplexNonzero public

normSquareNonzero :
  ∀ {z} →
  BishopComplexNonzero z →
  BishopReal._≄0 (Norm.normSqC z)
normSquareNonzero nz =
  Reciprocal.xNonzero (normSquarePositive nz)

reciprocalC :
  (z : Complex.BishopComplex) →
  BishopComplexNonzero z →
  Complex.BishopComplex
reciprocalC z nz =
  Algebra.scaleC
    (BishopInverse._⁻¹ (Norm.normSqC z) (normSquareNonzero nz))
    (conjugateC z)

multiplyConjugate :
  ∀ z →
  Complex._≈C_
    (Algebra._*C_ z (conjugateC z))
    (Complex.complex (Norm.normSqC z) BishopReal.0ℝ)
multiplyConjugate (Complex.complex a b) =
  let open BishopP.ℝ-Solver
  in
  solve 2
    (λ a′ b′ →
      (a′ ⊗ a′ ⊕ (⊝ (b′ ⊗ (⊝ b′))))
      ⊜ (a′ ⊗ a′) ⊕ (b′ ⊗ b′))
    BishopP.≃-refl a b
  ,
  solve 2
    (λ a′ b′ →
      (a′ ⊗ (⊝ b′)) ⊕ (b′ ⊗ a′)
      ⊜ Κ (+ 0 / 1))
    BishopP.≃-refl a b

multiplyReciprocal :
  ∀ z (nz : BishopComplexNonzero z) →
  Complex._≈C_
    (Algebra._*C_ z (reciprocalC z nz))
    Algebra.oneC
multiplyReciprocal (Complex.complex a b) nz =
  let
    d = Norm.normSqC (Complex.complex a b)
    dInv = BishopInverse._⁻¹ d (normSquareNonzero nz)
    inverseLaw = BishopInverse.*-inverseʳ d (normSquareNonzero nz)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ a′ b′ inv →
        (a′ ⊗ (inv ⊗ a′)) ⊕
        (⊝ (b′ ⊗ (inv ⊗ (⊝ b′))))
        ⊜ inv ⊗ ((a′ ⊗ a′) ⊕ (b′ ⊗ b′)))
      BishopP.≃-refl a b dInv)
    (BishopP.≃-trans
      (BishopP.*-comm dInv d)
      inverseLaw)
  ,
  solve 3
    (λ a′ b′ inv →
      (a′ ⊗ (inv ⊗ (⊝ b′))) ⊕
      (b′ ⊗ (inv ⊗ a′))
      ⊜ Κ (+ 0 / 1))
    BishopP.≃-refl a b dInv

normSquareConjugate :
  (z : Complex.BishopComplex) →
  BishopReal._≃_
    (Norm.normSqC (conjugateC z))
    (Norm.normSqC z)
normSquareConjugate (Complex.complex a b) =
  let open BishopP.ℝ-Solver in
  solve 2
    (λ a′ b′ →
      (a′ ⊗ a′) ⊕ ((⊝ b′) ⊗ (⊝ b′))
      ⊜
      (a′ ⊗ a′) ⊕ (b′ ⊗ b′))
    BishopP.≃-refl a b

normSquareScale :
  (scalar : BishopReal.ℝ) →
  (z : Complex.BishopComplex) →
  BishopReal._≃_
    (Norm.normSqC (Algebra.scaleC scalar z))
    (BishopReal._*_
      (Norm.square scalar)
      (Norm.normSqC z))
normSquareScale scalar (Complex.complex a b) =
  let open BishopP.ℝ-Solver in
  solve 3
    (λ s a′ b′ →
      ((s ⊗ a′) ⊗ (s ⊗ a′))
      ⊕ ((s ⊗ b′) ⊗ (s ⊗ b′))
      ⊜
      (s ⊗ s)
      ⊗ ((a′ ⊗ a′) ⊕ (b′ ⊗ b′)))
    BishopP.≃-refl scalar a b

normSquareReciprocal :
  (z : Complex.BishopComplex) →
  (nz : BishopComplexNonzero z) →
  BishopReal._≃_
    (Norm.normSqC (reciprocalC z nz))
    (BishopInverse._⁻¹
      (Norm.normSqC z)
      (normSquareNonzero nz))
normSquareReciprocal z nz =
  let
    d = Norm.normSqC z
    inv = BishopInverse._⁻¹ d (normSquareNonzero nz)
    inverseLaw = BishopInverse.*-inverseʳ d (normSquareNonzero nz)

    regroup :
      BishopReal._≃_
        (BishopReal._*_
          (Norm.square inv)
          d)
        (BishopReal._*_
          inv
          (BishopReal._*_ d inv))
    regroup =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ d′ inv′ →
          (inv′ ⊗ inv′) ⊗ d′
          ⊜ inv′ ⊗ (d′ ⊗ inv′))
        BishopP.≃-refl d inv
  in
  BishopP.≃-trans
    (normSquareScale inv (conjugateC z))
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (normSquareConjugate z))
      (BishopP.≃-trans
        regroup
        (BishopP.≃-trans
          (BishopP.*-congˡ inverseLaw)
          (BishopP.*-identityʳ inv))))

reciprocalNormSquarePositive :
  (z : Complex.BishopComplex) →
  (nz : BishopComplexNonzero z) →
  BishopReal._<_ BishopReal.0ℝ
    (Norm.normSqC (reciprocalC z nz))
reciprocalNormSquarePositive z nz =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm (normSquareReciprocal z nz))
    (BishopInverse.0<x⇒0<x⁻¹
      (normSquareNonzero nz)
      (normSquarePositive nz))

reciprocalPower :
  (z : Complex.BishopComplex) →
  BishopComplexNonzero z →
  Nat →
  Complex.BishopComplex
reciprocalPower z nz exponent =
  Algebra.powC (reciprocalC z nz) exponent
