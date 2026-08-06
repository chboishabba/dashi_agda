module DASHI.Physics.Closure.NSTriadKNLuoFiniteRootOfUnityCancellationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Prove the algebraic core of one-dimensional cyclic-character cancellation.
-- For a scalar root z and M=cutoff+1,
--
--   (1-z) sum_{x=0}^{M-1} z^x = 1-z^M.
--
-- If z^M=1 and 1-z has a supplied multiplicative inverse, the finite
-- geometric sum is zero. The proof uses the repository's checked geometric
-- identity and performs the cancellation explicitly. The concrete z=-1,
-- M=2 instance is included as a regression. Constructing primitive complex
-- roots for arbitrary M remains the separate scalar-carrier embedding.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

record InvertibleFiniteRoot : Set where
  constructor invertible-finite-root
  field
    root inverseOneMinusRoot : ℚ
    cutoff : Nat
    rootPeriod : Geo.pow root (suc cutoff) ≡ 1ℚ
    inverseMeaning : inverseOneMinusRoot * (1ℚ - root) ≡ 1ℚ

open InvertibleFiniteRoot public

finiteRootGeometricSumZero :
  (dataSet : InvertibleFiniteRoot) →
  Geo.partialSum (root dataSet) (cutoff dataSet) ≡ 0ℚ
finiteRootGeometricSumZero dataSet =
  let
    geometric = Geo.geometricIdentity (root dataSet) (cutoff dataSet)

    rightZero :
      1ℚ - Geo.pow (root dataSet) (suc (cutoff dataSet)) ≡ 0ℚ
    rightZero =
      trans
        (cong (1ℚ -_) (rootPeriod dataSet))
        (solve [])

    scaledZero :
      (1ℚ - root dataSet)
        * Geo.partialSum (root dataSet) (cutoff dataSet)
      ≡ 0ℚ
    scaledZero = trans geometric rightZero

    multiplyInverse :
      inverseOneMinusRoot dataSet
        * ((1ℚ - root dataSet)
          * Geo.partialSum (root dataSet) (cutoff dataSet))
      ≡ inverseOneMinusRoot dataSet * 0ℚ
    multiplyInverse = cong (inverseOneMinusRoot dataSet *_) scaledZero

    leftNormalize :
      inverseOneMinusRoot dataSet
        * ((1ℚ - root dataSet)
          * Geo.partialSum (root dataSet) (cutoff dataSet))
      ≡ Geo.partialSum (root dataSet) (cutoff dataSet)
    leftNormalize =
      trans
        (solve
          ( inverseOneMinusRoot dataSet
          ∷ root dataSet
          ∷ Geo.partialSum (root dataSet) (cutoff dataSet)
          ∷ []))
        (subst
          (λ product →
            product * Geo.partialSum (root dataSet) (cutoff dataSet)
            ≡ Geo.partialSum (root dataSet) (cutoff dataSet))
          (inverseMeaning dataSet)
          (solve (Geo.partialSum (root dataSet) (cutoff dataSet) ∷ [])))

    rightNormalize : inverseOneMinusRoot dataSet * 0ℚ ≡ 0ℚ
    rightNormalize = solve (inverseOneMinusRoot dataSet ∷ [])
  in
  trans (sym leftNormalize) (trans multiplyInverse rightNormalize)

minusOne half : ℚ
minusOne = - 1ℚ
half = Int.+ 1 / 2

twoPointRoot : InvertibleFiniteRoot
twoPointRoot =
  invertible-finite-root
    minusOne
    half
    1
    (solve [])
    (solve [])

twoPointRootCancellation :
  Geo.partialSum minusOne 1 ≡ 0ℚ
twoPointRootCancellation =
  finiteRootGeometricSumZero twoPointRoot
