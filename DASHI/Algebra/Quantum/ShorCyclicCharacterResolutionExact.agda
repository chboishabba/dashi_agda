module DASHI.Algebra.Quantum.ShorCyclicCharacterResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Fin.Base as Fin
open import Data.List.Base using (List; []; _∷_; allFin)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector

------------------------------------------------------------------------
-- ONE-DIMENSIONAL CYCLIC CHARACTER RESOLUTION
--
-- The Shor QFT acts independently in every target column.  Consequently the
-- full exponent x target inversion theorem should not be primitive.  The exact
-- reusable mathematical leaf is the normalized cyclic transform on one vector
-- of Q coefficients:
--
--   F(v)_k     = sum_x alpha * chi(k,x)     * v_x
--   F^-1(w)_x  = sum_k alpha * chi^-1(x,k)  * w_k.
--
-- If these two scalar transforms are inverse for arbitrary coefficient vectors,
-- the canonical nested-Vec Shor register inherits Fourier inversion in every
-- target column by constructive vector extensionality.
--
-- This is the same mathematical surface as the already-pinned external Lean
-- DFT theorem, but this file does not assert that the Lean coefficient carrier
-- and the DASHI coefficient carrier are already the same object.
------------------------------------------------------------------------

sumCongruence :
  ∀ {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (left right : Fin.Fin Q → Coefficient) →
  (∀ x → left x ≡ right x) →
  (indices : List (Fin.Fin Q)) →
  Vector.sumCoefficients A left indices
  ≡ Vector.sumCoefficients A right indices
sumCongruence A left right pointwise [] = refl
sumCongruence A left right pointwise (x ∷ xs)
  rewrite pointwise x
        | sumCongruence A left right pointwise xs = refl

scalarForward :
  ∀ {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (Fin.Fin Q → Coefficient) →
  Fin.Fin Q → Coefficient
scalarForward {Q = Q} A values k =
  Vector.sumCoefficients A
    (λ x →
      Phase.multiplyCoefficient A
        (Phase.normalisation A)
        (Phase.multiplyCoefficient A
          (Phase.phase A k x)
          (values x)))
    (allFin Q)

scalarInverse :
  ∀ {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (Fin.Fin Q → Coefficient) →
  Fin.Fin Q → Coefficient
scalarInverse {Q = Q} A values x =
  Vector.sumCoefficients A
    (λ k →
      Phase.multiplyCoefficient A
        (Phase.normalisation A)
        (Phase.multiplyCoefficient A
          (Phase.inversePhase A x k)
          (values k)))
    (allFin Q)

record CyclicCharacterResolutionAuthority
    {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) : Set₁ where
  constructor cyclicCharacterResolutionAuthority
  field
    inverseAfterForwardAt :
      (values : Fin.Fin Q → Coefficient) →
      (x : Fin.Fin Q) →
      scalarInverse A (scalarForward A values) x ≡ values x

    forwardAfterInverseAt :
      (values : Fin.Fin Q → Coefficient) →
      (k : Fin.Fin Q) →
      scalarForward A (scalarInverse A values) k ≡ values k

open CyclicCharacterResolutionAuthority public

------------------------------------------------------------------------
-- Identify the literal vector-table implementation with the scalar transform.
------------------------------------------------------------------------

vectorForwardLookup :
  ∀ {Coefficient Q N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (table : Vector.AmplitudeTable Coefficient Q N)
    (k : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  Vector.tableLookup (Vector.vectorForwardTable A table) k target
  ≡ scalarForward A (λ x → Vector.tableLookup table x target) k
vectorForwardLookup {Q = Q} A table k target =
  Vector.lookupTabulateTable
    (λ row slot →
      Vector.sumCoefficients A
        (λ x →
          Phase.multiplyCoefficient A
            (Phase.normalisation A)
            (Phase.multiplyCoefficient A
              (Phase.phase A row x)
              (Vector.tableLookup table x slot)))
        (allFin Q))
    k target

vectorInverseLookup :
  ∀ {Coefficient Q N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (table : Vector.AmplitudeTable Coefficient Q N)
    (x : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  Vector.tableLookup (Vector.vectorInverseTable A table) x target
  ≡ scalarInverse A (λ k → Vector.tableLookup table k target) x
vectorInverseLookup {Q = Q} A table x target =
  Vector.lookupTabulateTable
    (λ row slot →
      Vector.sumCoefficients A
        (λ k →
          Phase.multiplyCoefficient A
            (Phase.normalisation A)
            (Phase.multiplyCoefficient A
              (Phase.inversePhase A row k)
              (Vector.tableLookup table k slot)))
        (allFin Q))
    x target

inverseForwardCoordinate :
  ∀ {Coefficient Q N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (R : CyclicCharacterResolutionAuthority A)
    (table : Vector.AmplitudeTable Coefficient Q N)
    (x : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  Vector.tableLookup
    (Vector.vectorInverseTable A (Vector.vectorForwardTable A table))
    x target
  ≡ Vector.tableLookup table x target
inverseForwardCoordinate {Q = Q} A R table x target =
  trans
    (vectorInverseLookup A (Vector.vectorForwardTable A table) x target)
    (trans
      (sumCongruence A
        (λ k →
          Phase.multiplyCoefficient A
            (Phase.normalisation A)
            (Phase.multiplyCoefficient A
              (Phase.inversePhase A x k)
              (Vector.tableLookup (Vector.vectorForwardTable A table) k target)))
        (λ k →
          Phase.multiplyCoefficient A
            (Phase.normalisation A)
            (Phase.multiplyCoefficient A
              (Phase.inversePhase A x k)
              (scalarForward A
                (λ j → Vector.tableLookup table j target)
                k)))
        (λ k →
          cong
            (λ value →
              Phase.multiplyCoefficient A
                (Phase.normalisation A)
                (Phase.multiplyCoefficient A
                  (Phase.inversePhase A x k)
                  value))
            (vectorForwardLookup A table k target))
        (allFin Q))
      (inverseAfterForwardAt R
        (λ j → Vector.tableLookup table j target)
        x))

forwardInverseCoordinate :
  ∀ {Coefficient Q N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (R : CyclicCharacterResolutionAuthority A)
    (table : Vector.AmplitudeTable Coefficient Q N)
    (k : Fin.Fin Q)
    (target : Fin.Fin (suc N)) →
  Vector.tableLookup
    (Vector.vectorForwardTable A (Vector.vectorInverseTable A table))
    k target
  ≡ Vector.tableLookup table k target
forwardInverseCoordinate {Q = Q} A R table k target =
  trans
    (vectorForwardLookup A (Vector.vectorInverseTable A table) k target)
    (trans
      (sumCongruence A
        (λ x →
          Phase.multiplyCoefficient A
            (Phase.normalisation A)
            (Phase.multiplyCoefficient A
              (Phase.phase A k x)
              (Vector.tableLookup (Vector.vectorInverseTable A table) x target)))
        (λ x →
          Phase.multiplyCoefficient A
            (Phase.normalisation A)
            (Phase.multiplyCoefficient A
              (Phase.phase A k x)
              (scalarInverse A
                (λ j → Vector.tableLookup table j target)
                x)))
        (λ x →
          cong
            (λ value →
              Phase.multiplyCoefficient A
                (Phase.normalisation A)
                (Phase.multiplyCoefficient A
                  (Phase.phase A k x)
                  value))
            (vectorInverseLookup A table x target))
        (allFin Q))
      (forwardAfterInverseAt R
        (λ j → Vector.tableLookup table j target)
        k))

vectorInversionFromCharacterResolution :
  ∀ {Q Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  CyclicCharacterResolutionAuthority A →
  Vector.VectorCyclicPhaseInversionAuthority A
vectorInversionFromCharacterResolution A R = record
  { inverseAfterForwardTable = λ table →
      Vector.tableExtensionality _ _
        (inverseForwardCoordinate A R table)
  ; forwardAfterInverseTable = λ table →
      Vector.tableExtensionality _ _
        (forwardInverseCoordinate A R table)
  }

record ShorCyclicCharacterResolutionBoundary : Set where
  constructor shorCyclicCharacterResolutionBoundary
  field
    targetDimensionRemovedFromHardLeaf : Bool
    oneDimensionalCyclicResolutionSufficient : Bool
    vectorInversionCompiledConstructively : Bool
    functionExtensionalityUsed : Bool
    concreteCoefficientResolutionProvedHere : Bool
    externalLeanSameObjectWeldProvedHere : Bool

canonicalShorCyclicCharacterResolutionBoundary :
  ShorCyclicCharacterResolutionBoundary
canonicalShorCyclicCharacterResolutionBoundary =
  shorCyclicCharacterResolutionBoundary
    true true true false false false
