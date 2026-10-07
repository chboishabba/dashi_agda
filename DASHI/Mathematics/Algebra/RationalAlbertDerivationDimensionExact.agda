module DASHI.Mathematics.Algebra.RationalAlbertDerivationDimensionExact where

------------------------------------------------------------------------
-- DERIVATION ALGEBRA OF THE EXPLICIT RATIONAL ALBERT ALGEBRA
--
-- The carrier/product are literal repository objects, so the derivation
-- problem is an exact finite rational linear-algebra calculation rather than a
-- dimension/name analogy.
--
-- Companion runtime:
--   scripts/check_rational_albert_derivation_dimension.py
-- computes exactly over Q:
--   729 endomorphism unknowns,
--   derivation-constraint rank 677,
--   nullity 52,
--   rank 52 for the span of all 351 [L_ei,L_ej] commutators.
--
-- Hence the exact runtime calculation finds all derivations spanned by inner
-- Jordan derivations.  Dimension 52 is not by itself promoted to Lie type F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J

subA : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
subA left right = A._+A_ left (A.negA right)

leftMultiply : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
leftMultiply x y = J.jordanProduct x y

innerDerivation : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
innerDerivation x y z =
  subA
    (leftMultiply x (leftMultiply y z))
    (leftMultiply y (leftMultiply x z))

DerivationLaw : (A.RationalAlbert → A.RationalAlbert) → Set
DerivationLaw D =
  (x y : A.RationalAlbert) →
    D (J.jordanProduct x y)
    ≡ A._+A_
        (J.jordanProduct (D x) y)
        (J.jordanProduct x (D y))

albertCoordinateCount : Nat
albertCoordinateCount = 27

derivationMatrixUnknownCount : Nat
derivationMatrixUnknownCount = 729

derivationConstraintExactRankRuntime : Nat
derivationConstraintExactRankRuntime = 677

derivationSpaceDimensionRuntime : Nat
derivationSpaceDimensionRuntime = 52

innerCommutatorCandidateCount : Nat
innerCommutatorCandidateCount = 351

innerCommutatorSpanExactRankRuntime : Nat
innerCommutatorSpanExactRankRuntime = 52

record AlbertDerivationBoundary : Set where
  constructor albert-derivation-boundary
  field
    derivationLawTypedOnActualAlbertProduct : Bool
    innerCommutatorFamilyTyped : Bool
    exactRationalConstraintRank677RuntimeChecked : Bool
    exactRationalDerivationDimension52RuntimeChecked : Bool
    exactRationalInnerSpan52RuntimeChecked : Bool
    runtimeAllDerivationsInnerByDimensionComparison : Bool
    agdaKernelRankCertificatePaid : Bool
    agdaKernelInnerDerivationLawPaid : Bool
    f4LieAlgebraTypeRecognitionPaid : Bool
open AlbertDerivationBoundary public

currentAlbertDerivationBoundary : AlbertDerivationBoundary
currentAlbertDerivationBoundary =
  albert-derivation-boundary
    true true true true true true false false false
