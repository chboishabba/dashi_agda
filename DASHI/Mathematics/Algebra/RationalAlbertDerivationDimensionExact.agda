module DASHI.Mathematics.Algebra.RationalAlbertDerivationDimensionExact where

------------------------------------------------------------------------
-- DERIVATION ALGEBRA OF THE EXPLICIT RATIONAL ALBERT ALGEBRA
--
-- The carrier/product are now literal repository objects, so the derivation
-- problem is an exact finite rational linear-algebra calculation rather than a
-- dimension/name analogy.
--
-- For a linear endomorphism D of the 27-coordinate carrier, impose
--
--   D(x o y) = D(x) o y + x o D(y)
--
-- on the 27 coordinate basis.  There are 27^2 = 729 unknown matrix entries.
-- The companion pure-Python exact-rational elimination
--
--   scripts/check_rational_albert_derivation_dimension.py
--
-- computes:
--
--   derivation constraint rank = 677,
--   nullity = 729 - 677 = 52.
--
-- Independently, the 351 commutators [L_ei,L_ej] of coordinate left-
-- multiplication operators span exact rational rank 52.  Thus the runtime
-- calculation finds the complete derivation space and finds it spanned by
-- inner Jordan derivations.
--
-- This is the expected Lie-algebra dimension of F4, but dimension 52 alone is
-- NOT promoted to a Lie-type/classification theorem.  The missing formal layer
-- is a kernel rank certificate and/or root/Cartan/classification recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
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
    ≡ J.jordanProduct (D x) y A.+A J.jordanProduct x (D y)
  where
    open import Agda.Builtin.Equality using (_≡_)

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
