module DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4BoundaryExact where

------------------------------------------------------------------------
-- INNER DERIVATION LIE ALGEBRA OF THE RATIONAL ALBERT ALGEBRA
--
-- For a Jordan algebra, the commutators of left multiplication operators are
-- the natural inner derivations.  On the explicit rational H_3(O_Q) product,
-- define
--
--   D_{x,y}(z) = x ∘ (y ∘ z) - y ∘ (x ∘ z).
--
-- Companion exact-rational computation on the 27 coordinate basis constructs
-- all C(27,2)=351 such operators and establishes:
--
--   * all 351 satisfy the derivation identity;
--   * their span has dimension 52;
--   * 52 explicit pivot operators are independent;
--   * commutators remain in the same 52-dimensional span;
--   * the derived algebra has dimension 52;
--   * the center has dimension 0.
--
-- This is the expected inner-derivation algebra of the Albert algebra.  The
-- final promotion to the Lie type F4 is deliberately separated: dimension 52,
-- perfection and centerlessness do not by themselves prove root datum/type.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J

subA : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
subA left right = A._+A_ left (A.negA right)

leftMultiply : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
leftMultiply x z = J.jordanProduct x z

innerDerivation :
  A.RationalAlbert → A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
innerDerivation x y z =
  subA
    (J.jordanProduct x (J.jordanProduct y z))
    (J.jordanProduct y (J.jordanProduct x z))

DerivationLaw :
  (A.RationalAlbert → A.RationalAlbert) → Set
DerivationLaw D =
  (x y : A.RationalAlbert) →
    D (J.jordanProduct x y)
    ≡ A._+A_
        (J.jordanProduct (D x) y)
        (J.jordanProduct x (D y))
  where
    open import Agda.Builtin.Equality using (_≡_)

record InnerDerivationDiagnostic : Set where
  constructor inner-derivation-diagnostic
  field
    coordinateBasisDimension : Nat
    unorderedBasisPairs : Nat
    basisPairDerivationsChecked : Nat
    innerDerivationSpanDimension : Nat
    selectedIndependentOperators : Nat
    commutatorSpanDimension : Nat
    derivedAlgebraDimension : Nat
    centerDimension : Nat
    exactRationalProbePassed : Bool
open InnerDerivationDiagnostic public

localDiagnostic : InnerDerivationDiagnostic
localDiagnostic =
  inner-derivation-diagnostic
    27 351 351 52 52 52 52 0 true

record F4LieRecognitionBoundary : Set where
  constructor f4-lie-recognition-boundary
  field
    explicitAlbertProductPaid : Bool
    innerDerivationFormulaTyped : Bool
    allBasisPairDerivationsLocallyChecked : Bool
    innerDerivationDimension52LocallyChecked : Bool
    LieClosureDimension52LocallyChecked : Bool
    perfectLocallyChecked : Bool
    centerlessLocallyChecked : Bool
    AgdaAllInnerDerivationsPaid : Bool
    F4RootDatumPaid : Bool
    LieAlgebraIsomorphismToF4Paid : Bool
    fullAutAlbertEqualsF4Paid : Bool
open F4LieRecognitionBoundary public

canonicalBoundary : F4LieRecognitionBoundary
canonicalBoundary =
  f4-lie-recognition-boundary
    true true true true true true true
    false false false false
