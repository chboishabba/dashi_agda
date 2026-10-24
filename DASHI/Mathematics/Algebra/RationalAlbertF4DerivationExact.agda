module DASHI.Mathematics.Algebra.RationalAlbertF4DerivationExact where

------------------------------------------------------------------------
-- RATIONAL ALBERT INNER-DERIVATION / F4 MAX-CUT
--
-- On the now literal rational Albert Jordan algebra define
--
--   delta(X,Y) = [L_X,L_Y].
--
-- Companion exact rational linear algebra on the 27-coordinate basis checks:
--
-- * all 351 basis-pair operators satisfy the Jordan derivation commutator law;
-- * their 27x27 matrix span has rank exactly 52.
--
-- This is the expected derivation dimension of the Albert algebra / Lie(F4),
-- but the numerical rank is retained as an executable receipt rather than
-- silently naming an algebraic group from dimension alone.
--
-- The same file also gives the canonical diagonal lift of an octonion map or
-- octonion derivation to the three off-diagonal Albert coordinates.  Thus the
-- 14-dimensional octonion-derivation lane embeds as a concrete sub-lane of the
-- 52-dimensional Albert inner-derivation lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (0ℚ)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalOctonionG2DerivationExact as G2

subA : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
subA x y = A._+A_ x (A.negA y)

leftJordan : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
leftJordan x y = J.jordanProduct x y

innerDerivation :
  A.RationalAlbert → A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
innerDerivation x y z =
  subA
    (leftJordan x (leftJordan y z))
    (leftJordan y (leftJordan x z))

AlbertDerivationLaw : (A.RationalAlbert → A.RationalAlbert) → Set
AlbertDerivationLaw deriv =
  (x y : A.RationalAlbert) →
    deriv (J.jordanProduct x y) ≡
      A._+A_
        (J.jordanProduct (deriv x) y)
        (J.jordanProduct x (deriv y))

------------------------------------------------------------------------
-- Diagonal lift of octonion automorphisms / derivations.
------------------------------------------------------------------------

liftOctonionMap :
  (O.RationalOctonion → O.RationalOctonion) →
  A.RationalAlbert → A.RationalAlbert
liftOctonionMap f (A.albert a b c x y z) =
  A.albert a b c (f x) (f y) (f z)

liftOctonionDerivation :
  (O.RationalOctonion → O.RationalOctonion) →
  A.RationalAlbert → A.RationalAlbert
liftOctonionDerivation d (A.albert _ _ _ x y z) =
  A.albert 0ℚ 0ℚ 0ℚ (d x) (d y) (d z)

liftG7 liftG4 : A.RationalAlbert → A.RationalAlbert
liftG7 = liftOctonionMap G2.g7
liftG4 = liftOctonionMap G2.g4

LiftPreservesJordan : (O.RationalOctonion → O.RationalOctonion) → Set
LiftPreservesJordan f =
  (x y : A.RationalAlbert) →
    liftOctonionMap f (J.jordanProduct x y) ≡
      J.jordanProduct (liftOctonionMap f x) (liftOctonionMap f y)

LiftPreservesCubic : (O.RationalOctonion → O.RationalOctonion) → Set
LiftPreservesCubic f =
  (x : A.RationalAlbert) →
    A.cubicNorm (liftOctonionMap f x) ≡ A.cubicNorm x

record F4ExactProbeReceipt : Set where
  constructor f4-exact-probe-receipt
  field
    albertCoordinateDimension : Nat
    basisPairInnerDerivationCandidates : Nat
    innerDerivationSpanRank : Nat
    allBasisDerivationCommutatorChecksPassed : Bool
    octonionDerivationSubspanRank : Nat
open F4ExactProbeReceipt public

canonicalF4ExactProbeReceipt : F4ExactProbeReceipt
canonicalF4ExactProbeReceipt =
  f4-exact-probe-receipt 27 351 52 true 14

record F4PromotionBoundary : Set where
  constructor f4-promotion-boundary
  field
    literalAlbertInnerDerivationOperatorPaid : Bool
    exact351BasisOperatorsChecked : Bool
    exactInnerDerivationSpanRank52Passed : Bool
    diagonalOctonionMapLiftPaid : Bool
    diagonalOctonionDerivationLiftPaid : Bool
    explicitSignedBasisG2LiftCandidatesPaid : Bool
    agdaAllInnerDerivationsSatisfyDerivationLawPaid : Bool
    agdaRank52KernelPaid : Bool
    fullF4AlgebraicGroupRecognitionPaid : Bool
open F4PromotionBoundary public

currentF4PromotionBoundary : F4PromotionBoundary
currentF4PromotionBoundary =
  f4-promotion-boundary
    true true true true true true
    false false false
