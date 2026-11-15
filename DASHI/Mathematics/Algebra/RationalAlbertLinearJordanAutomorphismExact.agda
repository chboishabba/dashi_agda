module DASHI.Mathematics.Algebra.RationalAlbertLinearJordanAutomorphismExact where

------------------------------------------------------------------------
-- ACTUAL LINEAR JORDAN AUTOMORPHISMS OF THE RATIONAL ALBERT ALGEBRA
--
-- Package the explicit coordinate S3 and signed-basis-octonion symmetries as
-- bijective Q-linear maps preserving the Albert unit, Jordan product and cubic
-- norm.  This is the correct concrete carrier for the eventual Aut(J)
-- recognition theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S3
import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismLawsExact as S3Laws
import DASHI.Mathematics.Algebra.RationalOctonionLinearityExact as OLin
import DASHI.Mathematics.Algebra.RationalAlbertSignedBasisAutomorphismExact as G

record LinearJordanAutomorphism : Set where
  constructor linear-jordan-automorphism
  field
    to from : A.RationalAlbert → A.RationalAlbert
    leftInverse : ∀ x → from (to x) ≡ x
    rightInverse : ∀ x → to (from x) ≡ x
    preservesAdd : ∀ x y → to (A._+A_ x y) ≡ A._+A_ (to x) (to y)
    preservesScale : ∀ scalar x → to (A.scaleA scalar x) ≡ A.scaleA scalar (to x)
    preservesUnit : to A.unitAlbert ≡ A.unitAlbert
    preservesProduct : ∀ x y → to (J.jordanProduct x y) ≡ J.jordanProduct (to x) (to y)
    preservesCubic : ∀ x → A.cubicNorm (to x) ≡ A.cubicNorm x
open LinearJordanAutomorphism public

------------------------------------------------------------------------
-- Coordinate-cycle automorphism.
------------------------------------------------------------------------

cycleSquared : A.RationalAlbert → A.RationalAlbert
cycleSquared = S3.cycleSquared

cycleAdditive : ∀ x y →
  S3.cycleA (A._+A_ x y) ≡ A._+A_ (S3.cycleA x) (S3.cycleA y)
cycleAdditive (A.albert _ _ _ _ _ _) (A.albert _ _ _ _ _ _) = refl

cycleScale : ∀ scalar x →
  S3.cycleA (A.scaleA scalar x) ≡ A.scaleA scalar (S3.cycleA x)
cycleScale scalar (A.albert _ _ _ _ _ _) = refl

cycleRightInverse : ∀ x → S3.cycleA (cycleSquared x) ≡ x
cycleRightInverse = S3.cycleCubedIdentity

cycleLeftInverse : ∀ x → cycleSquared (S3.cycleA x) ≡ x
cycleLeftInverse (A.albert _ _ _ _ _ _) = refl

cycleAutomorphism : LinearJordanAutomorphism
cycleAutomorphism =
  linear-jordan-automorphism
    S3.cycleA
    cycleSquared
    cycleLeftInverse
    cycleRightInverse
    cycleAdditive
    cycleScale
    refl
    S3Laws.cyclePreservesProduct
    S3Laws.cyclePreservesCubic

------------------------------------------------------------------------
-- Coordinate transposition automorphism.
------------------------------------------------------------------------

swapAdditive : ∀ x y →
  S3.swapA (A._+A_ x y) ≡ A._+A_ (S3.swapA x) (S3.swapA y)
swapAdditive
  (A.albert a b c x y z)
  (A.albert d e f u v w) =
  Laws.albertExt refl refl refl
    (OLin.conjugateAdditive x u)
    (OLin.conjugateAdditive z w)
    (OLin.conjugateAdditive y v)

swapScale : ∀ scalar x →
  S3.swapA (A.scaleA scalar x) ≡ A.scaleA scalar (S3.swapA x)
swapScale scalar (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (OLin.conjugateScale scalar x)
    (OLin.conjugateScale scalar z)
    (OLin.conjugateScale scalar y)

swapAutomorphism : LinearJordanAutomorphism
swapAutomorphism =
  linear-jordan-automorphism
    S3.swapA
    S3.swapA
    S3.swapSquaredIdentity
    S3.swapSquaredIdentity
    swapAdditive
    swapScale
    refl
    S3Laws.swapPreservesProduct
    S3Laws.swapPreservesCubic

------------------------------------------------------------------------
-- Lifted signed-basis octonion automorphism A.
------------------------------------------------------------------------

liftAutoAAdditive : ∀ x y →
  G.liftAutoA (A._+A_ x y) ≡ A._+A_ (G.liftAutoA x) (G.liftAutoA y)
liftAutoAAdditive
  (A.albert a b c x y z)
  (A.albert d e f u v w) =
  Laws.albertExt refl refl refl
    (OLin.autoAAdditive x u)
    (OLin.autoAAdditive y v)
    (OLin.autoAAdditive z w)

liftAutoAScale : ∀ scalar x →
  G.liftAutoA (A.scaleA scalar x) ≡ A.scaleA scalar (G.liftAutoA x)
liftAutoAScale scalar (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (OLin.autoAScale scalar x)
    (OLin.autoAScale scalar y)
    (OLin.autoAScale scalar z)

liftAutoAAutomorphism : LinearJordanAutomorphism
liftAutoAAutomorphism =
  linear-jordan-automorphism
    G.liftAutoA
    G.liftAutoA
    G.liftAutoASquaredIdentity
    G.liftAutoASquaredIdentity
    liftAutoAAdditive
    liftAutoAScale
    refl
    G.liftAutoAPreservesProduct
    G.liftAutoAPreservesCubic

------------------------------------------------------------------------
-- Lifted signed-basis octonion automorphism B.
------------------------------------------------------------------------

liftAutoBSquared : A.RationalAlbert → A.RationalAlbert
liftAutoBSquared value = G.liftAutoB (G.liftAutoB value)

liftAutoBLeftInverse : ∀ x → liftAutoBSquared (G.liftAutoB x) ≡ x
liftAutoBLeftInverse (A.albert _ _ _ _ _ _) = G.liftAutoBCubedIdentity _

liftAutoBRightInverse : ∀ x → G.liftAutoB (liftAutoBSquared x) ≡ x
liftAutoBRightInverse = G.liftAutoBCubedIdentity

liftAutoBAdditive : ∀ x y →
  G.liftAutoB (A._+A_ x y) ≡ A._+A_ (G.liftAutoB x) (G.liftAutoB y)
liftAutoBAdditive
  (A.albert a b c x y z)
  (A.albert d e f u v w) =
  Laws.albertExt refl refl refl
    (OLin.autoBAdditive x u)
    (OLin.autoBAdditive y v)
    (OLin.autoBAdditive z w)

liftAutoBScale : ∀ scalar x →
  G.liftAutoB (A.scaleA scalar x) ≡ A.scaleA scalar (G.liftAutoB x)
liftAutoBScale scalar (A.albert a b c x y z) =
  Laws.albertExt refl refl refl
    (OLin.autoBScale scalar x)
    (OLin.autoBScale scalar y)
    (OLin.autoBScale scalar z)

liftAutoBAutomorphism : LinearJordanAutomorphism
liftAutoBAutomorphism =
  linear-jordan-automorphism
    G.liftAutoB
    liftAutoBSquared
    liftAutoBLeftInverse
    liftAutoBRightInverse
    liftAutoBAdditive
    liftAutoBScale
    refl
    G.liftAutoBPreservesProduct
    G.liftAutoBPreservesCubic

------------------------------------------------------------------------
-- Composition stays inside the typed automorphism carrier.
------------------------------------------------------------------------

compose : LinearJordanAutomorphism → LinearJordanAutomorphism → LinearJordanAutomorphism
compose f g =
  linear-jordan-automorphism
    (λ x → to f (to g x))
    (λ x → from g (from f x))
    (λ x →
      trans
        (cong (from g) (leftInverse f (to g x)))
        (leftInverse g x))
    (λ x →
      trans
        (cong (to f) (rightInverse g (from f x)))
        (rightInverse f x))
    (λ x y →
      trans
        (cong (to f) (preservesAdd g x y))
        (preservesAdd f (to g x) (to g y)))
    (λ scalar x →
      trans
        (cong (to f) (preservesScale g scalar x))
        (preservesScale f scalar (to g x)))
    (trans (cong (to f) (preservesUnit g)) (preservesUnit f))
    (λ x y →
      trans
        (cong (to f) (preservesProduct g x y))
        (preservesProduct f (to g x) (to g y)))
    (λ x → trans (preservesCubic f (to g x)) (preservesCubic g x))
  where
    open import Relation.Binary.PropositionalEquality using (cong; trans)

record Boundary : Set where
  constructor boundary
  field
    typedLinearJordanAutomorphismCarrierPaid : Bool
    coordinateS3ElementsInCarrierPaid : Bool
    signedBasisOctonionLiftsInCarrierPaid : Bool
    compositionClosurePaid : Bool
    fullAutJIdentifiedWithF4Internally : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true false
