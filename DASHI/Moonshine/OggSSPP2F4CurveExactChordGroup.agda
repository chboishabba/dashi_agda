module DASHI.Moonshine.OggSSPP2F4CurveExactChordGroup where

-- Literal geometric chord law on E(F4): y²+y=x³.
-- For x1 ≠ x2: λ=(y1+y2)/(x1+x2); X3=λ²+x1+x2;
-- Y3=λ*(x1+X3)+y1+1. In F4, nonzero division is square.
-- Doubling yields (x,y+1); vertical inverse pairs sum to infinity.
-- Group axioms and the C3² P,Q chart are exhaustive equality proofs.
-- This module does not equate its finite law with Mathlib's point law.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveShearReflectionExact as Action
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

open Curve using (RationalF4Point; AffineF4Point)

infixl 6 _⊞_
_⊞_ : RationalF4Point → RationalF4Point → RationalF4Point
Curve.infinity ⊞ q = q
(Curve.affine a) ⊞ Curve.infinity = Curve.affine a
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.p01
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.p01) = Curve.infinity
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaSquaredZeta
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.p00) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.p00) = Curve.infinity
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.p00
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaSquaredZeta
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.p01) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.pZetaSquaredZeta
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.infinity
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p01
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.p1Zeta) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p00
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.p1Zeta) = Curve.infinity
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p00
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaSquaredZeta
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p01
(Curve.affine Curve.p1ZetaSquared) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.pZetaSquaredZeta
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p00
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.infinity
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.pZetaZeta) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p01
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p01
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaSquaredZeta
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.infinity
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.p00
(Curve.affine Curve.pZetaZetaSquared) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p01
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p00
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaSquaredZetaSquared
(Curve.affine Curve.pZetaSquaredZeta) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.infinity
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.p00) = Curve.affine Curve.pZetaZetaSquared
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.p01) = Curve.affine Curve.p1ZetaSquared
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p00
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.pZetaZeta
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.p01
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.p1Zeta
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.pZetaSquaredZeta) = Curve.infinity
(Curve.affine Curve.pZetaSquaredZetaSquared) ⊞ (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaSquaredZeta

identityLeft : (p : RationalF4Point) → Curve.infinity ⊞ p ≡ p
identityLeft p = refl
identityRight : (p : RationalF4Point) → p ⊞ Curve.infinity ≡ p
identityRight Curve.infinity = refl
identityRight (Curve.affine a) = refl

commutative : (p q : RationalF4Point) → p ⊞ q ≡ q ⊞ p
commutative Curve.infinity Curve.infinity = refl
commutative Curve.infinity (Curve.affine b) = refl
commutative (Curve.affine a) Curve.infinity = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
commutative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

associative : (p q r : RationalF4Point) →
  (p ⊞ q) ⊞ r ≡ p ⊞ (q ⊞ r)
associative Curve.infinity q r = refl
associative (Curve.affine a) Curve.infinity r = refl
associative (Curve.affine a) (Curve.affine b) Curve.infinity = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
associative (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

curveInverse : RationalF4Point → RationalF4Point
curveInverse Curve.infinity = Curve.infinity
curveInverse (Curve.affine Curve.p00) = Curve.affine Curve.p01
curveInverse (Curve.affine Curve.p01) = Curve.affine Curve.p00
curveInverse (Curve.affine Curve.p1Zeta) = Curve.affine Curve.p1ZetaSquared
curveInverse (Curve.affine Curve.p1ZetaSquared) = Curve.affine Curve.p1Zeta
curveInverse (Curve.affine Curve.pZetaZeta) = Curve.affine Curve.pZetaZetaSquared
curveInverse (Curve.affine Curve.pZetaZetaSquared) = Curve.affine Curve.pZetaZeta
curveInverse (Curve.affine Curve.pZetaSquaredZeta) = Curve.affine Curve.pZetaSquaredZetaSquared
curveInverse (Curve.affine Curve.pZetaSquaredZetaSquared) = Curve.affine Curve.pZetaSquaredZeta

curveInverseLeft : (p : RationalF4Point) →
  curveInverse p ⊞ p ≡ Curve.infinity
curveInverseLeft Curve.infinity = refl
curveInverseLeft (Curve.affine Curve.p00) = refl
curveInverseLeft (Curve.affine Curve.p01) = refl
curveInverseLeft (Curve.affine Curve.p1Zeta) = refl
curveInverseLeft (Curve.affine Curve.p1ZetaSquared) = refl
curveInverseLeft (Curve.affine Curve.pZetaZeta) = refl
curveInverseLeft (Curve.affine Curve.pZetaZetaSquared) = refl
curveInverseLeft (Curve.affine Curve.pZetaSquaredZeta) = refl
curveInverseLeft (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

curveInverseRight : (p : RationalF4Point) →
  p ⊞ curveInverse p ≡ Curve.infinity
curveInverseRight Curve.infinity = refl
curveInverseRight (Curve.affine Curve.p00) = refl
curveInverseRight (Curve.affine Curve.p01) = refl
curveInverseRight (Curve.affine Curve.p1Zeta) = refl
curveInverseRight (Curve.affine Curve.p1ZetaSquared) = refl
curveInverseRight (Curve.affine Curve.pZetaZeta) = refl
curveInverseRight (Curve.affine Curve.pZetaZetaSquared) = refl
curveInverseRight (Curve.affine Curve.pZetaSquaredZeta) = refl
curveInverseRight (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

allNineThreeTorsion : (p : RationalF4Point) →
  (p ⊞ p) ⊞ p ≡ Curve.infinity
allNineThreeTorsion Curve.infinity = refl
allNineThreeTorsion (Curve.affine Curve.p00) = refl
allNineThreeTorsion (Curve.affine Curve.p01) = refl
allNineThreeTorsion (Curve.affine Curve.p1Zeta) = refl
allNineThreeTorsion (Curve.affine Curve.p1ZetaSquared) = refl
allNineThreeTorsion (Curve.affine Curve.pZetaZeta) = refl
allNineThreeTorsion (Curve.affine Curve.pZetaZetaSquared) = refl
allNineThreeTorsion (Curve.affine Curve.pZetaSquaredZeta) = refl
allNineThreeTorsion (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

P : RationalF4Point
P = Curve.affine Curve.p00
Q : RationalF4Point
Q = Curve.affine Curve.p1Zeta
PplusQ : P ⊞ Q ≡ Curve.affine Curve.pZetaZeta
PplusQ = refl

data Coeff3 : Set where
  c0 : Coeff3
  c1 : Coeff3
  c2 : Coeff3

infixl 6 _+₃_
_+₃_ : Coeff3 → Coeff3 → Coeff3
c0 +₃ b = b
c1 +₃ c0 = c1
c1 +₃ c1 = c2
c1 +₃ c2 = c0
c2 +₃ c0 = c2
c2 +₃ c1 = c0
c2 +₃ c2 = c1

neg₃ : Coeff3 → Coeff3
neg₃ c0 = c0
neg₃ c1 = c2
neg₃ c2 = c1

basisChart : Coeff3 → Coeff3 → RationalF4Point
basisChart c0 c0 = Curve.infinity
basisChart c0 c1 = Curve.affine Curve.p1Zeta
basisChart c0 c2 = Curve.affine Curve.p1ZetaSquared
basisChart c1 c0 = Curve.affine Curve.p00
basisChart c1 c1 = Curve.affine Curve.pZetaZeta
basisChart c1 c2 = Curve.affine Curve.pZetaSquaredZetaSquared
basisChart c2 c0 = Curve.affine Curve.p01
basisChart c2 c1 = Curve.affine Curve.pZetaSquaredZeta
basisChart c2 c2 = Curve.affine Curve.pZetaZetaSquared

chartDecoding : RationalF4Point → Coeff3 × Coeff3
chartDecoding Curve.infinity = c0 , c0
chartDecoding (Curve.affine Curve.p1Zeta) = c0 , c1
chartDecoding (Curve.affine Curve.p1ZetaSquared) = c0 , c2
chartDecoding (Curve.affine Curve.p00) = c1 , c0
chartDecoding (Curve.affine Curve.pZetaZeta) = c1 , c1
chartDecoding (Curve.affine Curve.pZetaSquaredZetaSquared) = c1 , c2
chartDecoding (Curve.affine Curve.p01) = c2 , c0
chartDecoding (Curve.affine Curve.pZetaSquaredZeta) = c2 , c1
chartDecoding (Curve.affine Curve.pZetaZetaSquared) = c2 , c2

decodeAfterEncode : (a b : Coeff3) →
  chartDecoding (basisChart a b) ≡ (a , b)
decodeAfterEncode c0 c0 = refl
decodeAfterEncode c0 c1 = refl
decodeAfterEncode c0 c2 = refl
decodeAfterEncode c1 c0 = refl
decodeAfterEncode c1 c1 = refl
decodeAfterEncode c1 c2 = refl
decodeAfterEncode c2 c0 = refl
decodeAfterEncode c2 c1 = refl
decodeAfterEncode c2 c2 = refl

encodeAfterDecode : (p : RationalF4Point) →
  basisChart (proj₁ (chartDecoding p)) (proj₂ (chartDecoding p)) ≡ p
encodeAfterDecode Curve.infinity = refl
encodeAfterDecode (Curve.affine Curve.p00) = refl
encodeAfterDecode (Curve.affine Curve.p01) = refl
encodeAfterDecode (Curve.affine Curve.p1Zeta) = refl
encodeAfterDecode (Curve.affine Curve.p1ZetaSquared) = refl
encodeAfterDecode (Curve.affine Curve.pZetaZeta) = refl
encodeAfterDecode (Curve.affine Curve.pZetaZetaSquared) = refl
encodeAfterDecode (Curve.affine Curve.pZetaSquaredZeta) = refl
encodeAfterDecode (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

basisChartAddition : (a b c d : Coeff3) →
  basisChart a b ⊞ basisChart c d
  ≡ basisChart (a +₃ c) (b +₃ d)
basisChartAddition c0 c0 c0 c0 = refl
basisChartAddition c0 c0 c0 c1 = refl
basisChartAddition c0 c0 c0 c2 = refl
basisChartAddition c0 c0 c1 c0 = refl
basisChartAddition c0 c0 c1 c1 = refl
basisChartAddition c0 c0 c1 c2 = refl
basisChartAddition c0 c0 c2 c0 = refl
basisChartAddition c0 c0 c2 c1 = refl
basisChartAddition c0 c0 c2 c2 = refl
basisChartAddition c0 c1 c0 c0 = refl
basisChartAddition c0 c1 c0 c1 = refl
basisChartAddition c0 c1 c0 c2 = refl
basisChartAddition c0 c1 c1 c0 = refl
basisChartAddition c0 c1 c1 c1 = refl
basisChartAddition c0 c1 c1 c2 = refl
basisChartAddition c0 c1 c2 c0 = refl
basisChartAddition c0 c1 c2 c1 = refl
basisChartAddition c0 c1 c2 c2 = refl
basisChartAddition c0 c2 c0 c0 = refl
basisChartAddition c0 c2 c0 c1 = refl
basisChartAddition c0 c2 c0 c2 = refl
basisChartAddition c0 c2 c1 c0 = refl
basisChartAddition c0 c2 c1 c1 = refl
basisChartAddition c0 c2 c1 c2 = refl
basisChartAddition c0 c2 c2 c0 = refl
basisChartAddition c0 c2 c2 c1 = refl
basisChartAddition c0 c2 c2 c2 = refl
basisChartAddition c1 c0 c0 c0 = refl
basisChartAddition c1 c0 c0 c1 = refl
basisChartAddition c1 c0 c0 c2 = refl
basisChartAddition c1 c0 c1 c0 = refl
basisChartAddition c1 c0 c1 c1 = refl
basisChartAddition c1 c0 c1 c2 = refl
basisChartAddition c1 c0 c2 c0 = refl
basisChartAddition c1 c0 c2 c1 = refl
basisChartAddition c1 c0 c2 c2 = refl
basisChartAddition c1 c1 c0 c0 = refl
basisChartAddition c1 c1 c0 c1 = refl
basisChartAddition c1 c1 c0 c2 = refl
basisChartAddition c1 c1 c1 c0 = refl
basisChartAddition c1 c1 c1 c1 = refl
basisChartAddition c1 c1 c1 c2 = refl
basisChartAddition c1 c1 c2 c0 = refl
basisChartAddition c1 c1 c2 c1 = refl
basisChartAddition c1 c1 c2 c2 = refl
basisChartAddition c1 c2 c0 c0 = refl
basisChartAddition c1 c2 c0 c1 = refl
basisChartAddition c1 c2 c0 c2 = refl
basisChartAddition c1 c2 c1 c0 = refl
basisChartAddition c1 c2 c1 c1 = refl
basisChartAddition c1 c2 c1 c2 = refl
basisChartAddition c1 c2 c2 c0 = refl
basisChartAddition c1 c2 c2 c1 = refl
basisChartAddition c1 c2 c2 c2 = refl
basisChartAddition c2 c0 c0 c0 = refl
basisChartAddition c2 c0 c0 c1 = refl
basisChartAddition c2 c0 c0 c2 = refl
basisChartAddition c2 c0 c1 c0 = refl
basisChartAddition c2 c0 c1 c1 = refl
basisChartAddition c2 c0 c1 c2 = refl
basisChartAddition c2 c0 c2 c0 = refl
basisChartAddition c2 c0 c2 c1 = refl
basisChartAddition c2 c0 c2 c2 = refl
basisChartAddition c2 c1 c0 c0 = refl
basisChartAddition c2 c1 c0 c1 = refl
basisChartAddition c2 c1 c0 c2 = refl
basisChartAddition c2 c1 c1 c0 = refl
basisChartAddition c2 c1 c1 c1 = refl
basisChartAddition c2 c1 c1 c2 = refl
basisChartAddition c2 c1 c2 c0 = refl
basisChartAddition c2 c1 c2 c1 = refl
basisChartAddition c2 c1 c2 c2 = refl
basisChartAddition c2 c2 c0 c0 = refl
basisChartAddition c2 c2 c0 c1 = refl
basisChartAddition c2 c2 c0 c2 = refl
basisChartAddition c2 c2 c1 c0 = refl
basisChartAddition c2 c2 c1 c1 = refl
basisChartAddition c2 c2 c1 c2 = refl
basisChartAddition c2 c2 c2 c0 = refl
basisChartAddition c2 c2 c2 c1 = refl
basisChartAddition c2 c2 c2 c2 = refl

basisZero : basisChart c0 c0 ≡ Curve.infinity
basisZero = refl
basisP : basisChart c1 c0 ≡ P
basisP = refl
basisQ : basisChart c0 c1 ≡ Q
basisQ = refl

basisFrobenius : (a b : Coeff3) →
  Action.frobenius (basisChart a b) ≡ basisChart a (neg₃ b)
basisFrobenius c0 c0 = refl
basisFrobenius c0 c1 = refl
basisFrobenius c0 c2 = refl
basisFrobenius c1 c0 = refl
basisFrobenius c1 c1 = refl
basisFrobenius c1 c2 = refl
basisFrobenius c2 c0 = refl
basisFrobenius c2 c1 = refl
basisFrobenius c2 c2 = refl

basisShear : (a b : Coeff3) →
  Action.rho (basisChart a b) ≡ basisChart (a +₃ b) b
basisShear c0 c0 = refl
basisShear c0 c1 = refl
basisShear c0 c2 = refl
basisShear c1 c0 = refl
basisShear c1 c1 = refl
basisShear c1 c2 = refl
basisShear c2 c0 = refl
basisShear c2 c1 = refl
basisShear c2 c2 = refl

basisInversion : (a b : Coeff3) →
  curveInverse (basisChart a b) ≡ basisChart (neg₃ a) (neg₃ b)
basisInversion c0 c0 = refl
basisInversion c0 c1 = refl
basisInversion c0 c2 = refl
basisInversion c1 c0 = refl
basisInversion c1 c1 = refl
basisInversion c1 c2 = refl
basisInversion c2 c0 = refl
basisInversion c2 c1 = refl
basisInversion c2 c2 = refl

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record Boundary : Set where
  constructor boundary
  field
    finiteChordAdditionTable : Bool
    associativeCommutativeInverseIdentity : Bool
    everyRationalPointThreeTorsion : Bool
    exactPQGroupBidi : Bool
    frobeniusReflectionAndRhoShear : Bool
    actualMathlibEllipticGroupComparison : Bool
    gamma0FourMarkedScheme : Bool
canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true true false false
