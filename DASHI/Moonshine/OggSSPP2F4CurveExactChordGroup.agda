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

------------------------------------------------------------------------
-- INDEPENDENT FINITE COORDINATE VALIDATION OF THE CHORD TABLE
--
-- This avoids defining the point law by transporting the ternary basis.
-- Every distinct-x table entry is checked against the exact secant
-- formula over F4; every same-x inverse/vertical case is checked against
-- tangent doubling or the point at infinity.
------------------------------------------------------------------------

open Curve using (F4; zero₄; one₄; zeta₄; zetaSquared₄;
                  _+₄_; _*₄_; square₄)

sameF4 : F4 → F4 → Bool
sameF4 zero₄ zero₄ = true
sameF4 zero₄ one₄ = false
sameF4 zero₄ zeta₄ = false
sameF4 zero₄ zetaSquared₄ = false
sameF4 one₄ zero₄ = false
sameF4 one₄ one₄ = true
sameF4 one₄ zeta₄ = false
sameF4 one₄ zetaSquared₄ = false
sameF4 zeta₄ zero₄ = false
sameF4 zeta₄ one₄ = false
sameF4 zeta₄ zeta₄ = true
sameF4 zeta₄ zetaSquared₄ = false
sameF4 zetaSquared₄ zero₄ = false
sameF4 zetaSquared₄ one₄ = false
sameF4 zetaSquared₄ zeta₄ = false
sameF4 zetaSquared₄ zetaSquared₄ = true

-- Every nonzero F4 element has inverse equal to its square.
inverse₄ : F4 → F4
inverse₄ = square₄

inverse₄Correct :
  (a : F4) →
  sameF4 a zero₄ ≡ false →
  a *₄ inverse₄ a ≡ one₄
inverse₄Correct zero₄ ()
inverse₄Correct one₄ proof = refl
inverse₄Correct zeta₄ proof = refl
inverse₄Correct zetaSquared₄ proof = refl

-- The following coordinate pair is meaningful only for distinct x.
-- The proof of secantMatchesTable below supplies that precondition.
chordCoordinates : AffineF4Point → AffineF4Point → F4 × F4
chordCoordinates p q =
  let xp = proj₁ (Curve.affineCoordinates p)
      yp = proj₂ (Curve.affineCoordinates p)
      xq = proj₁ (Curve.affineCoordinates q)
      yq = proj₂ (Curve.affineCoordinates q)
      lambda = (yp +₄ yq) *₄ inverse₄ (xp +₄ xq)
      xr = (square₄ lambda +₄ xp) +₄ xq
      yr = ((lambda *₄ (xp +₄ xr)) +₄ yp) +₄ one₄
  in xr , yr

-- This helper does NOT identify infinity with an affine point; in the
-- distinct-x proof below the group sum is definitionally affine.
coordinatesOrDummy : RationalF4Point → F4 × F4
coordinatesOrDummy Curve.infinity = zero₄ , zero₄
coordinatesOrDummy (Curve.affine p) = Curve.affineCoordinates p

secantMatchesTable :
  (p q : AffineF4Point) →
  sameF4 (proj₁ (Curve.affineCoordinates p))
         (proj₁ (Curve.affineCoordinates q)) ≡ false →
  coordinatesOrDummy (Curve.affine p ⊞ Curve.affine q)
    ≡ chordCoordinates p q
secantMatchesTable Curve.p00 Curve.p00 ()
secantMatchesTable Curve.p00 Curve.p01 ()
secantMatchesTable Curve.p00 Curve.p1Zeta proof = refl
secantMatchesTable Curve.p00 Curve.p1ZetaSquared proof = refl
secantMatchesTable Curve.p00 Curve.pZetaZeta proof = refl
secantMatchesTable Curve.p00 Curve.pZetaZetaSquared proof = refl
secantMatchesTable Curve.p00 Curve.pZetaSquaredZeta proof = refl
secantMatchesTable Curve.p00 Curve.pZetaSquaredZetaSquared proof = refl
secantMatchesTable Curve.p01 Curve.p00 ()
secantMatchesTable Curve.p01 Curve.p01 ()
secantMatchesTable Curve.p01 Curve.p1Zeta proof = refl
secantMatchesTable Curve.p01 Curve.p1ZetaSquared proof = refl
secantMatchesTable Curve.p01 Curve.pZetaZeta proof = refl
secantMatchesTable Curve.p01 Curve.pZetaZetaSquared proof = refl
secantMatchesTable Curve.p01 Curve.pZetaSquaredZeta proof = refl
secantMatchesTable Curve.p01 Curve.pZetaSquaredZetaSquared proof = refl
secantMatchesTable Curve.p1Zeta Curve.p00 proof = refl
secantMatchesTable Curve.p1Zeta Curve.p01 proof = refl
secantMatchesTable Curve.p1Zeta Curve.p1Zeta ()
secantMatchesTable Curve.p1Zeta Curve.p1ZetaSquared ()
secantMatchesTable Curve.p1Zeta Curve.pZetaZeta proof = refl
secantMatchesTable Curve.p1Zeta Curve.pZetaZetaSquared proof = refl
secantMatchesTable Curve.p1Zeta Curve.pZetaSquaredZeta proof = refl
secantMatchesTable Curve.p1Zeta Curve.pZetaSquaredZetaSquared proof = refl
secantMatchesTable Curve.p1ZetaSquared Curve.p00 proof = refl
secantMatchesTable Curve.p1ZetaSquared Curve.p01 proof = refl
secantMatchesTable Curve.p1ZetaSquared Curve.p1Zeta ()
secantMatchesTable Curve.p1ZetaSquared Curve.p1ZetaSquared ()
secantMatchesTable Curve.p1ZetaSquared Curve.pZetaZeta proof = refl
secantMatchesTable Curve.p1ZetaSquared Curve.pZetaZetaSquared proof = refl
secantMatchesTable Curve.p1ZetaSquared Curve.pZetaSquaredZeta proof = refl
secantMatchesTable Curve.p1ZetaSquared Curve.pZetaSquaredZetaSquared proof = refl
secantMatchesTable Curve.pZetaZeta Curve.p00 proof = refl
secantMatchesTable Curve.pZetaZeta Curve.p01 proof = refl
secantMatchesTable Curve.pZetaZeta Curve.p1Zeta proof = refl
secantMatchesTable Curve.pZetaZeta Curve.p1ZetaSquared proof = refl
secantMatchesTable Curve.pZetaZeta Curve.pZetaZeta ()
secantMatchesTable Curve.pZetaZeta Curve.pZetaZetaSquared ()
secantMatchesTable Curve.pZetaZeta Curve.pZetaSquaredZeta proof = refl
secantMatchesTable Curve.pZetaZeta Curve.pZetaSquaredZetaSquared proof = refl
secantMatchesTable Curve.pZetaZetaSquared Curve.p00 proof = refl
secantMatchesTable Curve.pZetaZetaSquared Curve.p01 proof = refl
secantMatchesTable Curve.pZetaZetaSquared Curve.p1Zeta proof = refl
secantMatchesTable Curve.pZetaZetaSquared Curve.p1ZetaSquared proof = refl
secantMatchesTable Curve.pZetaZetaSquared Curve.pZetaZeta ()
secantMatchesTable Curve.pZetaZetaSquared Curve.pZetaZetaSquared ()
secantMatchesTable Curve.pZetaZetaSquared Curve.pZetaSquaredZeta proof = refl
secantMatchesTable Curve.pZetaZetaSquared Curve.pZetaSquaredZetaSquared proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.p00 proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.p01 proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.p1Zeta proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.p1ZetaSquared proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.pZetaZeta proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.pZetaZetaSquared proof = refl
secantMatchesTable Curve.pZetaSquaredZeta Curve.pZetaSquaredZeta ()
secantMatchesTable Curve.pZetaSquaredZeta Curve.pZetaSquaredZetaSquared ()
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.p00 proof = refl
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.p01 proof = refl
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.p1Zeta proof = refl
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.p1ZetaSquared proof = refl
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.pZetaZeta proof = refl
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.pZetaZetaSquared proof = refl
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.pZetaSquaredZeta ()
secantMatchesTable Curve.pZetaSquaredZetaSquared Curve.pZetaSquaredZetaSquared ()

tangentDoubleEqualsCoordinateInverse :
  (p : AffineF4Point) →
  Curve.affine p ⊞ Curve.affine p ≡ curveInverse (Curve.affine p)
tangentDoubleEqualsCoordinateInverse Curve.p00 = refl
tangentDoubleEqualsCoordinateInverse Curve.p01 = refl
tangentDoubleEqualsCoordinateInverse Curve.p1Zeta = refl
tangentDoubleEqualsCoordinateInverse Curve.p1ZetaSquared = refl
tangentDoubleEqualsCoordinateInverse Curve.pZetaZeta = refl
tangentDoubleEqualsCoordinateInverse Curve.pZetaZetaSquared = refl
tangentDoubleEqualsCoordinateInverse Curve.pZetaSquaredZeta = refl
tangentDoubleEqualsCoordinateInverse Curve.pZetaSquaredZetaSquared = refl

verticalPairReturnsInfinity :
  (p q : AffineF4Point) →
  sameF4 (proj₁ (Curve.affineCoordinates p))
         (proj₁ (Curve.affineCoordinates q)) ≡ true →
  sameF4 (proj₂ (Curve.affineCoordinates p))
         (proj₂ (Curve.affineCoordinates q)) ≡ false →
  Curve.affine p ⊞ Curve.affine q ≡ Curve.infinity
verticalPairReturnsInfinity Curve.p00 Curve.p00 hx ()
verticalPairReturnsInfinity Curve.p00 Curve.p01 hx hy = refl
verticalPairReturnsInfinity Curve.p00 Curve.p1Zeta () hy
verticalPairReturnsInfinity Curve.p00 Curve.p1ZetaSquared () hy
verticalPairReturnsInfinity Curve.p00 Curve.pZetaZeta () hy
verticalPairReturnsInfinity Curve.p00 Curve.pZetaZetaSquared () hy
verticalPairReturnsInfinity Curve.p00 Curve.pZetaSquaredZeta () hy
verticalPairReturnsInfinity Curve.p00 Curve.pZetaSquaredZetaSquared () hy
verticalPairReturnsInfinity Curve.p01 Curve.p00 hx hy = refl
verticalPairReturnsInfinity Curve.p01 Curve.p01 hx ()
verticalPairReturnsInfinity Curve.p01 Curve.p1Zeta () hy
verticalPairReturnsInfinity Curve.p01 Curve.p1ZetaSquared () hy
verticalPairReturnsInfinity Curve.p01 Curve.pZetaZeta () hy
verticalPairReturnsInfinity Curve.p01 Curve.pZetaZetaSquared () hy
verticalPairReturnsInfinity Curve.p01 Curve.pZetaSquaredZeta () hy
verticalPairReturnsInfinity Curve.p01 Curve.pZetaSquaredZetaSquared () hy
verticalPairReturnsInfinity Curve.p1Zeta Curve.p00 () hy
verticalPairReturnsInfinity Curve.p1Zeta Curve.p01 () hy
verticalPairReturnsInfinity Curve.p1Zeta Curve.p1Zeta hx ()
verticalPairReturnsInfinity Curve.p1Zeta Curve.p1ZetaSquared hx hy = refl
verticalPairReturnsInfinity Curve.p1Zeta Curve.pZetaZeta () hy
verticalPairReturnsInfinity Curve.p1Zeta Curve.pZetaZetaSquared () hy
verticalPairReturnsInfinity Curve.p1Zeta Curve.pZetaSquaredZeta () hy
verticalPairReturnsInfinity Curve.p1Zeta Curve.pZetaSquaredZetaSquared () hy
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.p00 () hy
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.p01 () hy
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.p1Zeta hx hy = refl
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.p1ZetaSquared hx ()
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.pZetaZeta () hy
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.pZetaZetaSquared () hy
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.pZetaSquaredZeta () hy
verticalPairReturnsInfinity Curve.p1ZetaSquared Curve.pZetaSquaredZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaZeta Curve.p00 () hy
verticalPairReturnsInfinity Curve.pZetaZeta Curve.p01 () hy
verticalPairReturnsInfinity Curve.pZetaZeta Curve.p1Zeta () hy
verticalPairReturnsInfinity Curve.pZetaZeta Curve.p1ZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaZeta Curve.pZetaZeta hx ()
verticalPairReturnsInfinity Curve.pZetaZeta Curve.pZetaZetaSquared hx hy = refl
verticalPairReturnsInfinity Curve.pZetaZeta Curve.pZetaSquaredZeta () hy
verticalPairReturnsInfinity Curve.pZetaZeta Curve.pZetaSquaredZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.p00 () hy
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.p01 () hy
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.p1Zeta () hy
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.p1ZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.pZetaZeta hx hy = refl
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.pZetaZetaSquared hx ()
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.pZetaSquaredZeta () hy
verticalPairReturnsInfinity Curve.pZetaZetaSquared Curve.pZetaSquaredZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.p00 () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.p01 () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.p1Zeta () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.p1ZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.pZetaZeta () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.pZetaZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.pZetaSquaredZeta hx ()
verticalPairReturnsInfinity Curve.pZetaSquaredZeta Curve.pZetaSquaredZetaSquared hx hy = refl
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.p00 () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.p01 () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.p1Zeta () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.p1ZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.pZetaZeta () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.pZetaZetaSquared () hy
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.pZetaSquaredZeta hx hy = refl
verticalPairReturnsInfinity Curve.pZetaSquaredZetaSquared Curve.pZetaSquaredZetaSquared hx ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record Boundary : Set where
  constructor boundary
  field
    finiteChordAdditionTable : Bool
    independentF4SecantTangencyAndVerticalCertificates : Bool
    associativeCommutativeInverseIdentity : Bool
    everyRationalPointThreeTorsion : Bool
    exactPQGroupBidi : Bool
    frobeniusReflectionAndRhoShear : Bool
    actualMathlibEllipticGroupComparison : Bool
    gamma0FourMarkedScheme : Bool
canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true true true false false
