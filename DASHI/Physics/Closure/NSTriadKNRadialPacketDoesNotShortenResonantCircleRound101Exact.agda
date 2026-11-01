module DASHI.Physics.Closure.NSTriadKNRadialPacketDoesNotShortenResonantCircleRound101Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Jean Bourgain; Zeev Rudnick.
-- Title: "On the geometry of the nodal lines of eigenfunctions of the
-- two-dimensional torus".
-- Annales Henri Poincare 12 (2011), 1027--1053.
-- DOI: 10.1007/s00023-011-0098-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND101 / RADIAL PACKETS DO NOT CREATE SHORT ARCS
--
-- Bourgain--Rudnick short-arc information can only help if the physical
-- selector actually restricts an arithmetic circle to a short angular arc.
-- A radial Fourier packet does not do this.
--
-- If packet membership factors through the Laplacian eigenvalue |k|^2, then on
-- a fixed eigenvalue triple
--
--   |p|^2=m, |q|^2=l, |k|^2=n,
--
-- the three membership bits are constants depending only on (m,l,n).  Hence
-- the mixed-membership boundary predicate is constant across the ENTIRE
-- arithmetic-circle fibre.  The radial boundary selector either keeps the
-- whole fixed-(m,l,n) circle or discards the whole circle; it creates no
-- angular shortening by itself.
--
-- Therefore the Round100 arithmetic-circle route cannot import short-arc
-- lattice bounds merely from the existing dyadic/eigenvalue packet boundary.
-- A genuine angular selector/cancellation must be proved on the literal
-- interaction before short-arc number theory becomes applicable.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

radialSelected :
  ∀ {m : Level} {Mode : Set m} →
  (Nat → Bool) → (Mode → Nat) → Mode → Bool
radialSelected selector eigenvalue mode = selector (eigenvalue mode)

mixedBoundary : Bool → Bool → Bool → Bool
mixedBoundary true true true = false
mixedBoundary false false false = false
mixedBoundary _ _ _ = true

radialBoundary :
  ∀ {m : Level} {Mode : Set m} →
  (Nat → Bool) → (Mode → Nat) → Mode → Mode → Mode → Bool
radialBoundary selector eigenvalue k p q =
  mixedBoundary
    (radialSelected selector eigenvalue k)
    (radialSelected selector eigenvalue p)
    (radialSelected selector eigenvalue q)

fixedEigenvalueTripleBoundaryConstant :
  ∀ {m : Level} {Mode : Set m}
    (selector : Nat → Bool)
    (eigenvalue : Mode → Nat)
    (n mVal l : Nat)
    (k p q : Mode) →
  eigenvalue k ≡ n →
  eigenvalue p ≡ mVal →
  eigenvalue q ≡ l →
  radialBoundary selector eigenvalue k p q
  ≡ mixedBoundary (selector n) (selector mVal) (selector l)
fixedEigenvalueTripleBoundaryConstant selector eigenvalue n mVal l k p q
    kRadius pRadius qRadius
  rewrite kRadius | pRadius | qRadius = refl

sameEigenvalueTripleHasSameBoundaryStatus :
  ∀ {m : Level} {Mode : Set m}
    (selector : Nat → Bool)
    (eigenvalue : Mode → Nat)
    (n mVal l : Nat)
    (k p q k' p' q' : Mode) →
  eigenvalue k ≡ n →
  eigenvalue p ≡ mVal →
  eigenvalue q ≡ l →
  eigenvalue k' ≡ n →
  eigenvalue p' ≡ mVal →
  eigenvalue q' ≡ l →
  radialBoundary selector eigenvalue k p q
  ≡ radialBoundary selector eigenvalue k' p' q'
sameEigenvalueTripleHasSameBoundaryStatus selector eigenvalue n mVal l
    k p q k' p' q' kRadius pRadius qRadius kRadius' pRadius' qRadius'
  rewrite kRadius | pRadius | qRadius
        | kRadius' | pRadius' | qRadius' = refl

round101RadialBoundaryCreatesShortArcLocalization : Bool
round101RadialBoundaryCreatesShortArcLocalization = false

round101FixedEigenvalueBoundaryStatusIsAngularlyConstant : Bool
round101FixedEigenvalueBoundaryStatusIsAngularlyConstant = true

round101RadialBoundaryCreatesShortArcLocalizationIsFalse :
  round101RadialBoundaryCreatesShortArcLocalization ≡ false
round101RadialBoundaryCreatesShortArcLocalizationIsFalse = refl
