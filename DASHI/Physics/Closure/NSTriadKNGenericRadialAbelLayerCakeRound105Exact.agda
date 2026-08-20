module DASHI.Physics.Closure.NSTriadKNGenericRadialAbelLayerCakeRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND105 / GENERIC RADIAL ABEL LAYER-CAKE
--
-- Round104 proved the finite radial summation-by-parts identity over Q.  That
-- was sufficient to expose the packet-flux mechanism but left an avoidable
-- representation seam: the literal H^(1/2) Fourier multiplier is |k|, which is
-- not rational on a generic integer lattice mode.
--
-- This file proves the SAME finite Abel identity over the repository's generic
-- exact ordered commutative ring.  In particular, the scalar carrier already
-- exposes `sqrt`, so a concrete real/Bishop-real implementation may use the
-- literal multiplier
--
--   lambda(k) = sqrt(|k|^2)
--
-- without changing the packet-flux algebra.  No square-root law is assumed by
-- this theorem; it only removes Q as an accidental restriction on the exact
-- summation identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNExactRingSolverBridge as RingBridge

module _ (K : Algebra.ExactOrderedCommutativeRing) where

  S = Algebra.orderedScalar K
  Carrier = Scalar.Scalar S

  sub : Carrier → Carrier → Carrier
  sub x y = Scalar._+_ S x (Scalar.neg S y)

  BandTransfer : Set
  BandTransfer = Carrier × Carrier

  weight : BandTransfer → Carrier
  weight = proj₁

  transfer : BandTransfer → Carrier
  transfer = proj₂

  totalTransfer : List BandTransfer → Carrier
  totalTransfer [] = Scalar.zero S
  totalTransfer (b ∷ rest) =
    Scalar._+_ S (transfer b) (totalTransfer rest)

  weightedTransfer : List BandTransfer → Carrier
  weightedTransfer [] = Scalar.zero S
  weightedTransfer (b ∷ rest) =
    Scalar._+_ S
      (Scalar._*_ S (weight b) (transfer b))
      (weightedTransfer rest)

  baseWeight : List BandTransfer → Carrier
  baseWeight [] = Scalar.zero S
  baseWeight (b ∷ rest) = weight b

  radialLayerCake : List BandTransfer → Carrier
  radialLayerCake [] = Scalar.zero S
  radialLayerCake (b ∷ []) = Scalar.zero S
  radialLayerCake (b0 ∷ b1 ∷ rest) =
    Scalar._+_ S
      (Scalar._*_ S
        (sub (weight b1) (weight b0))
        (totalTransfer (b1 ∷ rest)))
      (radialLayerCake (b1 ∷ rest))

  weightedTransferAbelIdentity :
    (bands : List BandTransfer) →
    weightedTransfer bands
    ≡ Scalar._+_ S
        (Scalar._*_ S (baseWeight bands) (totalTransfer bands))
        (radialLayerCake bands)
  weightedTransferAbelIdentity [] =
    symZero
    where
      module R = RingBridge.Solver K
      symZero : Scalar.zero S ≡
        Scalar._+_ S
          (Scalar._*_ S (Scalar.zero S) (Scalar.zero S))
          (Scalar.zero S)
      symZero = R.solve 0
        (Scalar.zero S R.⊜
          ((Scalar.zero S R.⊗ Scalar.zero S) R.⊕ Scalar.zero S)) refl
  weightedTransferAbelIdentity (b ∷ []) =
    oneBand
    where
      module R = RingBridge.Solver K
      oneBand :
        Scalar._+_ S
          (Scalar._*_ S (weight b) (transfer b))
          (Scalar.zero S)
        ≡
        Scalar._+_ S
          (Scalar._*_ S (weight b)
            (Scalar._+_ S (transfer b) (Scalar.zero S)))
          (Scalar.zero S)
      oneBand = R.solve 2
        (λ w q →
          ((w R.⊗ q) R.⊕ Scalar.zero S)
          R.⊜
          ((w R.⊗ (q R.⊕ Scalar.zero S)) R.⊕ Scalar.zero S))
        refl (weight b) (transfer b)
  weightedTransferAbelIdentity (b0 ∷ b1 ∷ rest) =
    let
      tail = b1 ∷ rest
      tailIdentity = weightedTransferAbelIdentity tail

      exposeTail :
        Scalar._+_ S
          (Scalar._*_ S (weight b0) (transfer b0))
          (weightedTransfer tail)
        ≡
        Scalar._+_ S
          (Scalar._*_ S (weight b0) (transfer b0))
          (Scalar._+_ S
            (Scalar._*_ S (baseWeight tail) (totalTransfer tail))
            (radialLayerCake tail))
      exposeTail =
        cong
          (Scalar._+_ S (Scalar._*_ S (weight b0) (transfer b0)))
          tailIdentity

      endpoint :
        Scalar._+_ S
          (Scalar._*_ S (weight b0) (transfer b0))
          (Scalar._+_ S
            (Scalar._*_ S (baseWeight tail) (totalTransfer tail))
            (radialLayerCake tail))
        ≡
        Scalar._+_ S
          (Scalar._*_ S (weight b0)
            (Scalar._+_ S (transfer b0) (totalTransfer tail)))
          (Scalar._+_ S
            (Scalar._*_ S
              (sub (weight b1) (weight b0))
              (totalTransfer tail))
            (radialLayerCake tail))
      endpoint =
        polynomial
        where
          module R = RingBridge.Solver K
          polynomial = R.solve 5
            (λ w0 q0 w1 Q L →
              ((w0 R.⊗ q0) R.⊕ ((w1 R.⊗ Q) R.⊕ L))
              R.⊜
              ((w0 R.⊗ (q0 R.⊕ Q))
                R.⊕ (((w1 R.⊕ (R.⊝ w0)) R.⊗ Q) R.⊕ L)))
            refl
            (weight b0) (transfer b0) (weight b1)
            (totalTransfer tail) (radialLayerCake tail)
    in
    trans exposeTail endpoint

  conservativeWeightedTransferIsLayerCake :
    (bands : List BandTransfer) →
    totalTransfer bands ≡ Scalar.zero S →
    weightedTransfer bands ≡ radialLayerCake bands
  conservativeWeightedTransferIsLayerCake bands conservation =
    trans
      (weightedTransferAbelIdentity bands)
      (trans
        (cong
          (λ total →
            Scalar._+_ S
              (Scalar._*_ S (baseWeight bands) total)
              (radialLayerCake bands))
          conservation)
        zeroEndpoint)
    where
      module R = RingBridge.Solver K
      zeroEndpoint :
        Scalar._+_ S
          (Scalar._*_ S (baseWeight bands) (Scalar.zero S))
          (radialLayerCake bands)
        ≡ radialLayerCake bands
      zeroEndpoint = R.solve 2
        (λ w L → ((w R.⊗ Scalar.zero S) R.⊕ L) R.⊜ L)
        refl (baseWeight bands) (radialLayerCake bands)

round105GenericRadialAbelLayerCakeClosed : Bool
round105GenericRadialAbelLayerCakeClosed = true

round105RationalWeightRestrictionRemoved : Bool
round105RationalWeightRestrictionRemoved = true

round105GenericRadialAbelLayerCakeClosedIsTrue :
  round105GenericRadialAbelLayerCakeClosed ≡ true
round105GenericRadialAbelLayerCakeClosedIsTrue = refl

round105RationalWeightRestrictionRemovedIsTrue :
  round105RationalWeightRestrictionRemoved ≡ true
round105RationalWeightRestrictionRemovedIsTrue = refl
