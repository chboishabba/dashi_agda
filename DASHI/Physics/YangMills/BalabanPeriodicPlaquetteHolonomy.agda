module DASHI.Physics.YangMills.BalabanPeriodicPlaquetteHolonomy where

------------------------------------------------------------------------
-- Positive plaquettes and their ordered boundary holonomy.
--
-- CMP 98 (5), (7)--(9) treats a positive plaquette as the four-bond contour
--
--   x -> x+mu -> x+mu+nu -> x+nu -> x,   mu < nu.
--
-- This module constructs exactly that endpoint-indexed path on the periodic
-- four-dimensional lattice and derives its gauge transformation by the path
-- covariance theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; Axis4
  ; axis₀
  ; axis₁
  ; axis₂
  ; axis₃
  ; shiftForward
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( positiveBond )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  ( LatticePath4
  ; _▷_
  ; append
  ; reverseSingle
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure
  ; Carrier
  ; GaugeField4
  ; bondTransport
  ; multiply
  ; inverse
  )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( GaugeFunction4
  ; gaugeTransformBond
  ; directedPathTransport
  ; pathTransportGaugeCovariant
  )

data AxisPair4 : Set where
  axes01 axes02 axes03 axes12 axes13 axes23 : AxisPair4

firstAxis : AxisPair4 → Axis4
firstAxis axes01 = axis₀
firstAxis axes02 = axis₀
firstAxis axes03 = axis₀
firstAxis axes12 = axis₁
firstAxis axes13 = axis₁
firstAxis axes23 = axis₂

secondAxis : AxisPair4 → Axis4
secondAxis axes01 = axis₁
secondAxis axes02 = axis₂
secondAxis axes03 = axis₃
secondAxis axes12 = axis₂
secondAxis axes13 = axis₃
secondAxis axes23 = axis₃

shiftPairCommutes :
  ∀ {N : Nat} {{_ : NonZero N}}
  (pair : AxisPair4) (x : Cube4 N) →
  shiftForward (secondAxis pair)
    (shiftForward (firstAxis pair) x)
  ≡
  shiftForward (firstAxis pair)
    (shiftForward (secondAxis pair) x)
shiftPairCommutes axes01 (cube4 x₀ x₁ x₂ x₃) = refl
shiftPairCommutes axes02 (cube4 x₀ x₁ x₂ x₃) = refl
shiftPairCommutes axes03 (cube4 x₀ x₁ x₂ x₃) = refl
shiftPairCommutes axes12 (cube4 x₀ x₁ x₂ x₃) = refl
shiftPairCommutes axes13 (cube4 x₀ x₁ x₂ x₃) = refl
shiftPairCommutes axes23 (cube4 x₀ x₁ x₂ x₃) = refl

transportStart :
  ∀ {N : Nat} {{_ : NonZero N}}
  {x x' y : Cube4 N} →
  x ≡ x' →
  LatticePath4 x y →
  LatticePath4 x' y
transportStart eq p = subst (λ z → LatticePath4 z _) eq p

plaquetteBoundary :
  ∀ {N : Nat} {{_ : NonZero N}}
  (pair : AxisPair4) (x : Cube4 N) →
  LatticePath4 x x
plaquetteBoundary pair x =
  positiveBond x mu ▷
  positiveBond (shiftForward mu x) nu ▷
  transportStart
    (sym (shiftPairCommutes pair x))
    (append
      (reverseSingle
        (positiveBond (shiftForward nu x) mu))
      (reverseSingle
        (positiveBond x nu)))
  where
    mu : Axis4
    mu = firstAxis pair

    nu : Axis4
    nu = secondAxis pair

plaquetteHolonomy :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (U : GaugeField4 N group) →
  AxisPair4 →
  Cube4 N →
  Carrier group
plaquetteHolonomy group U pair x =
  directedPathTransport
    group
    (bondTransport group U)
    (plaquetteBoundary pair x)

plaquetteHolonomyGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (gauge : GaugeFunction4 N group) →
  (U : GaugeField4 N group) →
  (pair : AxisPair4) →
  (x : Cube4 N) →
  directedPathTransport group
    (gaugeTransformBond group gauge (bondTransport group U))
    (plaquetteBoundary pair x)
  ≡
  multiply group
    (gauge x)
    (multiply group
      (plaquetteHolonomy group U pair x)
      (inverse group (gauge x)))
plaquetteHolonomyGaugeCovariant group gauge U pair x =
  pathTransportGaugeCovariant
    group gauge (bondTransport group U)
    (plaquetteBoundary pair x)
