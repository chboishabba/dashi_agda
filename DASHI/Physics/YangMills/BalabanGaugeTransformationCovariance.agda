module DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance where

------------------------------------------------------------------------
-- Literal gauge transformation and contour covariance.
--
-- CMP 98 (7)--(9) defines
--
--   U^u(x,y) = u(x) U(x,y) u(y)^-1
--
-- and the ordered product U(F) along an oriented contour.  This module proves
-- directly on the periodic lattice carrier that
--
--   U^u(F : x -> y) = u(x) U(F) u(y)^-1.
--
-- The proof uses only endpoint-indexed path composition and the group laws.
-- No averaging theorem or analytic small-field premise occurs here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; source
  ; target
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  ( LatticePath4
  ; empty
  ; _▷_
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure
  ; Carrier
  ; unit
  ; multiply
  ; inverse
  ; multiplyAssoc
  ; unitLeft
  ; inverseLeft
  ; inverseRight
  )

DirectedGaugeField4 :
  (N : Nat) →
  GroupStructure →
  Set
DirectedGaugeField4 N group =
  DirectedBond4 N → Carrier group

GaugeFunction4 :
  (N : Nat) →
  GroupStructure →
  Set
GaugeFunction4 N group =
  Cube4 N → Carrier group

gaugeTransformBond :
  ∀ {N : Nat}
  (group : GroupStructure) →
  GaugeFunction4 N group →
  DirectedGaugeField4 N group →
  DirectedBond4 N →
  Carrier group
gaugeTransformBond group gauge U b =
  multiply group
    (gauge (source b))
    (multiply group
      (U b)
      (inverse group (gauge (target b))))

directedPathTransport :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  DirectedGaugeField4 N group →
  {x y : Cube4 N} →
  LatticePath4 x y →
  Carrier group
directedPathTransport group U empty = unit group
directedPathTransport group U (b ▷ p) =
  multiply group
    (U b)
    (directedPathTransport group U p)

cancelInverseMiddle :
  (group : GroupStructure) →
  (a r : Carrier group) →
  multiply group
    (inverse group a)
    (multiply group a r)
  ≡ r
cancelInverseMiddle group a r =
  trans
    (sym
      (multiplyAssoc group
        (inverse group a)
        a
        r))
    (trans
      (cong
        (λ q → multiply group q r)
        (inverseLeft group a))
      (unitLeft group r))

composeGaugeCovariantFactors :
  (group : GroupStructure) →
  (gStart first gMiddle second gEnd : Carrier group) →
  multiply group
    (multiply group
      gStart
      (multiply group first (inverse group gMiddle)))
    (multiply group
      gMiddle
      (multiply group second (inverse group gEnd)))
  ≡
  multiply group
    gStart
    (multiply group
      (multiply group first second)
      (inverse group gEnd))
composeGaugeCovariantFactors
  group gStart first gMiddle second gEnd =
  trans
    (multiplyAssoc group
      gStart
      (multiply group first (inverse group gMiddle))
      (multiply group
        gMiddle
        (multiply group second (inverse group gEnd))))
    (cong
      (multiply group gStart)
      (trans
        (multiplyAssoc group
          first
          (inverse group gMiddle)
          (multiply group
            gMiddle
            (multiply group second (inverse group gEnd))))
        (trans
          (cong
            (multiply group first)
            (cancelInverseMiddle
              group
              gMiddle
              (multiply group second (inverse group gEnd))))
          (sym
            (multiplyAssoc group
              first
              second
              (inverse group gEnd))))))

emptyPathGaugeCovariant :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (gauge : GaugeFunction4 N group) →
  (x : Cube4 N) →
  unit group
  ≡
  multiply group
    (gauge x)
    (multiply group
      (unit group)
      (inverse group (gauge x)))
emptyPathGaugeCovariant group gauge x =
  sym
    (trans
      (cong
        (multiply group (gauge x))
        (unitLeft group (inverse group (gauge x))))
      (inverseRight group (gauge x)))

pathTransportGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  {x y : Cube4 N} →
  (p : LatticePath4 x y) →
  directedPathTransport group
    (gaugeTransformBond group gauge U)
    p
  ≡
  multiply group
    (gauge x)
    (multiply group
      (directedPathTransport group U p)
      (inverse group (gauge y)))
pathTransportGaugeCovariant group gauge U {x = x} empty =
  emptyPathGaugeCovariant group gauge x
pathTransportGaugeCovariant group gauge U (b ▷ p) =
  trans
    (cong
      (multiply group (gaugeTransformBond group gauge U b))
      (pathTransportGaugeCovariant group gauge U p))
    (composeGaugeCovariantFactors
      group
      (gauge (source b))
      (U b)
      (gauge (target b))
      (directedPathTransport group U p)
      _)
