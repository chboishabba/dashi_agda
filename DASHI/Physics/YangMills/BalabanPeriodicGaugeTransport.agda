module DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport where

------------------------------------------------------------------------
-- Group-valued gauge fields and path transport on the literal periodic
-- lattice carrier.
--
-- A gauge field is stored only on positively oriented bonds.  Transport on a
-- backward bond is defined as the inverse of the corresponding positive-bond
-- value at the neighbouring source.  The reverse-bond and concatenation laws
-- are then proved from the group laws and the periodic shift identities.
--
-- The group is still a parameter because DASHI has no concrete SU(2) matrix
-- carrier.  The lattice geometry and all transport constructions are literal.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; Axis4
  ; forward
  ; backward
  ; shiftBackward
  ; shiftForwardBackward
  ; shiftBackwardForward
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; bond4
  ; reverseBond
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  ( LatticePath4
  ; empty
  ; _▷_
  ; append
  )

record GroupStructure : Set₁ where
  field
    Carrier : Set
    unit : Carrier
    multiply : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier

    multiplyAssoc :
      ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)

    unitLeft :
      ∀ a →
      multiply unit a ≡ a

    unitRight :
      ∀ a →
      multiply a unit ≡ a

    inverseLeft :
      ∀ a →
      multiply (inverse a) a ≡ unit

    inverseRight :
      ∀ a →
      multiply a (inverse a) ≡ unit

    inverseInvolutive :
      ∀ a →
      inverse (inverse a) ≡ a

open GroupStructure public

GaugeField4 :
  (N : Nat) →
  GroupStructure →
  Set
GaugeField4 N group =
  Cube4 N → Axis4 → Carrier group

bondTransport :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  GaugeField4 N group →
  DirectedBond4 N →
  Carrier group
bondTransport group U (bond4 x a forward) = U x a
bondTransport group U (bond4 x a backward) =
  inverse group (U (shiftBackward a x) a)

pathTransport :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (U : GaugeField4 N group) →
  {x y : Cube4 N} →
  LatticePath4 x y →
  Carrier group
pathTransport group U empty = unit group
pathTransport group U (b ▷ p) =
  multiply group
    (bondTransport group U b)
    (pathTransport group U p)

pathTransportAppend :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (U : GaugeField4 N group) →
  {x y z : Cube4 N} →
  (p : LatticePath4 x y) →
  (q : LatticePath4 y z) →
  pathTransport group U (append p q)
    ≡ multiply group
        (pathTransport group U p)
        (pathTransport group U q)
pathTransportAppend group U empty q =
  sym (unitLeft group (pathTransport group U q))
pathTransportAppend group U (b ▷ p) q =
  trans
    (cong
      (multiply group (bondTransport group U b))
      (pathTransportAppend group U p q))
    (sym
      (multiplyAssoc group
        (bondTransport group U b)
        (pathTransport group U p)
        (pathTransport group U q)))

bondTransportReverse :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (U : GaugeField4 N group) →
  (b : DirectedBond4 N) →
  bondTransport group U (reverseBond b)
    ≡ inverse group (bondTransport group U b)
bondTransportReverse group U (bond4 x a forward) =
  cong
    (inverse group)
    (cong (λ y → U y a) (shiftBackwardForward a x))
bondTransportReverse group U (bond4 x a backward) =
  sym
    (inverseInvolutive group (U (shiftBackward a x) a))

bondTransportBacktrack :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (U : GaugeField4 N group) →
  (b : DirectedBond4 N) →
  multiply group
    (bondTransport group U b)
    (bondTransport group U (reverseBond b))
  ≡ unit group
bondTransportBacktrack group U b =
  trans
    (cong
      (multiply group (bondTransport group U b))
      (bondTransportReverse group U b))
    (inverseRight group (bondTransport group U b))

reverseBondTransportBacktrack :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (U : GaugeField4 N group) →
  (b : DirectedBond4 N) →
  multiply group
    (bondTransport group U (reverseBond b))
    (bondTransport group U b)
  ≡ unit group
reverseBondTransportBacktrack group U b =
  trans
    (cong
      (λ q → multiply group q (bondTransport group U b))
      (bondTransportReverse group U b))
    (inverseLeft group (bondTransport group U b))
