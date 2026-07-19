module DASHI.Physics.YangMills.BalabanSU2AdjointPathTransport where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  (LatticePath4; append)
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  (GaugeField4; pathTransport; pathTransportAppend)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (SU2Quaternion; su2QuaternionGroup)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Adjoint; su2AdjointMultiply)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot; su2DotAdjointInvariant)

SU2GaugeField4 : Nat → Set
SU2GaugeField4 N = GaugeField4 N su2QuaternionGroup

su2PathTransport :
  ∀ {N : Nat} {{_ : NonZero N}} →
  SU2GaugeField4 N → {x y : Cube4 N} → LatticePath4 x y → SU2Quaternion
su2PathTransport = pathTransport su2QuaternionGroup

su2AdjointPathTransport :
  ∀ {N : Nat} {{_ : NonZero N}} →
  SU2GaugeField4 N → {x y : Cube4 N} → LatticePath4 x y →
  SU2LieAlgebra → SU2LieAlgebra
su2AdjointPathTransport U path X = su2Adjoint (su2PathTransport U path) X

su2AdjointPathTransportAppend :
  ∀ {N : Nat} {{_ : NonZero N}}
  (U : SU2GaugeField4 N) {x y z : Cube4 N}
  (p : LatticePath4 x y) (q : LatticePath4 y z) X →
  su2AdjointPathTransport U (append p q) X
    ≡ su2AdjointPathTransport U p (su2AdjointPathTransport U q X)
su2AdjointPathTransportAppend U p q X =
  trans
    (cong (λ transport → su2Adjoint transport X)
      (pathTransportAppend su2QuaternionGroup U p q))
    (su2AdjointMultiply (su2PathTransport U p) (su2PathTransport U q) X)

su2AdjointPathTransportInnerInvariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (U : SU2GaugeField4 N) {x y : Cube4 N}
  (p : LatticePath4 x y) X Y →
  su2Dot (su2AdjointPathTransport U p X)
         (su2AdjointPathTransport U p Y)
    ≡ su2Dot X Y
su2AdjointPathTransportInnerInvariant U p X Y =
  su2DotAdjointInvariant (su2PathTransport U p) X Y
