module DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative where

------------------------------------------------------------------------
-- Literal point-to-bond covariant derivative in the adjoint representation.
--
-- CMP 99 (3.3) uses
--
--   (D_U phi)(b) = Ad(U(b)) phi(b+) - phi(b-).
--
-- Here the periodic directed bond supplies b- and b+ literally.  The theorem
-- below proves covariance under
--
--   U^u(b)   = u(b-) U(b) u(b+)^-1,
--   phi^u(x) = Ad(u(x)) phi(x).
--
-- The group and its additive adjoint module are parameters because the repo
-- still has no concrete SU(2) matrix/Lie-algebra carrier.  All lattice and
-- covariance algebra is proved; no source theorem or analytic estimate is
-- assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; source
  ; target
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure
  ; Carrier
  ; unit
  ; multiply
  ; inverse
  ; inverseLeft
  )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  )

record AdjointAdditiveModule (group : GroupStructure) : Set₁ where
  field
    Vector : Set
    subtract : Vector → Vector → Vector
    action : Carrier group → Vector → Vector

    actionUnit :
      ∀ X →
      action (unit group) X ≡ X

    actionMultiply :
      ∀ g h X →
      action (multiply group g h) X
        ≡ action g (action h X)

    actionSubtract :
      ∀ g X Y →
      action g (subtract X Y)
        ≡ subtract (action g X) (action g Y)

open AdjointAdditiveModule public

PointAdjointField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointAdditiveModule group →
  Set
PointAdjointField4 N group module =
  Cube4 N → Vector module

BondAdjointField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointAdditiveModule group →
  Set
BondAdjointField4 N group module =
  DirectedBond4 N → Vector module

transformPointField :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (module : AdjointAdditiveModule group) →
  GaugeFunction4 N group →
  PointAdjointField4 N group module →
  PointAdjointField4 N group module
transformPointField group module gauge phi x =
  action module (gauge x) (phi x)

covariantDerivative :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (module : AdjointAdditiveModule group) →
  DirectedGaugeField4 N group →
  PointAdjointField4 N group module →
  BondAdjointField4 N group module
covariantDerivative group module U phi b =
  subtract module
    (action module (U b) (phi (target b)))
    (phi (source b))

inverseActionCancels :
  (group : GroupStructure) →
  (module : AdjointAdditiveModule group) →
  (g : Carrier group) →
  (X : Vector module) →
  action module (inverse group g) (action module g X) ≡ X
inverseActionCancels group module g X =
  trans
    (sym
      (actionMultiply module (inverse group g) g X))
    (trans
      (cong (λ h → action module h X) (inverseLeft group g))
      (actionUnit module X))

gaugeTransformedTransport :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (module : AdjointAdditiveModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (phi : PointAdjointField4 N group module) →
  (b : DirectedBond4 N) →
  action module
    (gaugeTransformBond group gauge U b)
    (transformPointField group module gauge phi (target b))
  ≡
  action module
    (gauge (source b))
    (action module (U b) (phi (target b)))
gaugeTransformedTransport group module gauge U phi b =
  trans
    (actionMultiply module
      (gauge (source b))
      (multiply group (U b) (inverse group (gauge (target b))))
      (action module (gauge (target b)) (phi (target b))))
    (cong
      (action module (gauge (source b)))
      (trans
        (actionMultiply module
          (U b)
          (inverse group (gauge (target b)))
          (action module (gauge (target b)) (phi (target b))))
        (cong
          (action module (U b))
          (inverseActionCancels
            group module
            (gauge (target b))
            (phi (target b))))))

covariantDerivativeGaugeCovariant :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (module : AdjointAdditiveModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (phi : PointAdjointField4 N group module) →
  (b : DirectedBond4 N) →
  covariantDerivative group module
    (gaugeTransformBond group gauge U)
    (transformPointField group module gauge phi)
    b
  ≡
  action module
    (gauge (source b))
    (covariantDerivative group module U phi b)
covariantDerivativeGaugeCovariant
  group module gauge U phi b =
  trans
    (cong
      (λ transported →
        subtract module
          transported
          (action module (gauge (source b)) (phi (source b))))
      (gaugeTransformedTransport group module gauge U phi b))
    (sym
      (actionSubtract module
        (gauge (source b))
        (action module (U b) (phi (target b)))
        (phi (source b))))
