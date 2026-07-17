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
PointAdjointField4 N group adj =
  Cube4 N → Vector adj

BondAdjointField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointAdditiveModule group →
  Set
BondAdjointField4 N group adj =
  DirectedBond4 N → Vector adj

transformPointField :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (adj : AdjointAdditiveModule group) →
  GaugeFunction4 N group →
  PointAdjointField4 N group adj →
  PointAdjointField4 N group adj
transformPointField group adj gauge phi x =
  action adj (gauge x) (phi x)

covariantDerivative :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (adj : AdjointAdditiveModule group) →
  DirectedGaugeField4 N group →
  PointAdjointField4 N group adj →
  BondAdjointField4 N group adj
covariantDerivative group adj U phi b =
  subtract adj
    (action adj (U b) (phi (target b)))
    (phi (source b))

inverseActionCancels :
  (group : GroupStructure) →
  (adj : AdjointAdditiveModule group) →
  (g : Carrier group) →
  (X : Vector adj) →
  action adj (inverse group g) (action adj g X) ≡ X
inverseActionCancels group adj g X =
  trans
    (sym
      (actionMultiply adj (inverse group g) g X))
    (trans
      (cong (λ h → action adj h X) (inverseLeft group g))
      (actionUnit adj X))

gaugeTransformedTransport :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (adj : AdjointAdditiveModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (phi : PointAdjointField4 N group adj) →
  (b : DirectedBond4 N) →
  action adj
    (gaugeTransformBond group gauge U b)
    (transformPointField group adj gauge phi (target b))
  ≡
  action adj
    (gauge (source b))
    (action adj (U b) (phi (target b)))
gaugeTransformedTransport group adj gauge U phi b =
  trans
    (actionMultiply adj
      (gauge (source b))
      (multiply group (U b) (inverse group (gauge (target b))))
      (action adj (gauge (target b)) (phi (target b))))
    (cong
      (action adj (gauge (source b)))
      (trans
        (actionMultiply adj
          (U b)
          (inverse group (gauge (target b)))
          (action adj (gauge (target b)) (phi (target b))))
        (cong
          (action adj (U b))
          (inverseActionCancels
            group adj
            (gauge (target b))
            (phi (target b))))))

covariantDerivativeGaugeCovariant :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (adj : AdjointAdditiveModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (phi : PointAdjointField4 N group adj) →
  (b : DirectedBond4 N) →
  covariantDerivative group adj
    (gaugeTransformBond group gauge U)
    (transformPointField group adj gauge phi)
    b
  ≡
  action adj
    (gauge (source b))
    (covariantDerivative group adj U phi b)
covariantDerivativeGaugeCovariant
  group adj gauge U phi b =
  trans
    (cong
      (λ transported →
        subtract adj
          transported
          (action adj (gauge (source b)) (phi (source b))))
      (gaugeTransformedTransport group adj gauge U phi b))
    (sym
      (actionSubtract adj
        (gauge (source b))
        (action adj (U b) (phi (target b)))
        (phi (source b))))
