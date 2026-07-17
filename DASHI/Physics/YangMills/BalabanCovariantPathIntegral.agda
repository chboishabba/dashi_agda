module DASHI.Physics.YangMills.BalabanCovariantPathIntegral where

------------------------------------------------------------------------
-- Covariant Lie-algebra line integral along an endpoint-indexed lattice path.
--
-- For p = (b0,...,bn), based at b0-, define
--
--   I_U(A;p)
--     = A(b0) + Ad(U(b0)) A(b1) + ... .
--
-- This is the literal algebra behind CMP 98's expressions
-- `(R_{0,y} A)(F)` and CMP 99's plaquette derivative (3.4).  We prove both
-- gauge covariance and the concatenation law.  The remaining source work is
-- to choose Bałaban's block paths and weights, not to postulate these laws.
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
  ; append
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure
  ; Carrier
  ; unit
  ; multiply
  ; inverse
  )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  ; directedPathTransport
  )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( AdjointAdditiveModule
  ; Vector
  ; action
  ; actionUnit
  ; actionMultiply
  ; inverseActionCancels
  )

record AdjointLinearModule (group : GroupStructure) : Set₁ where
  field
    additive : AdjointAdditiveModule group

    zeroVector : Vector additive
    addVector : Vector additive → Vector additive → Vector additive

    addAssociative :
      ∀ X Y Z →
      addVector (addVector X Y) Z
        ≡ addVector X (addVector Y Z)

    zeroLeft :
      ∀ X →
      addVector zeroVector X ≡ X

    zeroRight :
      ∀ X →
      addVector X zeroVector ≡ X

    actionZero :
      ∀ g →
      action additive g zeroVector ≡ zeroVector

    actionAdd :
      ∀ g X Y →
      action additive g (addVector X Y)
        ≡ addVector
            (action additive g X)
            (action additive g Y)

open AdjointLinearModule public

DirectedAdjointBondField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointLinearModule group →
  Set
DirectedAdjointBondField4 N group linear =
  DirectedBond4 N → Vector (additive linear)

transformAdjointBondField :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  GaugeFunction4 N group →
  DirectedAdjointBondField4 N group linear →
  DirectedAdjointBondField4 N group linear
transformAdjointBondField group linear gauge A b =
  action (additive linear) (gauge (source b)) (A b)

covariantPathIntegral :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {x y : Cube4 N} →
  LatticePath4 x y →
  Vector (additive linear)
covariantPathIntegral group linear U A empty =
  zeroVector linear
covariantPathIntegral group linear U A (b ▷ p) =
  addVector linear
    (A b)
    (action (additive linear) (U b)
      (covariantPathIntegral group linear U A p))

gaugeTransformedAction :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (b : DirectedBond4 N) →
  (X : Vector (additive linear)) →
  action (additive linear)
    (gaugeTransformBond group gauge U b)
    (action (additive linear) (gauge (target b)) X)
  ≡
  action (additive linear)
    (gauge (source b))
    (action (additive linear) (U b) X)
gaugeTransformedAction group linear gauge U b X =
  trans
    (actionMultiply (additive linear)
      (gauge (source b))
      (multiply group (U b) (inverse group (gauge (target b))))
      (action (additive linear) (gauge (target b)) X))
    (cong
      (action (additive linear) (gauge (source b)))
      (trans
        (actionMultiply (additive linear)
          (U b)
          (inverse group (gauge (target b)))
          (action (additive linear) (gauge (target b)) X))
        (cong
          (action (additive linear) (U b))
          (inverseActionCancels
            group (additive linear) (gauge (target b)) X))))

covariantPathIntegralGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {x y : Cube4 N} →
  (p : LatticePath4 x y) →
  covariantPathIntegral group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    p
  ≡
  action (additive linear) (gauge x)
    (covariantPathIntegral group linear U A p)
covariantPathIntegralGaugeCovariant
  group linear gauge U A {x = x} empty =
  sym (actionZero linear (gauge x))
covariantPathIntegralGaugeCovariant
  group linear gauge U A (b ▷ p) =
  trans
    (cong
      (addVector linear
        (action (additive linear) (gauge (source b)) (A b)))
      (trans
        (cong
          (action (additive linear)
            (gaugeTransformBond group gauge U b))
          (covariantPathIntegralGaugeCovariant
            group linear gauge U A p))
        (gaugeTransformedAction
          group linear gauge U b
          (covariantPathIntegral group linear U A p))))
    (sym
      (actionAdd linear
        (gauge (source b))
        (A b)
        (action (additive linear) (U b)
          (covariantPathIntegral group linear U A p))))

covariantPathIntegralAppend :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {x y z : Cube4 N} →
  (p : LatticePath4 x y) →
  (q : LatticePath4 y z) →
  covariantPathIntegral group linear U A (append p q)
  ≡
  addVector linear
    (covariantPathIntegral group linear U A p)
    (action (additive linear)
      (directedPathTransport group U p)
      (covariantPathIntegral group linear U A q))
covariantPathIntegralAppend group linear U A empty q =
  sym
    (trans
      (cong
        (addVector linear (zeroVector linear))
        (actionUnit (additive linear)
          (covariantPathIntegral group linear U A q)))
      (zeroLeft linear
        (covariantPathIntegral group linear U A q)))
covariantPathIntegralAppend group linear U A (b ▷ p) q =
  trans
    (cong
      (addVector linear (A b))
      (trans
        (cong
          (action (additive linear) (U b))
          (covariantPathIntegralAppend group linear U A p q))
        (actionAdd linear
          (U b)
          (covariantPathIntegral group linear U A p)
          (action (additive linear)
            (directedPathTransport group U p)
            (covariantPathIntegral group linear U A q)))))
    (trans
      (addAssociative linear
        (A b)
        (action (additive linear) (U b)
          (covariantPathIntegral group linear U A p))
        (action (additive linear) (U b)
          (action (additive linear)
            (directedPathTransport group U p)
            (covariantPathIntegral group linear U A q))))
      (cong
        (addVector linear
          (addVector linear
            (A b)
            (action (additive linear) (U b)
              (covariantPathIntegral group linear U A p))))
        (sym
          (actionMultiply (additive linear)
            (U b)
            (directedPathTransport group U p)
            (covariantPathIntegral group linear U A q)))))
