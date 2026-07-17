module DASHI.Physics.YangMills.BalabanPlaquetteCovariantDerivative where

------------------------------------------------------------------------
-- Literal plaquette derivative of an adjoint-valued bond field.
--
-- CMP 99 (3.4) is the covariant line integral of A around the positively
-- oriented plaquette boundary.  The boundary and every transport factor are
-- already concrete, so the operator below is a genuine finite-lattice
-- construction.  Its gauge covariance follows from the proved path-integral
-- theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( Vector
  ; action
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule
  ; additive
  ; DirectedAdjointBondField4
  ; transformAdjointBondField
  ; covariantPathIntegral
  ; covariantPathIntegralGaugeCovariant
  )
open import DASHI.Physics.YangMills.BalabanPeriodicPlaquetteHolonomy using
  ( AxisPair4
  ; plaquetteBoundary
  )

PlaquetteAdjointField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointLinearModule group →
  Set
PlaquetteAdjointField4 N group linear =
  AxisPair4 → Cube4 N → Vector (additive linear)

plaquetteCovariantDerivative :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  PlaquetteAdjointField4 N group linear
plaquetteCovariantDerivative group linear U A pair x =
  covariantPathIntegral
    group linear U A (plaquetteBoundary pair x)

plaquetteCovariantDerivativeGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  (pair : AxisPair4) →
  (x : Cube4 N) →
  plaquetteCovariantDerivative group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    pair x
  ≡
  action (additive linear) (gauge x)
    (plaquetteCovariantDerivative group linear U A pair x)
plaquetteCovariantDerivativeGaugeCovariant
  group linear gauge U A pair x =
  covariantPathIntegralGaugeCovariant
    group linear gauge U A (plaquetteBoundary pair x)
