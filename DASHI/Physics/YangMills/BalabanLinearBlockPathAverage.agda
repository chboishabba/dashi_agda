module DASHI.Physics.YangMills.BalabanLinearBlockPathAverage where

------------------------------------------------------------------------
-- Gauge-covariant finite block-path average.
--
-- CMP 98 (125) has the source main term
--
--   (Q_0(V) A)_c
--     = sum_{x in B(c-)} L^{-(d+1)}
--         (R_{0,c-} A)([x,x']).
--
-- A rooted sample below consists of a prefix from c- to x and the segment
-- [x,x'].  `transportedSegmentIntegral` is exactly the segment integral
-- transported back to c-.  The finite normalized sum is then constructed and
-- proved gauge covariant at the root.
--
-- The list of Bałaban block samples and the numerical weight L^{-(d+1)} are
-- still explicit inputs.  This module proves their operator algebra; it does
-- not assert that an arbitrary list is the source block geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  ( LatticePath4 )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure
  ; multiply
  ; inverse
  )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  ; directedPathTransport
  ; pathTransportGaugeCovariant
  )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( Vector
  ; action
  ; actionMultiply
  ; inverseActionCancels
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule
  ; additive
  ; zeroVector
  ; addVector
  ; actionZero
  ; actionAdd
  ; DirectedAdjointBondField4
  ; transformAdjointBondField
  ; covariantPathIntegral
  ; covariantPathIntegralGaugeCovariant
  )

record RootedSegmentSample
  {N : Nat} {{_ : NonZero N}}
  (root : Cube4 N) : Set where
  constructor rootedSegment
  field
    junction endpoint : Cube4 N
    prefix : LatticePath4 root junction
    segment : LatticePath4 junction endpoint

open RootedSegmentSample public

transportedSegmentIntegral :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {root : Cube4 N} →
  RootedSegmentSample root →
  Vector (additive linear)
transportedSegmentIntegral group linear U A sample =
  action (additive linear)
    (directedPathTransport group U (prefix sample))
    (covariantPathIntegral group linear U A (segment sample))

conjugatedTransportAction :
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gRoot transport gJunction :
    DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport.Carrier group) →
  (X : Vector (additive linear)) →
  action (additive linear)
    (multiply group gRoot
      (multiply group transport (inverse group gJunction)))
    (action (additive linear) gJunction X)
  ≡
  action (additive linear) gRoot
    (action (additive linear) transport X)
conjugatedTransportAction
  group linear gRoot transport gJunction X =
  trans
    (actionMultiply (additive linear)
      gRoot
      (multiply group transport (inverse group gJunction))
      (action (additive linear) gJunction X))
    (cong
      (action (additive linear) gRoot)
      (trans
        (actionMultiply (additive linear)
          transport
          (inverse group gJunction)
          (action (additive linear) gJunction X))
        (cong
          (action (additive linear) transport)
          (inverseActionCancels
            group (additive linear) gJunction X))))

transportedSegmentIntegralGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {root : Cube4 N} →
  (sample : RootedSegmentSample root) →
  transportedSegmentIntegral group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    sample
  ≡
  action (additive linear) (gauge root)
    (transportedSegmentIntegral group linear U A sample)
transportedSegmentIntegralGaugeCovariant
  group linear gauge U A sample =
  trans
    (cong
      (action (additive linear)
        (directedPathTransport group
          (gaugeTransformBond group gauge U)
          (prefix sample)))
      (covariantPathIntegralGaugeCovariant
        group linear gauge U A (segment sample)))
    (trans
      (cong
        (λ transport →
          action (additive linear) transport
            (action (additive linear)
              (gauge (junction sample))
              (covariantPathIntegral
                group linear U A (segment sample))))
        (pathTransportGaugeCovariant
          group gauge U (prefix sample)))
      (conjugatedTransportAction
        group linear
        (gauge _)
        (directedPathTransport group U (prefix sample))
        (gauge (junction sample))
        (covariantPathIntegral group linear U A (segment sample))))

rootedSampleSum :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {root : Cube4 N} →
  List (RootedSegmentSample root) →
  Vector (additive linear)
rootedSampleSum group linear U A [] = zeroVector linear
rootedSampleSum group linear U A (sample ∷ samples) =
  addVector linear
    (transportedSegmentIntegral group linear U A sample)
    (rootedSampleSum group linear U A samples)

rootedSampleSumGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (linear : AdjointLinearModule group) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group linear) →
  {root : Cube4 N} →
  (samples : List (RootedSegmentSample root)) →
  rootedSampleSum group linear
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField group linear gauge A)
    samples
  ≡
  action (additive linear) (gauge root)
    (rootedSampleSum group linear U A samples)
rootedSampleSumGaugeCovariant
  group linear gauge U A {root = root} [] =
  trans refl (actionZero linear (gauge root))
rootedSampleSumGaugeCovariant
  group linear gauge U A (sample ∷ samples) =
  trans
    (cong
      (λ tail →
        addVector linear
          (transportedSegmentIntegral group linear
            (gaugeTransformBond group gauge U)
            (transformAdjointBondField group linear gauge A)
            sample)
          tail)
      (rootedSampleSumGaugeCovariant
        group linear gauge U A samples))
    (trans
      (cong
        (λ head →
          addVector linear head
            (action (additive linear) (gauge _)
              (rootedSampleSum group linear U A samples)))
        (transportedSegmentIntegralGaugeCovariant
          group linear gauge U A sample))
      (trans refl
        (DASHI.Physics.YangMills.BalabanPeriodicLatticePaths.transportEndpoint
          refl
          refl)))

record ScalarAdjointLinearModule (group : GroupStructure) : Set₁ where
  field
    linear : AdjointLinearModule group
    Scalar : Set
    scale : Scalar → Vector (additive linear) → Vector (additive linear)

    actionScale :
      ∀ g scalar X →
      action (additive linear) g (scale scalar X)
        ≡ scale scalar (action (additive linear) g X)

open ScalarAdjointLinearModule public

linearBlockPathAverage :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (scalarLinear : ScalarAdjointLinearModule group) →
  (weight : Scalar scalarLinear) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group
    (linear scalarLinear)) →
  {root : Cube4 N} →
  List (RootedSegmentSample root) →
  Vector (additive (linear scalarLinear))
linearBlockPathAverage group scalarLinear weight U A samples =
  scale scalarLinear weight
    (rootedSampleSum group (linear scalarLinear) U A samples)
