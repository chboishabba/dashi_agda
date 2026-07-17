module DASHI.Physics.YangMills.BalabanSU2NestedRadialBlockPathTerm where

------------------------------------------------------------------------
-- Gauge-covariant nested radial block-path terms.
--
-- CMP 98 (124) repeatedly applies an operator at a fine-path junction,
-- transports the result to the coarse-bond root, and applies a second
-- operator there.  This module constructs precisely that typed pattern for
-- arbitrary radial reduced functions of ad_y, together with the `[operator-I]`
-- correction and its finite sample sum.
--
-- The scalar radial functions and the source-selected paths remain explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  ; directedPathTransport
  ; pathTransportGaugeCovariant
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( DirectedAdjointBondField4
  ; transformAdjointBondField
  ; covariantPathIntegral
  )
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  ( RootedSegmentSample
  ; root
  ; junction
  ; prefix
  ; segment
  ; transportedSegmentIntegral
  ; transportedSegmentIntegralGaugeCovariant
  ; conjugatedTransportAction
  )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( su2QuaternionGroup )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; lieZero
  ; lieAdd
  ; lieSubtract
  ; su2Adjoint
  ; su2AdjointAdd
  ; su2AdjointSubtract
  ; su2AdjointLinearModule
  )
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using
  ( RadialReducedOperator
  ; applyRadialReduced
  ; applyRadialReducedGaugeCovariant
  )

SU2LieField4 : Nat → Set
SU2LieField4 N = Cube4 N → SU2LieAlgebra

transformSU2LieField :
  ∀ {N : Nat} →
  GaugeFunction4 N su2QuaternionGroup →
  SU2LieField4 N →
  SU2LieField4 N
transformSU2LieField gauge Y x = su2Adjoint (gauge x) (Y x)

nestedRadialSegmentTerm :
  ∀ {N : Nat} {{_ : NonZero N}} →
  RadialReducedOperator →
  RadialReducedOperator →
  SU2LieField4 N →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule →
  {root : Cube4 N} →
  RootedSegmentSample root →
  SU2LieAlgebra
nestedRadialSegmentTerm rootOperator junctionOperator Y U A sample =
  applyRadialReduced rootOperator (Y (root sample))
    (su2Adjoint
      (directedPathTransport
        su2QuaternionGroup U (prefix sample))
      (applyRadialReduced junctionOperator (Y (junction sample))
        (covariantPathIntegral
          su2QuaternionGroup su2AdjointLinearModule
          U A (segment sample))))

nestedRadialSegmentGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (rootOperator junctionOperator : RadialReducedOperator) →
  (gauge : GaugeFunction4 N su2QuaternionGroup) →
  (Y : SU2LieField4 N) →
  (U : DirectedGaugeField4 N su2QuaternionGroup) →
  (A : DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule) →
  {root : Cube4 N} →
  (sample : RootedSegmentSample root) →
  nestedRadialSegmentTerm rootOperator junctionOperator
    (transformSU2LieField gauge Y)
    (gaugeTransformBond su2QuaternionGroup gauge U)
    (transformAdjointBondField
      su2QuaternionGroup su2AdjointLinearModule gauge A)
    sample
  ≡
  su2Adjoint (gauge root)
    (nestedRadialSegmentTerm
      rootOperator junctionOperator Y U A sample)
nestedRadialSegmentGaugeCovariant
  rootOperator junctionOperator gauge Y U A {root = root} sample =
  trans
    (cong
      (λ segmentValue →
        applyRadialReduced rootOperator
          (su2Adjoint (gauge root) (Y root))
          (su2Adjoint transformedPrefix
            (applyRadialReduced junctionOperator
              (su2Adjoint (gauge (junction sample))
                (Y (junction sample)))
              segmentValue)))
      (DASHI.Physics.YangMills.BalabanCovariantPathIntegral.covariantPathIntegralGaugeCovariant
        su2QuaternionGroup su2AdjointLinearModule gauge U A
        (segment sample)))
    (trans
      (cong
        (λ inner →
          applyRadialReduced rootOperator
            (su2Adjoint (gauge root) (Y root))
            (su2Adjoint transformedPrefix inner))
        (sym
          (applyRadialReducedGaugeCovariant
            junctionOperator
            (gauge (junction sample))
            (Y (junction sample))
            originalSegment)))
      (trans
        (cong
          (λ transport →
            applyRadialReduced rootOperator
              (su2Adjoint (gauge root) (Y root))
              (su2Adjoint transport
                (su2Adjoint (gauge (junction sample))
                  junctionValue)))
          (pathTransportGaugeCovariant
            su2QuaternionGroup gauge U (prefix sample)))
        (trans
          (cong
            (applyRadialReduced rootOperator
              (su2Adjoint (gauge root) (Y root)))
            (conjugatedTransportAction
              su2QuaternionGroup su2AdjointLinearModule
              (gauge root)
              originalPrefix
              (gauge (junction sample))
              junctionValue))
          (sym
            (applyRadialReducedGaugeCovariant
              rootOperator
              (gauge root)
              (Y root)
              transportedValue)))))
  where
    originalSegment : SU2LieAlgebra
    originalSegment =
      covariantPathIntegral
        su2QuaternionGroup su2AdjointLinearModule
        U A (segment sample)

    junctionValue : SU2LieAlgebra
    junctionValue =
      applyRadialReduced junctionOperator
        (Y (junction sample)) originalSegment

    originalPrefix :
      DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier.SU2Quaternion
    originalPrefix =
      directedPathTransport
        su2QuaternionGroup U (prefix sample)

    transformedPrefix :
      DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier.SU2Quaternion
    transformedPrefix =
      directedPathTransport su2QuaternionGroup
        (gaugeTransformBond su2QuaternionGroup gauge U)
        (prefix sample)

    transportedValue : SU2LieAlgebra
    transportedValue = su2Adjoint originalPrefix junctionValue

nestedRadialDifferenceTerm :
  ∀ {N : Nat} {{_ : NonZero N}} →
  RadialReducedOperator →
  RadialReducedOperator →
  SU2LieField4 N →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule →
  {root : Cube4 N} →
  RootedSegmentSample root →
  SU2LieAlgebra
nestedRadialDifferenceTerm rootOperator junctionOperator Y U A sample =
  lieSubtract
    (nestedRadialSegmentTerm
      rootOperator junctionOperator Y U A sample)
    (transportedSegmentIntegral
      su2QuaternionGroup su2AdjointLinearModule U A sample)

nestedRadialDifferenceGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (rootOperator junctionOperator : RadialReducedOperator) →
  (gauge : GaugeFunction4 N su2QuaternionGroup) →
  (Y : SU2LieField4 N) →
  (U : DirectedGaugeField4 N su2QuaternionGroup) →
  (A : DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule) →
  {root : Cube4 N} →
  (sample : RootedSegmentSample root) →
  nestedRadialDifferenceTerm rootOperator junctionOperator
    (transformSU2LieField gauge Y)
    (gaugeTransformBond su2QuaternionGroup gauge U)
    (transformAdjointBondField
      su2QuaternionGroup su2AdjointLinearModule gauge A)
    sample
  ≡
  su2Adjoint (gauge root)
    (nestedRadialDifferenceTerm
      rootOperator junctionOperator Y U A sample)
nestedRadialDifferenceGaugeCovariant
  rootOperator junctionOperator gauge Y U A sample =
  trans
    (cong
      (λ first → lieSubtract first
        (transportedSegmentIntegral su2QuaternionGroup
          su2AdjointLinearModule
          (gaugeTransformBond su2QuaternionGroup gauge U)
          (transformAdjointBondField
            su2QuaternionGroup su2AdjointLinearModule gauge A)
          sample))
      (nestedRadialSegmentGaugeCovariant
        rootOperator junctionOperator gauge Y U A sample))
    (trans
      (cong
        (lieSubtract
          (su2Adjoint (gauge (root sample))
            (nestedRadialSegmentTerm
              rootOperator junctionOperator Y U A sample)))
        (transportedSegmentIntegralGaugeCovariant
          su2QuaternionGroup su2AdjointLinearModule
          gauge U A sample))
      (sym
        (su2AdjointSubtract
          (gauge (root sample))
          (nestedRadialSegmentTerm
            rootOperator junctionOperator Y U A sample)
          (transportedSegmentIntegral
            su2QuaternionGroup su2AdjointLinearModule U A sample))))

nestedRadialDifferenceSum :
  ∀ {N : Nat} {{_ : NonZero N}} →
  RadialReducedOperator →
  RadialReducedOperator →
  SU2LieField4 N →
  DirectedGaugeField4 N su2QuaternionGroup →
  DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule →
  {root : Cube4 N} →
  List (RootedSegmentSample root) →
  SU2LieAlgebra
nestedRadialDifferenceSum rootOperator junctionOperator Y U A [] = lieZero
nestedRadialDifferenceSum rootOperator junctionOperator Y U A
  (sample ∷ samples) =
  lieAdd
    (nestedRadialDifferenceTerm
      rootOperator junctionOperator Y U A sample)
    (nestedRadialDifferenceSum
      rootOperator junctionOperator Y U A samples)

nestedRadialDifferenceSumGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}} →
  (rootOperator junctionOperator : RadialReducedOperator) →
  (gauge : GaugeFunction4 N su2QuaternionGroup) →
  (Y : SU2LieField4 N) →
  (U : DirectedGaugeField4 N su2QuaternionGroup) →
  (A : DirectedAdjointBondField4 N
    su2QuaternionGroup su2AdjointLinearModule) →
  {root : Cube4 N} →
  (samples : List (RootedSegmentSample root)) →
  nestedRadialDifferenceSum rootOperator junctionOperator
    (transformSU2LieField gauge Y)
    (gaugeTransformBond su2QuaternionGroup gauge U)
    (transformAdjointBondField
      su2QuaternionGroup su2AdjointLinearModule gauge A)
    samples
  ≡
  su2Adjoint (gauge root)
    (nestedRadialDifferenceSum
      rootOperator junctionOperator Y U A samples)
nestedRadialDifferenceSumGaugeCovariant
  rootOperator junctionOperator gauge Y U A {root = root} [] =
  DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.su2AdjointZero
    (gauge root)
nestedRadialDifferenceSumGaugeCovariant
  rootOperator junctionOperator gauge Y U A {root = root}
  (sample ∷ samples) =
  trans
    (cong
      (λ tail →
        lieAdd
          (nestedRadialDifferenceTerm rootOperator junctionOperator
            (transformSU2LieField gauge Y)
            (gaugeTransformBond su2QuaternionGroup gauge U)
            (transformAdjointBondField
              su2QuaternionGroup su2AdjointLinearModule gauge A)
            sample)
          tail)
      (nestedRadialDifferenceSumGaugeCovariant
        rootOperator junctionOperator gauge Y U A samples))
    (trans
      (cong
        (λ head →
          lieAdd head
            (su2Adjoint (gauge root)
              (nestedRadialDifferenceSum
                rootOperator junctionOperator Y U A samples)))
        (nestedRadialDifferenceGaugeCovariant
          rootOperator junctionOperator gauge Y U A sample))
      (sym
        (su2AdjointAdd
          (gauge root)
          (nestedRadialDifferenceTerm
            rootOperator junctionOperator Y U A sample)
          (nestedRadialDifferenceSum
            rootOperator junctionOperator Y U A samples))))
