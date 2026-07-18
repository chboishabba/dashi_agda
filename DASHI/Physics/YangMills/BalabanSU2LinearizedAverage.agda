module DASHI.Physics.YangMills.BalabanSU2LinearizedAverage where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4; Axis4)
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  (GaugeFunction4; gaugeTransformBond)
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  (transformAdjointBondField)
open import DASHI.Physics.YangMills.BalabanCanonicalBlockPathSamples using
  (canonicalBlockSamples)
open import DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm using
  (blockOrigin)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_; zeroR; realSolverRing; su2QuaternionGroup)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; su2LieExt; lieZero; lieAdd; lieSubtract; lieScale;
   lieZeroLeft; su2Adjoint; su2AdjointAdd; su2AdjointScale;
   su2AdjointLinearModule)
open import DASHI.Physics.YangMills.BalabanSU2LiteralOperatorInstances using
  (SU2DirectedGaugeField4; SU2AdjointBondField4;
   su2BlockedLinearAverageMainTerm; su2BlockedLinearAverageGaugeCovariant)
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using
  (RadialReducedOperator; applyRadialReduced)
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointComposition using
  (identityRadialReduced)
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  (applyIdentityReducedAdjoint)
open import DASHI.Physics.YangMills.BalabanSU2NestedRadialBlockPathTerm using
  (SU2LieField4; transformSU2LieField;
   nestedRadialSegmentTerm; nestedRadialDifferenceTerm;
   nestedRadialDifferenceSum; nestedRadialDifferenceSumGaugeCovariant)

linearizedAverageCorrection :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  ℝ → RadialReducedOperator → RadialReducedOperator →
  SU2LieField4 (M * suc L) →
  SU2DirectedGaugeField4 (M * suc L) →
  SU2AdjointBondField4 (M * suc L) →
  Cube4 M → Axis4 → SU2LieAlgebra
linearizedAverageCorrection
  {L = L} correctionWeight rootOperator junctionOperator Y U A coarse axis =
  lieScale correctionWeight
    (nestedRadialDifferenceSum rootOperator junctionOperator Y U A
      (canonicalBlockSamples (suc L) axis (blockOrigin coarse)))

linearizedAverage :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  ℝ → ℝ → RadialReducedOperator → RadialReducedOperator →
  SU2LieField4 (M * suc L) →
  SU2DirectedGaugeField4 (M * suc L) →
  SU2AdjointBondField4 (M * suc L) →
  Cube4 M → Axis4 → SU2LieAlgebra
linearizedAverage mainWeight correctionWeight rootOperator junctionOperator Y U A coarse axis =
  lieAdd
    (su2BlockedLinearAverageMainTerm mainWeight U A coarse axis)
    (linearizedAverageCorrection correctionWeight rootOperator junctionOperator Y U A coarse axis)

linearAverageGaugeCovariant :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  (mainWeight correctionWeight : ℝ) →
  (rootOperator junctionOperator : RadialReducedOperator) →
  (gauge : GaugeFunction4 (M * suc L) su2QuaternionGroup) →
  (Y : SU2LieField4 (M * suc L)) →
  (U : SU2DirectedGaugeField4 (M * suc L)) →
  (A : SU2AdjointBondField4 (M * suc L)) →
  (coarse : Cube4 M) → (axis : Axis4) →
  linearizedAverage mainWeight correctionWeight rootOperator junctionOperator
    (transformSU2LieField gauge Y)
    (gaugeTransformBond su2QuaternionGroup gauge U)
    (transformAdjointBondField su2QuaternionGroup su2AdjointLinearModule gauge A)
    coarse axis
  ≡ su2Adjoint (gauge (blockOrigin coarse))
      (linearizedAverage mainWeight correctionWeight rootOperator junctionOperator
        Y U A coarse axis)
linearAverageGaugeCovariant
  {L = L} mainWeight correctionWeight rootOperator junctionOperator
  gauge Y U A coarse axis =
  trans
    (cong
      (λ correction → lieAdd
        (su2BlockedLinearAverageMainTerm mainWeight
          (gaugeTransformBond su2QuaternionGroup gauge U)
          (transformAdjointBondField su2QuaternionGroup su2AdjointLinearModule gauge A)
          coarse axis)
        (lieScale correctionWeight correction))
      (nestedRadialDifferenceSumGaugeCovariant
        rootOperator junctionOperator gauge Y U A
        (canonicalBlockSamples (suc L) axis (blockOrigin coarse))))
    (trans
      (cong
        (λ main → lieAdd main
          (lieScale correctionWeight
            (su2Adjoint (gauge (blockOrigin coarse))
              (nestedRadialDifferenceSum rootOperator junctionOperator Y U A
                (canonicalBlockSamples (suc L) axis (blockOrigin coarse))))))
        (su2BlockedLinearAverageGaugeCovariant mainWeight gauge U A coarse axis))
      (trans
        (cong
          (lieAdd
            (su2Adjoint (gauge (blockOrigin coarse))
              (su2BlockedLinearAverageMainTerm mainWeight U A coarse axis)))
          (sym (su2AdjointScale (gauge (blockOrigin coarse)) correctionWeight
            (nestedRadialDifferenceSum rootOperator junctionOperator Y U A
              (canonicalBlockSamples (suc L) axis (blockOrigin coarse))))))
        (sym (su2AdjointAdd (gauge (blockOrigin coarse))
          (su2BlockedLinearAverageMainTerm mainWeight U A coarse axis)
          (linearizedAverageCorrection correctionWeight rootOperator junctionOperator
            Y U A coarse axis)))))

lieSubtractSelf : ∀ X → lieSubtract X X ≡ lieZero
lieSubtractSelf (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ []) realSolverRing)
    (Solver.solve (y ∷ []) realSolverRing)
    (Solver.solve (z ∷ []) realSolverRing)

nestedIdentitySegment :
  ∀ {N : Nat} {{_ : NonZero N}}
  (Y : SU2LieField4 N) (U : SU2DirectedGaugeField4 N)
  (A : SU2AdjointBondField4 N) {root : Cube4 N}
  (sample : DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.RootedSegmentSample root) →
  nestedRadialSegmentTerm identityRadialReduced identityRadialReduced Y U A sample
  ≡ DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.transportedSegmentIntegral
      su2QuaternionGroup su2AdjointLinearModule U A sample
nestedIdentitySegment Y U A sample =
  trans
    (applyIdentityReducedAdjoint _ _)
    (cong
      (su2Adjoint
        (DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance.directedPathTransport
          su2QuaternionGroup U
          (DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.prefix sample)))
      (applyIdentityReducedAdjoint _ _))

nestedIdentityDifference :
  ∀ {N : Nat} {{_ : NonZero N}}
  (Y : SU2LieField4 N) (U : SU2DirectedGaugeField4 N)
  (A : SU2AdjointBondField4 N) {root : Cube4 N}
  (sample : DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.RootedSegmentSample root) →
  nestedRadialDifferenceTerm identityRadialReduced identityRadialReduced Y U A sample
    ≡ lieZero
nestedIdentityDifference Y U A sample =
  trans
    (cong
      (λ value → lieSubtract value
        (DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.transportedSegmentIntegral
          su2QuaternionGroup su2AdjointLinearModule U A sample))
      (nestedIdentitySegment Y U A sample))
    (lieSubtractSelf _)

nestedIdentityDifferenceSum :
  ∀ {N : Nat} {{_ : NonZero N}}
  (Y : SU2LieField4 N) (U : SU2DirectedGaugeField4 N)
  (A : SU2AdjointBondField4 N) {root : Cube4 N}
  (samples : List (DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.RootedSegmentSample root)) →
  nestedRadialDifferenceSum identityRadialReduced identityRadialReduced Y U A samples
    ≡ lieZero
nestedIdentityDifferenceSum Y U A [] = refl
nestedIdentityDifferenceSum Y U A (sample ∷ samples) =
  trans
    (cong
      (λ head → lieAdd head
        (nestedRadialDifferenceSum identityRadialReduced identityRadialReduced Y U A samples))
      (nestedIdentityDifference Y U A sample))
    (trans
      (lieZeroLeft _)
      (nestedIdentityDifferenceSum Y U A samples))

linearAverageTrivialBackground :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  (mainWeight correctionWeight : ℝ) →
  (Y : SU2LieField4 (M * suc L)) →
  (U : SU2DirectedGaugeField4 (M * suc L)) →
  (A : SU2AdjointBondField4 (M * suc L)) →
  (coarse : Cube4 M) → (axis : Axis4) →
  linearizedAverage mainWeight correctionWeight
    identityRadialReduced identityRadialReduced Y U A coarse axis
  ≡ su2BlockedLinearAverageMainTerm mainWeight U A coarse axis
linearAverageTrivialBackground {L = L}
  mainWeight correctionWeight Y U A coarse axis =
  trans
    (cong
      (lieAdd (su2BlockedLinearAverageMainTerm mainWeight U A coarse axis))
      (trans
        (cong (lieScale correctionWeight)
          (nestedIdentityDifferenceSum Y U A
            (canonicalBlockSamples (suc L) axis (blockOrigin coarse))))
        (DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieScaleZero lieZero)))
    (DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieZeroRight _)

linearAverageFiniteSupport :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}}
  (coarse : Cube4 M) (axis : Axis4) →
  List (DASHI.Physics.YangMills.BalabanLinearBlockPathAverage.RootedSegmentSample
    (blockOrigin coarse))
linearAverageFiniteSupport {L = L} coarse axis =
  canonicalBlockSamples (suc L) axis (blockOrigin coarse)

linearAverageRegularBackgroundPerturbation :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  (mainWeight correctionWeight : ℝ) →
  (rootOperator junctionOperator : RadialReducedOperator) →
  (Y : SU2LieField4 (M * suc L)) →
  (U : SU2DirectedGaugeField4 (M * suc L)) →
  (A : SU2AdjointBondField4 (M * suc L)) →
  (coarse : Cube4 M) → (axis : Axis4) →
  linearizedAverage mainWeight correctionWeight rootOperator junctionOperator
    Y U A coarse axis
  ≡ lieAdd
      (su2BlockedLinearAverageMainTerm mainWeight U A coarse axis)
      (linearizedAverageCorrection correctionWeight rootOperator junctionOperator
        Y U A coarse axis)
linearAverageRegularBackgroundPerturbation
  mainWeight correctionWeight rootOperator junctionOperator Y U A coarse axis = refl
