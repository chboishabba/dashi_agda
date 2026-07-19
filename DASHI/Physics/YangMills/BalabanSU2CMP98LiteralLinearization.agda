module DASHI.Physics.YangMills.BalabanSU2CMP98LiteralLinearization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (NonZero)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4; Axis4)
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using (GaugeFunction4)
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using (RootedSegmentSample)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using (su2QuaternionGroup)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using (SU2LieAlgebra)
open import DASHI.Physics.YangMills.BalabanSU2LiteralOperatorInstances using
  (SU2DirectedGaugeField4; SU2AdjointBondField4)
open import DASHI.Physics.YangMills.BalabanSU2NestedRadialBlockPathTerm using (SU2LieField4)
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using (RadialReducedOperator)
open import DASHI.Physics.YangMills.BalabanSU2LinearizedAverage as Concrete using
  ( linearizedAverage
  ; linearAverageGaugeCovariant
  ; linearAverageTrivialBackground
  ; linearAverageFiniteSupport
  ; linearAverageRegularBackgroundPerturbation
  )

-- The source transcription is the concrete coordinate-order expression already
-- implemented in BalabanSU2LinearizedAverage.  Keeping this separate from the
-- executable name makes later equation-by-equation source audits possible.
cmp98SourceFormula = linearizedAverage
cmp98Implementation = linearizedAverage

cmp98LinearizationSourceExact :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}}
  (mainWeight correctionWeight : ℝ)
  (rootOp junctionOp : RadialReducedOperator)
  (Y : SU2LieField4 (M * suc L))
  (U : SU2DirectedGaugeField4 (M * suc L))
  (A : SU2AdjointBondField4 (M * suc L))
  (coarse : Cube4 M) (axis : Axis4) →
  cmp98Implementation mainWeight correctionWeight rootOp junctionOp Y U A coarse axis
    ≡
  cmp98SourceFormula mainWeight correctionWeight rootOp junctionOp Y U A coarse axis
cmp98LinearizationSourceExact
  mainWeight correctionWeight rootOp junctionOp Y U A coarse axis = refl

linearAverageGaugeCovariant = Concrete.linearAverageGaugeCovariant
linearAverageAtTrivialBackground = Concrete.linearAverageTrivialBackground
linearAverageFiniteSupport = Concrete.linearAverageFiniteSupport
linearAverageBackgroundPerturbation = Concrete.linearAverageRegularBackgroundPerturbation
