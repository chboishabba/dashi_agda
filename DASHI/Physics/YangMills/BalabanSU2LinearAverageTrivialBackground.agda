module DASHI.Physics.YangMills.BalabanSU2LinearAverageTrivialBackground where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import Data.Nat.Base using (NonZero)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  (DirectedGaugeField4; GaugeFunction4; gaugeTransformBond)
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  (DirectedAdjointBondField4; transformAdjointBondField)
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  (RootedSegmentSample; linearBlockPathAverage; linearBlockPathAverageGaugeCovariant)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (su2QuaternionGroup; su2Identity)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2AdjointLinearModule)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2ScalarAdjointLinearModule)

SU2DirectedGaugeField4 : Nat → Set
SU2DirectedGaugeField4 N = DirectedGaugeField4 N su2QuaternionGroup

SU2AdjointBondField4 : Nat → Set
SU2AdjointBondField4 N =
  DirectedAdjointBondField4 N su2QuaternionGroup su2AdjointLinearModule

trivialSU2Background : ∀ {N : Nat} → SU2DirectedGaugeField4 N
trivialSU2Background _ = su2Identity

Q0 :
  ∀ {N : Nat} {{_ : NonZero N}}
  (weight : ℝ) (A : SU2AdjointBondField4 N)
  {root : Cube4 N} → List (RootedSegmentSample root) → SU2LieAlgebra
Q0 weight A samples =
  linearBlockPathAverage
    su2QuaternionGroup su2ScalarAdjointLinearModule weight
    trivialSU2Background A samples

-- The finite support of Q0 is definitionally the supplied finite sample list.
record Q0FiniteSupport {N : Nat} {{_ : NonZero N}}
  {root : Cube4 N} (samples : List (RootedSegmentSample root)) : Set where
  constructor q0FiniteSupport
  field
    support : List (RootedSegmentSample root)
    supportExact : support ≡ samples

q0FiniteSupportWitness :
  ∀ {N : Nat} {{_ : NonZero N}} {root : Cube4 N}
  (samples : List (RootedSegmentSample root)) → Q0FiniteSupport samples
q0FiniteSupportWitness samples = q0FiniteSupport samples refl

Q0GaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (weight : ℝ)
  (gauge : GaugeFunction4 N su2QuaternionGroup)
  (A : SU2AdjointBondField4 N)
  {root : Cube4 N}
  (samples : List (RootedSegmentSample root)) →
  linearBlockPathAverage
    su2QuaternionGroup su2ScalarAdjointLinearModule weight
    (gaugeTransformBond su2QuaternionGroup gauge trivialSU2Background)
    (transformAdjointBondField
      su2QuaternionGroup su2AdjointLinearModule gauge A)
    samples
  ≡
  DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.su2Adjoint
    (gauge root) (Q0 weight A samples)
Q0GaugeCovariant weight gauge A samples =
  linearBlockPathAverageGaugeCovariant
    su2QuaternionGroup su2ScalarAdjointLinearModule
    weight gauge trivialSU2Background A samples
