module DASHI.Physics.YangMills.BalabanSU2CMP98LiteralLinearization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (NonZero)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4; Axis4)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using (SU2LieAlgebra)
open import DASHI.Physics.YangMills.BalabanSU2LiteralOperatorInstances using
  (SU2DirectedGaugeField4; SU2AdjointBondField4)
open import DASHI.Physics.YangMills.BalabanSU2NestedRadialBlockPathTerm using (SU2LieField4)
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using (RadialReducedOperator)
open import DASHI.Physics.YangMills.BalabanSU2LinearizedAverage public
  using (linearizedAverage; linearAverageGaugeCovariant; linearAverageFiniteSupport)
  renaming
    ( linearAverageTrivialBackground to linearAverageAtTrivialBackground
    ; linearAverageRegularBackgroundPerturbation to linearAverageBackgroundPerturbation
    )

-- This name denotes the current executable coordinate-order formula only.  The
-- independent five-term source transcription and its audit theorem live in
-- BalabanSU2CMP98Equation124; no definitional self-equality is advertised as a
-- source audit.
cmp98ImplementationFormula :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}} →
  ℝ → ℝ → RadialReducedOperator → RadialReducedOperator →
  SU2LieField4 (M * suc L) → SU2DirectedGaugeField4 (M * suc L) →
  SU2AdjointBondField4 (M * suc L) → Cube4 M → Axis4 → SU2LieAlgebra
cmp98ImplementationFormula = linearizedAverage

cmp98ImplementationDefinitionExact :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}}
  (mainWeight correctionWeight : ℝ)
  (rootOp junctionOp : RadialReducedOperator)
  (Y : SU2LieField4 (M * suc L))
  (U : SU2DirectedGaugeField4 (M * suc L))
  (A : SU2AdjointBondField4 (M * suc L))
  (coarse : Cube4 M) (axis : Axis4) →
  cmp98ImplementationFormula
    mainWeight correctionWeight rootOp junctionOp Y U A coarse axis
    ≡
  linearizedAverage
    mainWeight correctionWeight rootOp junctionOp Y U A coarse axis
cmp98ImplementationDefinitionExact
  mainWeight correctionWeight rootOp junctionOp Y U A coarse axis = refl
