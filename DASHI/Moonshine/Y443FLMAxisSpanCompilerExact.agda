module DASHI.Moonshine.Y443FLMAxisSpanCompilerExact where

-- The short-vector / triality source construction supplies the basis
-- expansions. This compiler pays the logical weld, without assuming that
-- coordinate tags, modular checks, or an external action inhabit V_2.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLM
import DASHI.Moonshine.Y443FLMWeightTwoBasisUVExact as Basis
import DASHI.Moonshine.Y443FLMGriessGeneratorUVExact as Gen

module Selected (V : VOA.VertexOperatorAlgebra) where
  module A = FLM.Selected V
  module B = Basis.Selected V
  module G = Gen.Selected V

  module WithAxes
    (griess : A.ConcreteGriessProduct)
    (Axis : Set)
    (axis : Axis → A.WeightTwo)
    where

    module L = B.WithGriess griess
    module E = G.WithGenerators griess Axis axis

    module Compile
      (span : L.ActualWeightTwoSpan)
      (axisExpansion : Fin 196884 → E.Expression)
      (basisReopens : (i : Fin 196884) →
         E.evaluate (axisExpansion i) ≡ L.basisState span i)
      where

      compile : L.LinearTerm → E.Expression
      compile (L.basis i) = axisExpansion i
      compile (L.sumTerm x y) = E.sum (compile x) (compile y)
      compile (L.scaleTerm s x) = E.scale s (compile x)

      compileReopens : (t : L.LinearTerm) →
        E.evaluate (compile t) ≡ L.evaluate span t
      compileReopens (L.basis i) =
        Gen.trans (basisReopens i) (Gen.sym (L.evaluateBasis span i))
      compileReopens (L.sumTerm x y) =
        Gen.trans
          (Gen.cong₂ (A.weightTwoAdd griess)
            (compileReopens x) (compileReopens y))
          (Gen.sym (L.evaluateSum span x y))
      compileReopens (L.scaleTerm s x) =
        Gen.trans
          (Gen.cong (A.weightTwoScale griess s) (compileReopens x))
          (Gen.sym (L.evaluateScale span s x))

      actualGeneration : E.ActualGeneration
      actualGeneration = record
        { expressionFor = λ x → compile (L.expressionFor span x)
        ; expressionEvaluates = λ x →
            Gen.trans (compileReopens (L.expressionFor span x))
              (L.expressionEvaluates span x)
        }

      axisAgreementImpliesWholeWeightTwo :
        (left right : A.SelectedVOAAutomorphism) →
        ((a : Axis) → A.weightTwoAction left (axis a)
                    ≡ A.weightTwoAction right (axis a)) →
        (x : A.WeightTwo) →
        A.weightTwoAction left x ≡ A.weightTwoAction right x
      axisAgreementImpliesWholeWeightTwo =
        E.generatorAgreementIsWholeWeightTwo actualGeneration
