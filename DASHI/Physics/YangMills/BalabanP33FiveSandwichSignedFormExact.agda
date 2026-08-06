module DASHI.Physics.YangMills.BalabanP33FiveSandwichSignedFormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The existing operator pipeline proves absolute unit-form estimates for the
-- five factorized Hessian channels.  Coercivity needs signed inequalities.
-- This module specializes the bound carrier to the rationals and proves
--
--   -epsilon_i <= <v,E_i v> <= epsilon_i
--
-- for curvature, transport, chart, gauge and constraint.  Exact epsilon
-- identities then expose the configured 32/64/32/64/64 radius budgets without
-- treating either sign as an additional physical input.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline
import DASHI.Physics.YangMills.BalabanClayGate4SandwichOperatorToFormBoundExact as Sandwich
import DASHI.Physics.YangMills.BalabanClayGate4FiveSandwichChannelAssemblyExact as Assembly
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact as Primitive
import DASHI.Physics.YangMills.BalabanP33PrimitiveAbsoluteOperatorAdapterExact as Absolute

sandwichFormValue :
  ∀ {Operator State}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator ℚ}
    {formAlgebra : Sandwich.OperatorNormFormAlgebra
      Operator State ℚ operatorAlgebra} →
  Sandwich.SandwichChannelNormBudget formAlgebra →
  State → ℚ
sandwichFormValue {formAlgebra = formAlgebra} budget state =
  Sandwich.inner formAlgebra state
    (Sandwich.apply formAlgebra (Sandwich.channel budget) state)

sandwichFormAbsoluteBound :
  ∀ {Operator State}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator ℚ}
    {formAlgebra : Sandwich.OperatorNormFormAlgebra
      Operator State ℚ operatorAlgebra}
    (budget : Sandwich.SandwichChannelNormBudget formAlgebra)
    state →
  Pipeline.LessEqual operatorAlgebra ≡ _≤_ →
  (∀ value → Sandwich.absolute formAlgebra value ≡ ∣ value ∣) →
  Sandwich.UnitState formAlgebra state →
  ∣ sandwichFormValue budget state ∣ ≤ Sandwich.epsilon budget
sandwichFormAbsoluteBound
    {operatorAlgebra = operatorAlgebra}
    {formAlgebra = formAlgebra}
    budget state orderMeaning absoluteMeaning unit =
  subst
    (λ lower → lower ≤ Sandwich.epsilon budget)
    (absoluteMeaning (sandwichFormValue budget state))
    (subst
      (λ relation → relation
        (Sandwich.absolute formAlgebra
          (sandwichFormValue budget state))
        (Sandwich.epsilon budget))
      orderMeaning
      (Sandwich.sandwichChannelUnitFormBound budget state unit))

sandwichFormTwoSided :
  ∀ {Operator State}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator ℚ}
    {formAlgebra : Sandwich.OperatorNormFormAlgebra
      Operator State ℚ operatorAlgebra}
    (budget : Sandwich.SandwichChannelNormBudget formAlgebra)
    state →
  Pipeline.LessEqual operatorAlgebra ≡ _≤_ →
  (∀ value → Sandwich.absolute formAlgebra value ≡ ∣ value ∣) →
  Sandwich.UnitState formAlgebra state →
  Primitive.TwoSided
    (sandwichFormValue budget state)
    (Sandwich.epsilon budget)
sandwichFormTwoSided budget state orderMeaning absoluteMeaning unit =
  Absolute.operatorNormDominatesCoordinate
    (sandwichFormValue budget state)
    (Sandwich.epsilon budget)
    (sandwichFormAbsoluteBound
      budget state orderMeaning absoluteMeaning unit)

configuredSandwichFormTwoSided :
  ∀ {Operator State}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator ℚ}
    {formAlgebra : Sandwich.OperatorNormFormAlgebra
      Operator State ℚ operatorAlgebra}
    (budget : Sandwich.SandwichChannelNormBudget formAlgebra)
    state configuredBudget →
  Pipeline.LessEqual operatorAlgebra ≡ _≤_ →
  (∀ value → Sandwich.absolute formAlgebra value ≡ ∣ value ∣) →
  Sandwich.UnitState formAlgebra state →
  Sandwich.epsilon budget ≡ configuredBudget →
  Primitive.TwoSided
    (sandwichFormValue budget state)
    configuredBudget
configuredSandwichFormTwoSided
    budget state configuredBudget orderMeaning absoluteMeaning unit exact =
  subst
    (Primitive.TwoSided (sandwichFormValue budget state))
    exact
    (sandwichFormTwoSided
      budget state orderMeaning absoluteMeaning unit)

curvatureSignedFormBound :
  ∀ {Operator State}
    (assembly : Assembly.FiveSandwichChannelAssembly Operator State ℚ)
    state radius →
  Pipeline.LessEqual (Assembly.operatorAlgebra assembly) ≡ _≤_ →
  (∀ value →
    Sandwich.absolute (Assembly.formAlgebra assembly) value ≡ ∣ value ∣) →
  Sandwich.UnitState (Assembly.formAlgebra assembly) state →
  Sandwich.epsilon (Assembly.curvatureBudget assembly)
    ≡ Constants.configuredCurvatureCoefficient * radius →
  Primitive.TwoSided
    (sandwichFormValue (Assembly.curvatureBudget assembly) state)
    (Constants.configuredCurvatureCoefficient * radius)
curvatureSignedFormBound assembly state radius =
  configuredSandwichFormTwoSided
    (Assembly.curvatureBudget assembly) state
    (Constants.configuredCurvatureCoefficient * radius)

transportSignedFormBound :
  ∀ {Operator State}
    (assembly : Assembly.FiveSandwichChannelAssembly Operator State ℚ)
    state radius →
  Pipeline.LessEqual (Assembly.operatorAlgebra assembly) ≡ _≤_ →
  (∀ value →
    Sandwich.absolute (Assembly.formAlgebra assembly) value ≡ ∣ value ∣) →
  Sandwich.UnitState (Assembly.formAlgebra assembly) state →
  Sandwich.epsilon (Assembly.transportBudget assembly)
    ≡ Constants.configuredTransportCoefficient * radius →
  Primitive.TwoSided
    (sandwichFormValue (Assembly.transportBudget assembly) state)
    (Constants.configuredTransportCoefficient * radius)
transportSignedFormBound assembly state radius =
  configuredSandwichFormTwoSided
    (Assembly.transportBudget assembly) state
    (Constants.configuredTransportCoefficient * radius)

chartSignedFormBound :
  ∀ {Operator State}
    (assembly : Assembly.FiveSandwichChannelAssembly Operator State ℚ)
    state radius →
  Pipeline.LessEqual (Assembly.operatorAlgebra assembly) ≡ _≤_ →
  (∀ value →
    Sandwich.absolute (Assembly.formAlgebra assembly) value ≡ ∣ value ∣) →
  Sandwich.UnitState (Assembly.formAlgebra assembly) state →
  Sandwich.epsilon (Assembly.chartBudget assembly)
    ≡ Constants.configuredChartCoefficient * radius →
  Primitive.TwoSided
    (sandwichFormValue (Assembly.chartBudget assembly) state)
    (Constants.configuredChartCoefficient * radius)
chartSignedFormBound assembly state radius =
  configuredSandwichFormTwoSided
    (Assembly.chartBudget assembly) state
    (Constants.configuredChartCoefficient * radius)

gaugeSignedFormBound :
  ∀ {Operator State}
    (assembly : Assembly.FiveSandwichChannelAssembly Operator State ℚ)
    state radius →
  Pipeline.LessEqual (Assembly.operatorAlgebra assembly) ≡ _≤_ →
  (∀ value →
    Sandwich.absolute (Assembly.formAlgebra assembly) value ≡ ∣ value ∣) →
  Sandwich.UnitState (Assembly.formAlgebra assembly) state →
  Sandwich.epsilon (Assembly.gaugeBudget assembly)
    ≡ Constants.configuredGaugeCoefficient * radius →
  Primitive.TwoSided
    (sandwichFormValue (Assembly.gaugeBudget assembly) state)
    (Constants.configuredGaugeCoefficient * radius)
gaugeSignedFormBound assembly state radius =
  configuredSandwichFormTwoSided
    (Assembly.gaugeBudget assembly) state
    (Constants.configuredGaugeCoefficient * radius)

constraintSignedFormBound :
  ∀ {Operator State}
    (assembly : Assembly.FiveSandwichChannelAssembly Operator State ℚ)
    state radius →
  Pipeline.LessEqual (Assembly.operatorAlgebra assembly) ≡ _≤_ →
  (∀ value →
    Sandwich.absolute (Assembly.formAlgebra assembly) value ≡ ∣ value ∣) →
  Sandwich.UnitState (Assembly.formAlgebra assembly) state →
  Sandwich.epsilon (Assembly.constraintBudget assembly)
    ≡ Constants.configuredConstraintCoefficient * radius →
  Primitive.TwoSided
    (sandwichFormValue (Assembly.constraintBudget assembly) state)
    (Constants.configuredConstraintCoefficient * radius)
constraintSignedFormBound assembly state radius =
  configuredSandwichFormTwoSided
    (Assembly.constraintBudget assembly) state
    (Constants.configuredConstraintCoefficient * radius)

sandwichAbsoluteToSignedFormLevel : ProofLevel
sandwichAbsoluteToSignedFormLevel = machineChecked

fiveSandwichConfiguredSignedBoundsLevel : ProofLevel
fiveSandwichConfiguredSignedBoundsLevel = machineChecked
