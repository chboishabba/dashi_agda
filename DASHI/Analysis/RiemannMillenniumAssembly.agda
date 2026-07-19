module DASHI.Analysis.RiemannMillenniumAssembly where

-- Final compositional theorem for the DASHI/Weil route.
--
-- The theorems below are executable proof composition.  They do not supply
-- the open mathematical inputs: the analytic substrate, exact explicit
-- formula, termwise DASHI identification, dense extension, or Weil criterion.

open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.RiemannFormulaAnalyticCompatibility
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.DashiWeilExactIdentification
open import DASHI.Analysis.DashiWeilTermwiseBridge
open import DASHI.Analysis.WeilPositivityCore
open import DASHI.Analysis.WeilDensityClosure
open import DASHI.Analysis.RiemannArithmeticCoercivity

record WeilRiemannCriterion
  (analytic : AnalyticSubstrate)
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    positivityImpliesRH :
      ((f : Test) → admissible f → nonnegative (spectralZeroForm f)) →
      RiemannHypothesisFor analytic

    rhImpliesPositivity :
      RiemannHypothesisFor analytic →
      (f : Test) → admissible f → nonnegative (spectralZeroForm f)

exactAsLike :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  DashiWeilQuadratic space formula →
  DashiWeilQuadraticLike space formula
exactAsLike space formula bridge = record
  { DashiTest = DashiWeilQuadratic.DashiTest bridge
  ; embed = DashiWeilQuadratic.embed bridge
  }

record DashiRiemannAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    dashi : DashiWeilQuadratic space formula
    completion :
      DensePositivityExtension space formula
        (exactAsLike space formula dashi)
    criterion : WeilRiemannCriterion analytic space formula

-- Every arrow in this theorem is explicit:
-- DASHI coercivity -> embedded spectral positivity -> dense extension -> RH.
dashiAssemblyImpliesRH :
  (assembly : DashiRiemannAssembly) →
  RiemannHypothesisFor (DashiRiemannAssembly.analytic assembly)
dashiAssemblyImpliesRH assembly =
  let space = DashiRiemannAssembly.space assembly
      formula = DashiRiemannAssembly.formula assembly
      dashi = DashiRiemannAssembly.dashi assembly
      completion = DashiRiemannAssembly.completion assembly
      criterion = DashiRiemannAssembly.criterion assembly
      embeddedPositive =
        embeddedSpectralPositive space formula dashi
      universalPositive =
        DensePositivityExtension.extendPositive completion embeddedPositive
  in
  WeilRiemannCriterion.positivityImpliesRH criterion universalPositive

record SequentialDashiRiemannAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    dashi : DashiWeilQuadratic space formula
    density :
      SequentialDashiDensity space formula
        (exactAsLike space formula dashi)
    criterion : WeilRiemannCriterion analytic space formula

sequentialDashiAssemblyImpliesRH :
  (assembly : SequentialDashiRiemannAssembly) →
  RiemannHypothesisFor
    (SequentialDashiRiemannAssembly.analytic assembly)
sequentialDashiAssemblyImpliesRH assembly =
  let space = SequentialDashiRiemannAssembly.space assembly
      formula = SequentialDashiRiemannAssembly.formula assembly
      dashi = SequentialDashiRiemannAssembly.dashi assembly
      density = SequentialDashiRiemannAssembly.density assembly
      completion =
        sequentialDensityToExtension space formula
          (exactAsLike space formula dashi) density
      assembled : DashiRiemannAssembly
      assembled = record
        { analytic = SequentialDashiRiemannAssembly.analytic assembly
        ; space = space
        ; formula = formula
        ; compatibility =
            SequentialDashiRiemannAssembly.compatibility assembly
        ; dashi = dashi
        ; completion = completion
        ; criterion = SequentialDashiRiemannAssembly.criterion assembly
        }
  in
  dashiAssemblyImpliesRH assembled

record TermwiseSequentialDashiRiemannAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    termwise : DashiWeilTermwiseBridge space formula
    density :
      SequentialDashiDensity space formula
        (exactAsLike space formula
          (termwiseToExactIdentification space formula termwise))
    criterion : WeilRiemannCriterion analytic space formula

termwiseSequentialAssemblyImpliesRH :
  (assembly : TermwiseSequentialDashiRiemannAssembly) →
  RiemannHypothesisFor
    (TermwiseSequentialDashiRiemannAssembly.analytic assembly)
termwiseSequentialAssemblyImpliesRH assembly =
  let space = TermwiseSequentialDashiRiemannAssembly.space assembly
      formula = TermwiseSequentialDashiRiemannAssembly.formula assembly
      termwise = TermwiseSequentialDashiRiemannAssembly.termwise assembly
      exact = termwiseToExactIdentification space formula termwise
      density = TermwiseSequentialDashiRiemannAssembly.density assembly
      sequential : SequentialDashiRiemannAssembly
      sequential = record
        { analytic =
            TermwiseSequentialDashiRiemannAssembly.analytic assembly
        ; space = space
        ; formula = formula
        ; compatibility =
            TermwiseSequentialDashiRiemannAssembly.compatibility assembly
        ; dashi = exact
        ; density = density
        ; criterion =
            TermwiseSequentialDashiRiemannAssembly.criterion assembly
        }
  in
  sequentialDashiAssemblyImpliesRH sequential

record PositiveDecompositionAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    decomposition : WeilPositiveDecomposition space formula
    criterion : WeilRiemannCriterion analytic space formula

-- Alternative terminal route: an exact global positive decomposition bypasses
-- the separate density step because it already covers every admissible test.
positiveDecompositionImpliesRH :
  (assembly : PositiveDecompositionAssembly) →
  RiemannHypothesisFor
    (PositiveDecompositionAssembly.analytic assembly)
positiveDecompositionImpliesRH assembly =
  let space = PositiveDecompositionAssembly.space assembly
      formula = PositiveDecompositionAssembly.formula assembly
      decomposition = PositiveDecompositionAssembly.decomposition assembly
      criterion = PositiveDecompositionAssembly.criterion assembly
      universalPositive =
        decompositionImpliesWeilPositivity space formula decomposition
  in
  WeilRiemannCriterion.positivityImpliesRH criterion universalPositive

record ArithmeticCoercivityAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    compatibility :
      RiemannFormulaAnalyticCompatibility analytic space formula
    arithmeticCoercivity :
      ArithmeticPositiveDecomposition space formula
    criterion : WeilRiemannCriterion analytic space formula

-- This is the most direct prize-facing route currently exposed by the repo:
-- an exact nonnegative decomposition of the arithmetic explicit-formula side
-- is transferred to the spectral side, then Weil positivity yields RH for the
-- same completed-zeta substrate.
arithmeticCoercivityImpliesRH :
  (assembly : ArithmeticCoercivityAssembly) →
  RiemannHypothesisFor
    (ArithmeticCoercivityAssembly.analytic assembly)
arithmeticCoercivityImpliesRH assembly =
  let space = ArithmeticCoercivityAssembly.space assembly
      formula = ArithmeticCoercivityAssembly.formula assembly
      arithmetic =
        ArithmeticCoercivityAssembly.arithmeticCoercivity assembly
      criterion = ArithmeticCoercivityAssembly.criterion assembly
      universalPositive =
        arithmeticCoercivityImpliesWeilPositivity
          space formula arithmetic
  in
  WeilRiemannCriterion.positivityImpliesRH criterion universalPositive
