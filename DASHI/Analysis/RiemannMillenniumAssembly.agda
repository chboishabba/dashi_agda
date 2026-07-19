module DASHI.Analysis.RiemannMillenniumAssembly where

-- Final compositional theorem for the DASHI/Weil route.
--
-- The theorem below is executable proof composition.  It does not supply the
-- open mathematical inputs: the analytic substrate, exact explicit formula,
-- dense extension, or Weil criterion.

open import DASHI.Analysis.RiemannZetaProgramBoundary
  using (RiemannHypothesisWitness)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.DashiWeilExactIdentification
open import DASHI.Analysis.WeilPositivityCore

record WeilRiemannCriterion
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    positivityImpliesRH :
      ((f : Test) → admissible f → nonnegative (spectralZeroForm f)) →
      RiemannHypothesisWitness

    rhImpliesPositivity :
      RiemannHypothesisWitness →
      (f : Test) → admissible f → nonnegative (spectralZeroForm f)

    criterionMatchesCompletedZeta : Set

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
    dashi : DashiWeilQuadratic space formula
    completion :
      DensePositivityExtension space formula
        (exactAsLike space formula dashi)
    criterion : WeilRiemannCriterion space formula

-- Every arrow in this theorem is now explicit:
-- DASHI coercivity -> embedded spectral positivity -> dense extension -> RH.
dashiAssemblyImpliesRH :
  DashiRiemannAssembly → RiemannHypothesisWitness
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

record PositiveDecompositionAssembly : Set₁ where
  field
    analytic : AnalyticSubstrate
    space : WeilTestSpace
    formula : RiemannExplicitFormula space
    decomposition : WeilPositiveDecomposition space formula
    criterion : WeilRiemannCriterion space formula

-- Alternative terminal route: an exact global positive decomposition bypasses
-- the separate density step because it already covers every admissible test.
positiveDecompositionImpliesRH :
  PositiveDecompositionAssembly → RiemannHypothesisWitness
positiveDecompositionImpliesRH assembly =
  let space = PositiveDecompositionAssembly.space assembly
      formula = PositiveDecompositionAssembly.formula assembly
      decomposition = PositiveDecompositionAssembly.decomposition assembly
      criterion = PositiveDecompositionAssembly.criterion assembly
      universalPositive =
        decompositionImpliesWeilPositivity space formula decomposition
  in
  WeilRiemannCriterion.positivityImpliesRH criterion universalPositive
