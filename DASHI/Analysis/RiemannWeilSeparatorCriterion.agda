module DASHI.Analysis.RiemannWeilSeparatorCriterion where

-- Constructive shape of the converse Weil criterion.
--
-- An off-critical nontrivial zero must generate an admissible test whose
-- spectral Weil form is not nonnegative.  Universal positivity therefore
-- excludes every off-line zero.  The only classical ingredient exposed here
-- is stability of the critical-line predicate under double negation.

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula

Neg : Set → Set
Neg proposition = proposition → ⊥

record WeilOffLineSeparator
  (analytic : AnalyticSubstrate)
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    criticalLineStable :
      (s : ComplexAnalyticCarrier.Complex
        (AnalyticSubstrate.carrier analytic)) →
      Neg
        (Neg
          (CompletedRiemannZeta.criticalLine
            (AnalyticSubstrate.completed analytic) s)) →
      CompletedRiemannZeta.criticalLine
        (AnalyticSubstrate.completed analytic) s

    separateOffLineZero :
      (s : ComplexAnalyticCarrier.Complex
        (AnalyticSubstrate.carrier analytic)) →
      CompletedRiemannZeta.nontrivialZero
        (AnalyticSubstrate.completed analytic) s →
      Neg
        (CompletedRiemannZeta.criticalLine
          (AnalyticSubstrate.completed analytic) s) →
      Σ Test
        (λ f →
          admissible f
          ×
          Neg (nonnegative (spectralZeroForm f)))

universalWeilPositivityImpliesRH :
  (analytic : AnalyticSubstrate) →
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  WeilOffLineSeparator analytic space formula →
  ((f : WeilTestSpace.Test space) →
    WeilTestSpace.admissible space f →
    WeilTestSpace.nonnegative space
      (RiemannExplicitFormula.spectralZeroForm formula f)) →
  RiemannHypothesisFor analytic
universalWeilPositivityImpliesRH analytic space formula criterion universalPositive s nontrivial =
  WeilOffLineSeparator.criticalLineStable criterion s
    (λ notOnLine →
      let witness =
            WeilOffLineSeparator.separateOffLineZero criterion
              s nontrivial notOnLine
          f = proj₁ witness
          payload = proj₂ witness
          admissibleF = proj₁ payload
          spectralNotNonnegative = proj₂ payload
      in
      spectralNotNonnegative (universalPositive f admissibleF))
