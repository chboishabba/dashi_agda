module DASHI.Analysis.RiemannWeilSquareCriterion where

-- Prize-facing form of Weil positivity: every convolution square g * g∨ has
-- nonnegative explicit-formula value.  An off-line zero must be separable by a
-- generator whose square has negative spectral value.

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilConvolutionSquare

SquareNeg : Set → Set
SquareNeg proposition = proposition → ⊥

record WeilSquareOffLineSeparator
  (analytic : AnalyticSubstrate)
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (algebra : WeilConvolutionAlgebra space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    criticalLineStable :
      (s : ComplexAnalyticCarrier.Complex
        (AnalyticSubstrate.carrier analytic)) →
      SquareNeg
        (SquareNeg
          (CompletedRiemannZeta.criticalLine
            (AnalyticSubstrate.completed analytic) s)) →
      CompletedRiemannZeta.criticalLine
        (AnalyticSubstrate.completed analytic) s

    separateOffLineZero :
      (s : ComplexAnalyticCarrier.Complex
        (AnalyticSubstrate.carrier analytic)) →
      CompletedRiemannZeta.nontrivialZero
        (AnalyticSubstrate.completed analytic) s →
      SquareNeg
        (CompletedRiemannZeta.criticalLine
          (AnalyticSubstrate.completed analytic) s) →
      Σ (WeilConvolutionAlgebra.Generator algebra)
        (λ g →
          SquareNeg
            (nonnegative
              (spectralZeroForm
                (WeilConvolutionAlgebra.convolutionSquare algebra g))))

weilSquarePositivityImpliesRH :
  (analytic : AnalyticSubstrate) →
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  WeilSquareOffLineSeparator analytic space formula algebra →
  ((g : WeilConvolutionAlgebra.Generator algebra) →
    WeilTestSpace.nonnegative space
      (RiemannExplicitFormula.spectralZeroForm formula
        (WeilConvolutionAlgebra.convolutionSquare algebra g))) →
  RiemannHypothesisFor analytic
weilSquarePositivityImpliesRH
  analytic space formula algebra criterion squarePositive s nontrivial =
  WeilSquareOffLineSeparator.criticalLineStable criterion s
    (λ notOnLine →
      let witness =
            WeilSquareOffLineSeparator.separateOffLineZero criterion
              s nontrivial notOnLine
          g = proj₁ witness
          squareNotNonnegative = proj₂ witness
      in
      squareNotNonnegative (squarePositive g))
