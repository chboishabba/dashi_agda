module DASHI.Analysis.BombieriWeilTestBridge where

-- Bridge from a logarithmic compact-smooth generator algebra to the abstract
-- Weil convolution-square carrier used by the terminal RH theorem.

open import Agda.Builtin.Equality using (refl)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.WeilConvolutionSquare

record LogarithmicWeilTestBridge (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    Generator : Set
    CompactSmooth : Generator → Set

    reverseConjugate : Generator → Generator
    convolution : Generator → Generator → Generator
    liftToWeilTest : Generator → Test

    generatorCompactSmooth :
      (g : Generator) →
      CompactSmooth g

    reversePreservesCompactSmooth :
      (g : Generator) →
      CompactSmooth g →
      CompactSmooth (reverseConjugate g)

    convolutionPreservesCompactSmooth :
      (g h : Generator) →
      CompactSmooth g →
      CompactSmooth h →
      CompactSmooth (convolution g h)

    liftedSquareAdmissible :
      (g : Generator) →
      admissible
        (liftToWeilTest
          (convolution g (reverseConjugate g)))

logarithmicBridgeToWeilConvolutionAlgebra :
  (space : WeilTestSpace) →
  LogarithmicWeilTestBridge space →
  WeilConvolutionAlgebra space
logarithmicBridgeToWeilConvolutionAlgebra space bridge = record
  { Generator = LogarithmicWeilTestBridge.Generator bridge
  ; reverseConjugate =
      LogarithmicWeilTestBridge.reverseConjugate bridge
  ; convolution =
      λ g h →
        LogarithmicWeilTestBridge.liftToWeilTest bridge
          (LogarithmicWeilTestBridge.convolution bridge g h)
  ; convolutionSquare =
      λ g →
        LogarithmicWeilTestBridge.liftToWeilTest bridge
          (LogarithmicWeilTestBridge.convolution bridge g
            (LogarithmicWeilTestBridge.reverseConjugate bridge g))
  ; squareDefinition = λ g → refl
  ; squareAdmissible =
      LogarithmicWeilTestBridge.liftedSquareAdmissible bridge
  }
