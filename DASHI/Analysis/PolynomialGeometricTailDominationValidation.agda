module DASHI.Analysis.PolynomialGeometricTailDominationValidation where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.PolynomialGeometricTailDominationExact as P

finiteTailDominationRegression :
  ∀ {Scalar : Set}
    (K : P.OrderedTailKernel Scalar)
    (term majorant : Nat → Scalar) →
  (∀ index → P.LessEqual K (term index) (majorant index)) →
  ∀ start count →
  P.LessEqual K
    (P.finiteTail K term start count)
    (P.finiteTail K majorant start count)
finiteTailDominationRegression = P.finiteTailDomination

vanishingTailTransferRegression :
  ∀ {Scalar : Set}
    (K : P.OrderedTailKernel Scalar)
    (term majorant : Nat → Scalar)
    (S : P.TailSmallness K) →
  (∀ index → P.LessEqual K (term index) (majorant index)) →
  P.TailVanishes K S majorant →
  P.TailVanishes K S term
vanishingTailTransferRegression = P.dominatedTailVanishes
