module DASHI.Analysis.RiemannG2ClayTerminalBishopLocatedValidation where

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2ClayTerminalBishopLocatedExact as BishopClay

bishopLocatedTerminalCompilesLiteralRH :
  ∀ {analytic} →
  BishopClay.ClayTerminalBishopLocatedInput analytic →
  Analytic.RiemannHypothesisFor analytic
bishopLocatedTerminalCompilesLiteralRH =
  BishopClay.compileClayTerminalBishopLocatedToRH
