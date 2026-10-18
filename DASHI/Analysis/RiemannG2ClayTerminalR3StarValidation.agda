module DASHI.Analysis.RiemannG2ClayTerminalR3StarValidation where

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2ClayTerminalR3StarExact as R3StarClay

r3StarTerminalInputCompilesLiteralRH :
  ∀ {analytic} →
  R3StarClay.ClayTerminalR3StarInput analytic →
  Analytic.RiemannHypothesisFor analytic
r3StarTerminalInputCompilesLiteralRH =
  R3StarClay.compileClayTerminalR3StarToRH
