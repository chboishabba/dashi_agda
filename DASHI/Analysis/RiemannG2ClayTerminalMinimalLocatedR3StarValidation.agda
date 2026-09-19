module DASHI.Analysis.RiemannG2ClayTerminalMinimalLocatedR3StarValidation where

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2ClayTerminalMinimalLocatedR3StarExact as Minimal

minimalLocatedR3StarCompilesLiteralRH :
  ∀ {analytic} →
  Minimal.ClayTerminalMinimalLocatedR3StarInput analytic →
  Analytic.RiemannHypothesisFor analytic
minimalLocatedR3StarCompilesLiteralRH =
  Minimal.compileClayTerminalMinimalLocatedR3StarToRH
