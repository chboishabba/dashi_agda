module DASHI.Analysis.RiemannG2ClayTerminalLocatedR3StarValidation where

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2ClayTerminalLocatedR3StarExact as LocatedClay

locatedR3StarTerminalCompilesLiteralRH :
  ∀ {analytic} →
  LocatedClay.ClayTerminalLocatedR3StarInput analytic →
  Analytic.RiemannHypothesisFor analytic
locatedR3StarTerminalCompilesLiteralRH =
  LocatedClay.compileClayTerminalLocatedR3StarToRH
