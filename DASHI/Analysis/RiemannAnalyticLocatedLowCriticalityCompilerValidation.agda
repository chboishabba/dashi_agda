module DASHI.Analysis.RiemannAnalyticLocatedLowCriticalityCompilerValidation where

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannLocatedHeightCarrierExact as Height
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannAnalyticLocatedLowCriticalityCompilerExact as Compile

sourceCriticalityAndCoordinateCoreCompileR3Star :
  ∀ {analytic heightCarrier}
    {attachment :
      Located.AnalyticLocatedHeightCarrierAttachment analytic heightCarrier} →
  Compile.LocatedCriticalCoordinateCore analytic heightCarrier attachment →
  Compile.PublishedLocatedLowCriticality attachment →
  Located.LocatedAnalyticCoordinateRealization analytic
sourceCriticalityAndCoordinateCoreCompileR3Star =
  Compile.compileLocatedAnalyticCoordinateRealization
