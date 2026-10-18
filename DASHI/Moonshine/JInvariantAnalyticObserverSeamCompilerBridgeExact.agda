module DASHI.Moonshine.JInvariantAnalyticObserverSeamCompilerBridgeExact where

------------------------------------------------------------------------
-- ANALYTIC STRUCTURED OBSERVER -> EXISTING SEAM / ORBIT COMPILER
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- JInvariantAnalyticJCoarseFineObserverExact now provides the corrected
-- analytic -> finite structured observation boundary.  The older generic
-- AnalyticStructuredSeamCompiler already knows how to retain the full fine
-- field, derive local27, and combine it with an independently supplied scale
-- recognizer.
--
-- This owner composes those two interfaces.  No new scale theorem or analytic
-- acquisition theorem is asserted here.
------------------------------------------------------------------------

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Moonshine.JInvariantAnalyticStructuredSeamCompilerBidiExact as Seam
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale

observerSeamProducers :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    {View : Set}
    (scaleOf : Modular.FinePoint system → View)
    (recognizer : Scale.SeamScaleRecognizer View) →
  Seam.AnalyticStructuredSeamProducers
    (Modular.FinePoint system)
observerSeamProducers observer {View} scaleOf recognizer = record
  { Seam.structuredField =
      Observer.observeStructuredField observer
  ; Seam.renderedScaleView = View
  ; Seam.scaleOf = scaleOf
  ; Seam.scaleRecognizer = recognizer
  }

compileObserverSeam :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    {View : Set}
    (scaleOf : Modular.FinePoint system → View)
    (recognizer : Scale.SeamScaleRecognizer View)
    (point : Modular.FinePoint system) →
  Seam.CompiledAnalyticSeam
    (observerSeamProducers observer scaleOf recognizer)
    point
compileObserverSeam observer scaleOf recognizer point =
  Seam.compileAnalyticSeam
    (observerSeamProducers observer scaleOf recognizer)
    point
