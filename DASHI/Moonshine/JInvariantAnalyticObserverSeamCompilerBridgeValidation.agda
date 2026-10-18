module DASHI.Moonshine.JInvariantAnalyticObserverSeamCompilerBridgeValidation where

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Moonshine.JInvariantAnalyticStructuredSeamCompilerBidiExact as Seam
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Moonshine.JInvariantAnalyticObserverSeamCompilerBridgeExact as P

observerSeamRegression :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    {View : Set}
    (scaleOf : Modular.FinePoint system → View)
    (recognizer : Scale.SeamScaleRecognizer View)
    (point : Modular.FinePoint system) →
  Seam.CompiledAnalyticSeam
    (P.observerSeamProducers observer scaleOf recognizer)
    point
observerSeamRegression =
  P.compileObserverSeam
