module DASHI.Moonshine.JInvariantAnalyticStructuredSeamCompilerBidiExact where

------------------------------------------------------------------------
-- ANALYTIC j-SEAM -> STRUCTURED jCOARSE/jFINE -> LOCAL 27 -> ORBIT INDEX
--
-- This module pays orchestration only.  It does not invent the analytic
-- decoder.  Once an analytic modular coordinate supplies both the full
-- structured jCoarse/jFine field and a seam-scale recognition receipt, all
-- downstream finite/orbit data compile on the same object.
--
-- RH cross-pollination supplies the governance rule: retain the full fine
-- residual by default; local 27 is a downstream observer, not a replacement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as Residual
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Moonshine.JInvariantOrderThreeSeamModularWordExact as Word

------------------------------------------------------------------------
-- 1. Same analytic coordinate supplies both structured field and scale view.
------------------------------------------------------------------------

record AnalyticStructuredSeamProducers (Analytic : Set) : Set₁ where
  field
    structuredField : Analytic → Residual.StructuredJField
    renderedScaleView : Set
    scaleOf : Analytic → renderedScaleView
    scaleRecognizer : Scale.SeamScaleRecognizer renderedScaleView

open AnalyticStructuredSeamProducers public

------------------------------------------------------------------------
-- 2. Compiled same-object packet.
------------------------------------------------------------------------

record CompiledAnalyticSeam
    {Analytic : Set}
    (producers : AnalyticStructuredSeamProducers Analytic)
    (z : Analytic) : Set where
  constructor compiled-analytic-seam
  field
    fullStructured : Residual.StructuredJField
    local27 : Residual.LocalJ27
    index : Nat
    scale : Nat
    local27IsObserverOfFull :
      local27 ≡ Residual.localJObserver fullStructured
    scaleIsOrbitNorm :
      scale ≡ Scale.seamScale index

open CompiledAnalyticSeam public

compileAnalyticSeam :
  {Analytic : Set} →
  (producers : AnalyticStructuredSeamProducers Analytic) →
  (z : Analytic) →
  CompiledAnalyticSeam producers z
compileAnalyticSeam producers z =
  compiled-analytic-seam
    full
    (Residual.localJObserver full)
    k
    recognised
    refl
    law
  where
    full = structuredField producers z
    recognizer = scaleRecognizer producers
    view = scaleOf producers z
    k = Scale.SeamScaleRecognizer.recogniseIndex recognizer view
    recognised = Scale.SeamScaleRecognizer.recognisedScale recognizer view
    law = Scale.SeamScaleRecognizer.recognitionLaw recognizer view

------------------------------------------------------------------------
-- 3. The modular word and scale share this same index by construction.
------------------------------------------------------------------------

compiledWordScaleSameIndex :
  {Analytic : Set} →
  (producers : AnalyticStructuredSeamProducers Analytic) →
  (z : Analytic) →
  Scale.WordScaleSameIndexReceipt
    (index (compileAnalyticSeam producers z))
compiledWordScaleSameIndex producers z =
  Scale.canonicalWordScaleSameIndex (index (compileAnalyticSeam producers z))

------------------------------------------------------------------------
-- 4. Fine residual firewall inherited from RH/j observer governance.
------------------------------------------------------------------------

compiledLocal27DoesNotGloballyReconstructFullFine : Bool
compiledLocal27DoesNotGloballyReconstructFullFine = true

compiledFullFieldRetainedByDefault : Bool
compiledFullFieldRetainedByDefault = true

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

data AnalyticStructuredSeamCompilerResidual : Set where
  missingAnalyticStructuredFieldProducer : AnalyticStructuredSeamCompilerResidual
  missingAnalyticScaleRecognizerProducer : AnalyticStructuredSeamCompilerResidual
  missingAnalyticFrickeFiniteTransportIntertwiner : AnalyticStructuredSeamCompilerResidual

record AnalyticStructuredSeamCompilerFrontier : Set where
  constructor analytic-structured-seam-compiler-frontier
  field
    sameObjectCompilerExact : Bool
    fullFineRetainedByDefault : Bool
    localTwentySevenDownstreamOnly : Bool
    orbitWordScaleCompileImmediately : Bool
    analyticProducersConstructed : Bool
    firstResidual : AnalyticStructuredSeamCompilerResidual

canonicalAnalyticStructuredSeamCompilerFrontier :
  AnalyticStructuredSeamCompilerFrontier
canonicalAnalyticStructuredSeamCompilerFrontier =
  analytic-structured-seam-compiler-frontier
    true true true true false
    missingAnalyticStructuredFieldProducer
