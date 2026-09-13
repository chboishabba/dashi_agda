module DASHI.Moonshine.JInvariantFormulaic369PantsRendererExact where

------------------------------------------------------------------------
-- FORMULAIC J RENDERER WITH PANTS/GLUING ADDRESSES
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

record JPantsRenderSample (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor j-pants-render-sample
  field
    baseSample : Render.J369RenderSample R
    pantsCoarse9 : Frontier.PantsPath 2
    pantsRefinement27 : Frontier.PantsPath 3

open JPantsRenderSample public

renderWithPants :
  (R : Render.JPhaseRenderingAlgebra) →
  Klein.Point (Render.klein R) →
  JPantsRenderSample R
renderWithPants R z =
  let s = Render.renderAt R z
  in j-pants-render-sample
       s
       (Pants369.nineToPants2 (Render.observer9 s))
       (Pants369.voxel27ToPants3 (Render.observer27 s))

pants9RecoversRendererObserver :
  (R : Render.JPhaseRenderingAlgebra) →
  (z : Klein.Point (Render.klein R)) →
  Pants369.pants2ToNine (pantsCoarse9 (renderWithPants R z))
  ≡ Render.observer9 (Render.renderAt R z)
pants9RecoversRendererObserver R z =
  Pants369.ninePantsRoundTrip (Render.observer9 (Render.renderAt R z))

pants27RecoversRendererObserver :
  (R : Render.JPhaseRenderingAlgebra) →
  (z : Klein.Point (Render.klein R)) →
  Pants369.pants3ToVoxel27 (pantsRefinement27 (renderWithPants R z))
  ≡ Render.observer27 (Render.renderAt R z)
pants27RecoversRendererObserver R z =
  Pants369.voxelPantsRoundTrip (Render.observer27 (Render.renderAt R z))

pantsRenderRetainsExactPhase :
  (R : Render.JPhaseRenderingAlgebra) →
  (z : Klein.Point (Render.klein R)) →
  Render.exactPhase (baseSample (renderWithPants R z)) ≡ Render.jPhase R z
pantsRenderRetainsExactPhase R z = refl

pantsRenderRetainsColour :
  (R : Render.JPhaseRenderingAlgebra) →
  (z : Klein.Point (Render.klein R)) →
  Render.renderedColour (baseSample (renderWithPants R z)) ≡ Render.jColour R z
pantsRenderRetainsColour R z = refl

record FormulaicPantsRendererBoundary : Set where
  constructor formulaic-pants-renderer-boundary
  field
    nineObserverHasExactDepthTwoPantsRealisation : Bool
    twentySevenObserverHasExactDepthThreePantsRealisation : Bool
    continuousPhaseRetained : Bool
    pantsAddressReplacesAnalyticPhase : Bool
    neutralPantsSeamAutomaticallyEqualsVisualWaist : Bool
    smoothPantsSurfaceClaimed : Bool

canonicalFormulaicPantsRendererBoundary : FormulaicPantsRendererBoundary
canonicalFormulaicPantsRendererBoundary =
  formulaic-pants-renderer-boundary true true true false false false
