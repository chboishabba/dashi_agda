module DASHI.Moonshine.JInvariantFormulaic369RendererExact where

------------------------------------------------------------------------
-- FORMULAIC KLEIN-J / 369 RENDERER
--
-- Goal: reproduce the j phase image from formulae, not from a painted image.
--
-- Same-object pipeline:
--
--   z
--   -> J(z) = g2(z)^3 / Delta(z)
--   -> (Re J(z), Im J(z))
--   -> atan2(Im J(z), Re J(z))
--   -> exact continuous phase payload
--   -> C3 / C6 / C9 / C27 Base369 observers
--   -> colour/tone sample
--
-- Agda owns the semantic pipeline and the finite observers.  A numerical
-- producer may evaluate g2/Delta/atan2 on a raster grid, but it may not replace
-- the exact phase payload by a finite colour label.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

open import Base369 using
  ( HexTruth
  ; tri-low ; tri-mid ; tri-high
  )

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariantRainbowFullTurnHyperformExact as Rainbow
import DASHI.Moonshine.JInvariantImageFractalSourceAtlasExact as Sources

------------------------------------------------------------------------
-- 1. Analytic rendering algebra.
--
-- Value is the same Value used by the Klein-j algebra.  Scalar/Phase/Tone and
-- Colour are intentionally abstract so the owner can be instantiated by an
-- exact complex library, a constructive real library, or a governed numerical
-- producer without changing the renderer semantics.
------------------------------------------------------------------------

record JPhaseRenderingAlgebra : Set₁ where
  constructor j-phase-rendering-algebra
  field
    klein : Klein.KleinJAlgebra

    Scalar : Set
    Phase : Set
    Tone : Set
    Colour : Set

    realPart : Klein.Value klein → Scalar
    imagPart : Klein.Value klein → Scalar
    atan2 : Scalar → Scalar → Phase
    toneOfValue : Klein.Value klein → Tone

    phaseColour : Phase → Colour
    composeTone : Tone → Colour → Colour

    phase3 : Phase → Triadic.KernelTrit
    phase6 : Phase → HexTruth
    phase9 : Phase → Triadic.NineSheet
    phase27 : Phase → Fabric.Ternary27Point

open JPhaseRenderingAlgebra public

------------------------------------------------------------------------
-- 2. Formulaic same-object evaluation.
------------------------------------------------------------------------

jValue :
  (R : JPhaseRenderingAlgebra) →
  Klein.Point (klein R) →
  Klein.Value (klein R)
jValue R z = Klein.KleinJ (klein R) z

jPhase :
  (R : JPhaseRenderingAlgebra) →
  Klein.Point (klein R) →
  Phase R
jPhase R z =
  atan2 R
    (imagPart R (jValue R z))
    (realPart R (jValue R z))

jTone :
  (R : JPhaseRenderingAlgebra) →
  Klein.Point (klein R) →
  Tone R
jTone R z = toneOfValue R (jValue R z)

jColour :
  (R : JPhaseRenderingAlgebra) →
  Klein.Point (klein R) →
  Colour R
jColour R z =
  composeTone R (jTone R z) (phaseColour R (jPhase R z))

------------------------------------------------------------------------
-- 3. Rich render sample: finite 369 observations stay over the continuous
--    phase payload rather than replacing it.
------------------------------------------------------------------------

record J369RenderSample (R : JPhaseRenderingAlgebra) : Set where
  constructor j369-render-sample
  field
    point : Klein.Point (klein R)
    exactValue : Klein.Value (klein R)
    exactPhase : Phase R
    exactTone : Tone R
    renderedColour : Colour R
    observer3 : Triadic.KernelTrit
    observer6 : HexTruth
    observer9 : Triadic.NineSheet
    observer27 : Fabric.Ternary27Point

open J369RenderSample public

renderAt :
  (R : JPhaseRenderingAlgebra) →
  Klein.Point (klein R) →
  J369RenderSample R
renderAt R z =
  j369-render-sample
    z
    (jValue R z)
    (jPhase R z)
    (jTone R z)
    (jColour R z)
    (phase3 R (jPhase R z))
    (phase6 R (jPhase R z))
    (phase9 R (jPhase R z))
    (phase27 R (jPhase R z))

renderRetainsExactValue :
  (R : JPhaseRenderingAlgebra) →
  (z : Klein.Point (klein R)) →
  exactValue (renderAt R z) ≡ jValue R z
renderRetainsExactValue R z = refl

renderRetainsExactPhase :
  (R : JPhaseRenderingAlgebra) →
  (z : Klein.Point (klein R)) →
  exactPhase (renderAt R z) ≡ jPhase R z
renderRetainsExactPhase R z = refl

render3IsObserverOnly :
  (R : JPhaseRenderingAlgebra) →
  (z : Klein.Point (klein R)) →
  observer3 (renderAt R z) ≡ phase3 R (jPhase R z)
render3IsObserverOnly R z = refl

render6IsObserverOnly :
  (R : JPhaseRenderingAlgebra) →
  (z : Klein.Point (klein R)) →
  observer6 (renderAt R z) ≡ phase6 R (jPhase R z)
render6IsObserverOnly R z = refl

render9IsObserverOnly :
  (R : JPhaseRenderingAlgebra) →
  (z : Klein.Point (klein R)) →
  observer9 (renderAt R z) ≡ phase9 R (jPhase R z)
render9IsObserverOnly R z = refl

render27IsObserverOnly :
  (R : JPhaseRenderingAlgebra) →
  (z : Klein.Point (klein R)) →
  observer27 (renderAt R z) ≡ phase27 R (jPhase R z)
render27IsObserverOnly R z = refl

------------------------------------------------------------------------
-- 4. Raster producer boundary.
--
-- pointAt is the calibrated pixel -> analytic-point map.  This keeps the
-- rasterizer downstream of the formula.  Reproducing the image means running
-- renderPixel over a finite pixel grid; the pixel producer does not own any j
-- semantics.
------------------------------------------------------------------------

record J369RasterProducer (R : JPhaseRenderingAlgebra) : Set₁ where
  constructor j369-raster-producer
  field
    Pixel : Set
    pointAt : Pixel → Klein.Point (klein R)

open J369RasterProducer public

renderPixel :
  (R : JPhaseRenderingAlgebra) →
  (P : J369RasterProducer R) →
  Pixel P →
  J369RenderSample R
renderPixel R P px = renderAt R (pointAt P px)

pixelColour :
  (R : JPhaseRenderingAlgebra) →
  (P : J369RasterProducer R) →
  Pixel P →
  Colour R
pixelColour R P px = renderedColour (renderPixel R P px)

------------------------------------------------------------------------
-- 5. Full-turn 369 rendering contract.
--
-- The phase observers are required to be interpreted against the already-owned
-- exact 3/6/9/27 full-turn partitions.  This owner does not assert an RGB
-- standard; phaseColour is the final continuous colour-map authority.
------------------------------------------------------------------------

record J369RendererFullTurnReceipt : Set where
  constructor j369-renderer-full-turn-receipt
  field
    partition3 : Rainbow.FullTurnPartition
    partition6 : Rainbow.FullTurnPartition
    partition9 : Rainbow.FullTurnPartition
    partition27 : Rainbow.FullTurnPartition
    threeCoversFullTurn :
      Rainbow.sectorCount partition3 ≡ 3
    sixCoversFullTurn :
      Rainbow.sectorCount partition6 ≡ 6
    nineCoversFullTurn :
      Rainbow.sectorCount partition9 ≡ 9
    twentySevenCoversFullTurn :
      Rainbow.sectorCount partition27 ≡ 27

canonicalJ369RendererFullTurnReceipt : J369RendererFullTurnReceipt
canonicalJ369RendererFullTurnReceipt =
  j369-renderer-full-turn-receipt
    Rainbow.partition3
    Rainbow.partition6
    Rainbow.partition9
    Rainbow.partition27
    refl refl refl refl

------------------------------------------------------------------------
-- 6. Attribution / reproduction frontier.
------------------------------------------------------------------------

phaseSourceStillDoesNotEntitleKernelProof :
  Sources.sourceEntitlesKernelProof Sources.phaseTripleWindingClaim ≡ false
phaseSourceStillDoesNotEntitleKernelProof = refl

complexSourceStillDoesNotEntitleKernelProof :
  Sources.sourceEntitlesKernelProof Sources.complexPlaneCarrierClaim ≡ false
complexSourceStillDoesNotEntitleKernelProof = refl

record FormulaicRendererFrontier : Set where
  constructor formulaic-renderer-frontier
  field
    kleinJFormulaOwned : Bool
    atan2PhasePipelineOwned : Bool
    threeSixNineTwentySevenObserversOwned : Bool
    exactPhaseRetainedInFibre : Bool
    rasterProducerSeparated : Bool
    concreteAnalyticComplexInstantiationPaid : Bool
    concreteNumericalRasterizerPaid : Bool
    reproducedRasterComparedToSource : Bool

canonicalFormulaicRendererFrontier : FormulaicRendererFrontier
canonicalFormulaicRendererFrontier =
  formulaic-renderer-frontier
    true true true true true false false false

------------------------------------------------------------------------
-- Formulaic target now exposed by this owner:
--
--   renderPixel px
--     = colour(
--         tone(J(pointAt px)),
--         atan2(Im J(pointAt px), Re J(pointAt px)))
--
-- with J = g2^3 / Delta and C3/C6/C9/C27 observers attached to the same phase.
------------------------------------------------------------------------
