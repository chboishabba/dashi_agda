module DASHI.Cognition.PNF.MultimodalPhaseFutureEquivalenceExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OpticalTextCompressionPNFExact as Optical
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- MULTIMODAL REPRESENTATION PHASE VS TASK / DYNAMICAL PHASE
--
-- Text, visual and latent encodings are physical representation modalities.
-- The C3/task-character phase is a separate dynamical coordinate.  Changing
-- modality need not change the consumer-visible future class, and advancing a
-- task phase need not change modality.
------------------------------------------------------------------------

record MultimodalPhaseCoordinate : Set where
  constructor multimodalPhaseCoordinate
  field
    modality : Optical.RepresentationModality
    taskPhase : Wheel.DepthWheelPhase

open MultimodalPhaseCoordinate public

changeModality :
  Optical.RepresentationModality →
  MultimodalPhaseCoordinate →
  MultimodalPhaseCoordinate
changeModality target coordinate =
  multimodalPhaseCoordinate target (taskPhase coordinate)

advanceTaskPhase : MultimodalPhaseCoordinate → MultimodalPhaseCoordinate
advanceTaskPhase coordinate =
  multimodalPhaseCoordinate
    (modality coordinate)
    (Wheel.nextDepthWheelPhase (taskPhase coordinate))

modalityChangeCommutesWithTaskPhaseAdvance :
  (target : Optical.RepresentationModality) →
  (coordinate : MultimodalPhaseCoordinate) →
  changeModality target (advanceTaskPhase coordinate)
  ≡ advanceTaskPhase (changeModality target coordinate)
modalityChangeCommutesWithTaskPhaseAdvance target coordinate = refl

modalityChangePreservesTaskPhase :
  (target : Optical.RepresentationModality) →
  (coordinate : MultimodalPhaseCoordinate) →
  taskPhase (changeModality target coordinate) ≡ taskPhase coordinate
modalityChangePreservesTaskPhase target coordinate = refl

------------------------------------------------------------------------
-- Common-latent cross-modal future equivalence.
------------------------------------------------------------------------

record CrossModalConsumerFactorization
    (Text Visual Latent Query Observation : Set) : Set₁ where
  constructor crossModalConsumerFactorization
  field
    encodeText : Text → Latent
    encodeVisual : Visual → Latent
    observeText : Query → Text → Observation
    observeVisual : Query → Visual → Observation
    observeLatent : Query → Latent → Observation

    textFactors :
      (query : Query) → (text : Text) →
      observeText query text ≡ observeLatent query (encodeText text)

    visualFactors :
      (query : Query) → (visual : Visual) →
      observeVisual query visual ≡ observeLatent query (encodeVisual visual)

open CrossModalConsumerFactorization public

sameLatentImpliesCrossModalConsumerEquivalence :
  ∀ {Text Visual Latent Query Observation}
    (system : CrossModalConsumerFactorization Text Visual Latent Query Observation)
    {text : Text} {visual : Visual} →
  encodeText system text ≡ encodeVisual system visual →
  (query : Query) →
  observeText system query text ≡ observeVisual system query visual
sameLatentImpliesCrossModalConsumerEquivalence system latentEqual query =
  trans
    (textFactors system query _)
    (trans
      (cong (observeLatent system query) latentEqual)
      (sym (visualFactors system query _)))

------------------------------------------------------------------------
-- Consequence: modality/token representation may change while the declared
-- consumer future remains invariant, provided the common latent factorization
-- is proved.  Without that proof, modality compression is only an engineering
-- transform, not semantic equivalence authority.
------------------------------------------------------------------------
