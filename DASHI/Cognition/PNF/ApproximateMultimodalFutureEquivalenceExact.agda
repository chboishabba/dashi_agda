module DASHI.Cognition.PNF.ApproximateMultimodalFutureEquivalenceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- APPROXIMATE CROSS-MODAL FUTURE EQUIVALENCE
--
-- Exact common-latent equality is stronger than production multimodal systems
-- need.  This module gives the quantitative finite theorem: latent proximity
-- plus consumer stability bounds observable distortion for every query trace.
------------------------------------------------------------------------

record NatMetric (Carrier : Set) : Set₁ where
  constructor natMetric
  field
    distance : Carrier → Carrier → Nat

open NatMetric public

record ApproximateCrossModalSystem
    (Text Visual Latent Query Observation : Set) : Set₁ where
  constructor approximateCrossModalSystem
  field
    latentMetric : NatMetric Latent
    observationMetric : NatMetric Observation

    encodeText : Text → Latent
    encodeVisual : Visual → Latent
    observeLatent : List Query → Latent → Observation
    observeText : List Query → Text → Observation
    observeVisual : List Query → Visual → Observation

    textExactThroughLatent :
      (queries : List Query) → (text : Text) →
      observeText queries text ≡ observeLatent queries (encodeText text)

    visualExactThroughLatent :
      (queries : List Query) → (visual : Visual) →
      observeVisual queries visual ≡ observeLatent queries (encodeVisual visual)

    consumerLipschitz : Nat
    consumerStable :
      (queries : List Query) → (left right : Latent) →
      distance observationMetric
        (observeLatent queries left)
        (observeLatent queries right)
      ≤ consumerLipschitz * distance latentMetric left right

open ApproximateCrossModalSystem public

crossModalFutureDistortionBound :
  ∀ {Text Visual Latent Query Observation}
    (system : ApproximateCrossModalSystem Text Visual Latent Query Observation)
    {text : Text} {visual : Visual} {eta : Nat} →
  distance (latentMetric system)
    (encodeText system text) (encodeVisual system visual)
  ≤ eta →
  (queries : List Query) →
  distance (observationMetric system)
    (observeText system queries text)
    (observeVisual system queries visual)
  ≤ consumerLipschitz system * eta
crossModalFutureDistortionBound system latentBound queries
  rewrite textExactThroughLatent system queries _
        | visualExactThroughLatent system queries _ =
  ≤-trans
    (consumerStable system queries _ _)
    (*-monoˡ-≤ (consumerLipschitz system) latentBound)

------------------------------------------------------------------------
-- Rate comparison remains separate from the distortion theorem.
------------------------------------------------------------------------

record CrossModalRateWitness
    {Text Visual : Set}
    (text : Text) (visual : Visual) : Set where
  constructor crossModalRateWitness
  field
    textCost visualCost : Nat
    visualNoMoreExpensive : visualCost ≤ textCost

open CrossModalRateWitness public

record CrossModalRateDistortionCertificate
    {Text Visual Latent Query Observation : Set}
    (system : ApproximateCrossModalSystem Text Visual Latent Query Observation)
    (text : Text) (visual : Visual)
    (eta : Nat) : Set₁ where
  constructor crossModalRateDistortionCertificate
  field
    rate : CrossModalRateWitness text visual
    latentDistortion :
      distance (latentMetric system)
        (encodeText system text) (encodeVisual system visual)
      ≤ eta
    futureBound :
      (queries : List Query) →
      distance (observationMetric system)
        (observeText system queries text)
        (observeVisual system queries visual)
      ≤ consumerLipschitz system * eta

approximateCrossModalCertificate :
  ∀ {Text Visual Latent Query Observation}
    (system : ApproximateCrossModalSystem Text Visual Latent Query Observation)
    {text : Text} {visual : Visual} {eta : Nat} →
  CrossModalRateWitness text visual →
  distance (latentMetric system)
    (encodeText system text) (encodeVisual system visual)
  ≤ eta →
  CrossModalRateDistortionCertificate system text visual eta
approximateCrossModalCertificate system rateWitness latentBound =
  crossModalRateDistortionCertificate
    rateWitness
    latentBound
    (crossModalFutureDistortionBound system latentBound)

------------------------------------------------------------------------
-- This separates OCR/surface compression rate from consumer-future distortion:
-- a cheaper modality is useful only under a proved consumer-stability bound.
------------------------------------------------------------------------
