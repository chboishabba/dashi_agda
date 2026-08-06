module DASHI.Physics.Closure.NSTriadKNLuoFourInteractionSeparatingProbeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations aux
-- derivees partielles non lineaires",
-- Annales scientifiques de l'Ecole Normale Superieure 14 (1981), 209--246.
-- DOI: 10.24033/asens.1404.
--
-- Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin,
-- "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Make HH, LH, HL and comparable-shell values a separating audit family.
-- Equality of totals is deliberately not enough: equality on all four probes
-- determines the complete finite interaction vector.  Physical classwise
-- estimates remain separate producers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Common.SeparatingProbeFamilyExact as Common

data InteractionProbe : Set where
  highHighProbe : InteractionProbe
  lowHighProbe : InteractionProbe
  highLowProbe : InteractionProbe
  comparableProbe : InteractionProbe

record InteractionVector : Set where
  constructor interactionVector
  field
    highHighValue : ℚ
    lowHighValue : ℚ
    highLowValue : ℚ
    comparableValue : ℚ

open InteractionVector public

observeInteraction : InteractionProbe → InteractionVector → ℚ
observeInteraction highHighProbe vector = highHighValue vector
observeInteraction lowHighProbe vector = lowHighValue vector
observeInteraction highLowProbe vector = highLowValue vector
observeInteraction comparableProbe vector = comparableValue vector

interactionProbesSeparate :
  ∀ left right →
  ((probe : InteractionProbe) →
    observeInteraction probe left ≡ observeInteraction probe right) →
  left ≡ right
interactionProbesSeparate
  (interactionVector leftHH leftLH leftHL leftCC)
  (interactionVector rightHH rightLH rightHL rightCC)
  agreement
  rewrite agreement highHighProbe
        | agreement lowHighProbe
        | agreement highLowProbe
        | agreement comparableProbe = refl

fourInteractionProbeSystem :
  Common.SeparatingProbeSystem InteractionVector ℚ
fourInteractionProbeSystem =
  Common.separatingProbeSystem
    InteractionProbe
    observeInteraction
    interactionProbesSeparate

record FourInteractionProbeBoundary : Set where
  constructor fourInteractionProbeBoundary
  field
    matchingInteractionSumDeterminesVector : Set
    matchingInteractionSumDoesNotDetermineVector :
      matchingInteractionSumDeterminesVector → Set

    separatingVectorSuppliesClasswiseBounds : Set
    separatingVectorDoesNotSupplyClasswiseBounds :
      separatingVectorSuppliesClasswiseBounds → Set

canonicalFourInteractionProbeBoundary : FourInteractionProbeBoundary
canonicalFourInteractionProbeBoundary =
  fourInteractionProbeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
