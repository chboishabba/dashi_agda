module DASHI.Empirical.DarkDimensionToyDiscriminatorExact where

-- DASHI contribution: a populated, expressly hypothetical, two-axis
-- falsification experiment. These are NOT observations or numerical
-- predictions of a published Dark Dimension model.  Existing source
-- attribution and empirical-promotion gates remain authoritative.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionProspectiveDiscriminatorExact as D
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as S

data ToyHypothesis : Set where
  ordinaryFourDimensional : ToyHypothesis
  toyCompactExtraDimension : ToyHypothesis

-- Explicit candidate signatures, not fitted data.
predictToy : ToyHypothesis → D.ProspectiveObservationState
predictToy ordinaryFourDimensional =
  D.prospectiveObservationState
    D.fullShapeUnobserved D.micronScaleDeviationDisfavoured
predictToy toyCompactExtraDimension =
  D.prospectiveObservationState
    D.fullShapeUnobserved D.micronScaleDeviationSupported

toyCosmologyCollision :
  D.cosmologyState (predictToy ordinaryFourDimensional)
  ≡ D.cosmologyState (predictToy toyCompactExtraDimension)
toyCosmologyCollision = refl

toyGravitySeparation :
  D.gravityState (predictToy ordinaryFourDimensional)
  ≡ D.gravityState (predictToy toyCompactExtraDimension) → ⊥
toyGravitySeparation ()

-- Concrete joint observations permit a hypothesis-by-hypothesis
-- consistency test, without pretending that the observations occurred.
consistentWith :
  ToyHypothesis → D.ProspectiveObservationState → Set
consistentWith h observed =
  D.gravityState (predictToy h) ≡ D.gravityState observed

hypotheticalGravitySupportExcludesOrdinaryToy :
  (observed : D.ProspectiveObservationState) →
  D.gravityState observed ≡ D.micronScaleDeviationSupported →
  consistentWith ordinaryFourDimensional observed → ⊥
hypotheticalGravitySupportExcludesOrdinaryToy
  (D.prospectiveObservationState c D.micronScaleDeviationSupported)
  refl ()
  
-- No projection from this synthetic discriminator to string identity.
canonicalStringPromotionStillBlocked :
  S.stringTheoryPromotionPermitted
    S.canonicalDarkDimensionPromotionStatus ≡ false
canonicalStringPromotionStillBlocked = refl

-- The prospective observational packet is still open.
preregistrationStillOpen :
  D.prospectivePacketLocked D.canonicalProspectiveDiscriminatorPacket
    ≡ false
preregistrationStillOpen = refl
