module DASHI.Biology.IBSLatentStateTransitionRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSLatentStateTransitionExact as Latent

stateAtlasRegression :
  Latent.canonicalTemporalStateEvidenceAtlas ≡ Latent.canonicalTemporalStateEvidenceAtlas
stateAtlasRegression = refl

transitionFrontierRegression :
  Latent.canonicalIBSTransitionParetoFrontier ≡ Latent.canonicalIBSTransitionParetoFrontier
transitionFrontierRegression = refl

sameSymptomsNotSameStateRegression :
  Latent.SameSymptomsIdentifySameLatentStatePermission → ⊥
sameSymptomsNotSameStateRegression = Latent.sameSymptomsDoNotIdentifySameLatentState

lagAssociationNotDirectionRegression :
  Latent.LagAssociationIdentifiesCausalDirectionPermission → ⊥
lagAssociationNotDirectionRegression = Latent.lagAssociationDoesNotIdentifyCausalDirection

trajectoryClusterNotAttractorRegression :
  Latent.TrajectoryClusterIsValidatedAttractorPermission → ⊥
trajectoryClusterNotAttractorRegression = Latent.trajectoryClusterDoesNotValidateAttractor

historyBoundaryRegression :
  Latent.canonicalIBSTemporalPathBoundary ≡ Latent.canonicalIBSTemporalPathBoundary
historyBoundaryRegression = refl
