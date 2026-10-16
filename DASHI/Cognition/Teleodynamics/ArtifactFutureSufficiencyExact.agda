module DASHI.Cognition.Teleodynamics.ArtifactFutureSufficiencyExact where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.VerifiedArtifactTransitionExact as Artifact

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record ArtifactFutureModel (Body Residual : Set) : Set₁ where
  constructor artifact-future-model
  field
    Consumer : Set
    Observation : Set
    observe : Consumer → Body → Observation
    reconstruct : Body → Residual → Body
open ArtifactFutureModel public

record ResidualFutureSufficiency
    {Identity Body Residual : Set}
    (M : ArtifactFutureModel Body Residual)
    (state : Artifact.ArtifactState Identity Body Residual) : Set₁ where
  constructor residual-future-sufficiency
  field
    reconstructExact : reconstruct M (Artifact.body state) (Artifact.residual state) ≡ Artifact.body state
open ResidualFutureSufficiency public

futureObservationPreserved :
  ∀ {Identity Body Residual : Set}
    {M : ArtifactFutureModel Body Residual}
    {state : Artifact.ArtifactState Identity Body Residual} →
  ResidualFutureSufficiency M state →
  (q : Consumer M) →
  observe M q (reconstruct M (Artifact.body state) (Artifact.residual state)) ≡
  observe M q (Artifact.body state)
futureObservationPreserved {M = M} suff q =
  cong (observe M q) (reconstructExact suff)
