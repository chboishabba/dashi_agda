module DASHI.Cognition.PerceptualModeJet where

------------------------------------------------------------------------
-- Jet-style local data for perceptual mode modelling.
--
-- This captures the user's "nth derivative" intuition safely: the minimal
-- Turing operator uses first-order time evolution and a second-order spatial
-- Laplacian, while higher-order local data are model refinements/residuals.

open import DASHI.Biology.TuringPatternRegimeSurface using
  ( DerivativeRole
  ; firstOrderTimeEvolution
  ; secondOrderSpatialLaplacian
  ; higherOrderResidualJet
  )
open import DASHI.Cognition.KlueverFormConstantProjection using (KlueverForm)

record PerceptualModeJet : Set₁ where
  constructor perceptualModeJet
  field
    FieldValue : Set
    SpatialGradient : Set
    SpatialLaplacian : Set
    HigherResidual : Set
    SelectedMode : Set
    ProjectedForm : KlueverForm

    timeEvolutionRole : DerivativeRole
    diffusionRole : DerivativeRole
    residualRole : DerivativeRole

    laplacianIsCoreDiffusionOperator : Set
    higherTermsAreModelResidual : Set
    projectedFormIsLossy : Set

record PerceptualModeJetBoundary : Set₁ where
  constructor perceptualModeJetBoundary
  field
    jet : PerceptualModeJet

    notArbitraryNthDerivativeStack : Set
    notReverseSolvableFromForm : Set
    notSemanticAuthority : Set
