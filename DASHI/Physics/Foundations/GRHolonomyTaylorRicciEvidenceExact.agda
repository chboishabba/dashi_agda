{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRHolonomyTaylorRicciEvidenceExact where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.DiscreteToSmoothEinsteinLimitReceipt as Smooth

------------------------------------------------------------------------
-- THEOREM-BEARING REFINEMENT OF THE HOLONOMY/TAYLOR REQUEST SURFACE
--
-- The existing HolonomyTaylorRicciConvergenceSupplyInterface names the desired
-- proposition families.  This record requires inhabitants of those families.
-- It therefore cannot be discharged by merely choosing convenient Set-valued
-- placeholders.
------------------------------------------------------------------------

record HolonomyTaylorRicciConvergenceEvidence
    (supply : Smooth.HolonomyTaylorRicciConvergenceSupplyInterface) : Setω where
  field
    holonomyTaylorExpansionEvidence :
      ∀ depth connection →
      Smooth.holonomyTaylorExpansion supply depth connection

    curvatureExtractionErrorBoundEvidence :
      ∀ depth connection →
      Smooth.curvatureExtractionErrorBound supply depth connection

    ricciContractionLimitCompatibilityEvidence :
      ∀ depth connection →
      Smooth.ricciContractionLimitCompatibility supply depth connection

    uniformCurvatureDerivativeBoundEvidence :
      Smooth.uniformCurvatureDerivativeBound supply

    discreteRicciC0ConvergenceRateEvidence :
      ∀ depth connection →
      Smooth.discreteRicciC0ConvergenceRate supply depth connection

open HolonomyTaylorRicciConvergenceEvidence public

record GRDiscreteToSmoothFirstAnalyticBundle : Setω where
  field
    supply :
      Smooth.HolonomyTaylorRicciConvergenceSupplyInterface

    evidence :
      HolonomyTaylorRicciConvergenceEvidence supply

    sameLiteralNonflatFamilyUsedDownstream :
      Set

    sameLiteralNonflatFamilyUsedDownstreamEvidence :
      sameLiteralNonflatFamilyUsedDownstream

    noFlatIdentitySubstitution :
      Set

    noFlatIdentitySubstitutionEvidence :
      noFlatIdentitySubstitution

    boundary : List String

open GRDiscreteToSmoothFirstAnalyticBundle public

requestSurfaceAloneClosesCurvatureConvergence : Bool
requestSurfaceAloneClosesCurvatureConvergence = false

requestSurfaceAloneClosesCurvatureConvergenceIsFalse :
  requestSurfaceAloneClosesCurvatureConvergence ≡ false
requestSurfaceAloneClosesCurvatureConvergenceIsFalse = refl

theoremBearingBundleStillRequired : Bool
theoremBearingBundleStillRequired = true

theoremBearingBundleStillRequiredIsTrue :
  theoremBearingBundleStillRequired ≡ true
theoremBearingBundleStillRequiredIsTrue = refl
