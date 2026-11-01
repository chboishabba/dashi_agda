{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTBalancedLocalizedAntigravityMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.Foundations.GRQFTFiniteComovingRiemannDeviationExact as Riemann
import DASHI.Physics.Foundations.GRQFTFiniteDefocusingSolutionWitnessExact as Defocus
import DASHI.Physics.Foundations.GRQFTFiniteAnisotropicTOVBalanceExact as TOV
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local

------------------------------------------------------------------------
-- BALANCED LOCALIZED ANTIGRAVITY MAX-CUT
--
-- This supersedes the first algebraic shell candidate by carrying the corrected
-- anisotropic transition that satisfies the normalized finite TOV balance.
------------------------------------------------------------------------

record BalancedLocalizedPositiveGAntigravityMaxCut : Set where
  constructor balanced-localized-positive-g-antigravity-max-cut
  field
    finiteDefocusing :
      Defocus.FiniteDefocusingSolutionWitness

    comovingDeviation :
      Riemann.FiniteComovingRiemannDeviationWitness

    anisotropicBalance :
      TOV.FiniteAnisotropicTOVBalanceWitness

    coupling : Signed.CouplingSign
    couplingPositive :
      coupling ≡ Signed.positiveCoupling

    externalResponse :
      Local.ExteriorRadialResponse
    externalResponseOutward :
      externalResponse ≡ Local.outwardExteriorAcceleration

    allPrincipalDeviationOutward :
      (i : Riemann.SpatialAxis3) →
      Riemann.principalDeviationAcceleration i
        ≡ Riemann.outwardSeparationAcceleration

open BalancedLocalizedPositiveGAntigravityMaxCut public

canonicalBalancedLocalizedPositiveGAntigravityMaxCut :
  BalancedLocalizedPositiveGAntigravityMaxCut
canonicalBalancedLocalizedPositiveGAntigravityMaxCut =
  balanced-localized-positive-g-antigravity-max-cut
    Defocus.canonicalFiniteDefocusingSolutionWitness
    Riemann.canonicalFiniteComovingRiemannDeviationWitness
    TOV.canonicalFiniteAnisotropicTOVBalanceWitness
    Signed.positiveCoupling
    refl
    Local.outwardExteriorAcceleration
    refl
    Riemann.allPrincipalComovingDeviationDirectionsOutward

balancedLocalizedPositiveGExternalRepulsion :
  externalResponse canonicalBalancedLocalizedPositiveGAntigravityMaxCut
    ≡ Local.outwardExteriorAcceleration
balancedLocalizedPositiveGExternalRepulsion = refl

balancedLocalizedPositiveG :
  coupling canonicalBalancedLocalizedPositiveGAntigravityMaxCut
    ≡ Signed.positiveCoupling
balancedLocalizedPositiveG = refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record BalancedLocalizedAntigravityBoundary : Set where
  constructor balanced-localized-antigravity-boundary
  field
    positiveGCouplingRetained : Bool
    normalizedAnisotropicHydrostaticBalanceRetained : Bool
    pressureFreeOuterRadialBoundaryRetained : Bool
    netNegativeIntegratedActiveMassRetained : Bool
    outwardExternalResponseRetained : Bool
    outwardPrincipalTidalDeviationRetained : Bool
    negativeGRequired : Bool
    negativeInertialMassRequired : Bool
    fullContinuumTOVSolved : Bool
    junctionConditionsSolved : Bool
    exactLocalizedMetricSolved : Bool

canonicalBalancedLocalizedAntigravityBoundary :
  BalancedLocalizedAntigravityBoundary
canonicalBalancedLocalizedAntigravityBoundary =
  balanced-localized-antigravity-boundary
    true true true true true true false false false false false
