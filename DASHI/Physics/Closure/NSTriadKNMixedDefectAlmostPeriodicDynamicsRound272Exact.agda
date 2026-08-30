module DASHI.Physics.Closure.NSTriadKNMixedDefectAlmostPeriodicDynamicsRound272Exact where

------------------------------------------------------------------------
-- ROUND272 / DYNAMIC WELD FOR THE MIXED-DEFECT CRITICAL ELEMENT
--
-- R271 selects a minimal mixed-defect profile and records compactness modulo
-- Navier--Stokes symmetries.  The next rigidity arguments require more: the
-- selected object must be the initial datum of one maximal-lifespan nonlinear
-- NS solution whose whole critical orbit is represented by translation/scale
-- parameters.  This is not definitionally contained in static profile
-- compactness and is therefore kept as an explicit analytic theorem.
--
-- BIDI target:
--   selected R271 profile
--     -> SAME nonlinear NS solution u_c
--     -> maximal lifespan I_c
--     -> frequency scale N(t) and centre x(t)
--     -> renormalized orbit precompact in H^(1/2)
--     -> zero excluded from orbit closure (nonzero obstruction)
--     -> mixed-defect badness persists on this SAME solution.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record MixedDefectAlmostPeriodicDynamics {ℓ : Level}
    (CriticalElement : Set ℓ) : Set (lsuc ℓ) where
  field
    element : CriticalElement

    Time : Set ℓ
    State : Set ℓ
    solution : Time → State
    maximalLifespan : Set ℓ
    solvesNavierStokesOnMaximalLifespan : Set ℓ

    frequencyScale : Time → State
    spatialCenter : Time → State
    renormalizedState : Time → State

    renormalizedOrbitPrecompactHOneHalf : Set ℓ
    zeroExcludedFromRenormalizedOrbitClosure : Set ℓ
    criticalNormUniformlyBoundedOnOrbit : Set ℓ

    selectedProfileIsInitialOrReferenceStateOfSolution : Set ℓ
    mixedDefectBadnessPersistsOnSameSolution : Set ℓ

open MixedDefectAlmostPeriodicDynamics public

round272StaticR271ProfileIsNotYetDynamicSolution : Bool
round272StaticR271ProfileIsNotYetDynamicSolution = true

round272DynamicAlmostPeriodicWeldIsRequired : Bool
round272DynamicAlmostPeriodicWeldIsRequired = true

round272KnownGKPMechanismSuggestsButDoesNotAutomaticallyInstantiateMixedDefectWeld : Bool
round272KnownGKPMechanismSuggestsButDoesNotAutomaticallyInstantiateMixedDefectWeld = true

round272DynamicWeldClosed : Bool
round272DynamicWeldClosed = false

round272PackageAClosed : Bool
round272PackageAClosed = false

round272DynamicWeldClosedIsFalse : round272DynamicWeldClosed ≡ false
round272DynamicWeldClosedIsFalse = refl
