module DASHI.Physics.Closure.AlpogeBuckmasterSmoothForcedEulerBlowupBoundaryExact where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.IncompressibleEulerGalerkinCoreExact as Euler
import DASHI.Physics.Closure.NSTriadKNSmoothForcedBlowupAdversarialBoundaryRound521Exact as R521

------------------------------------------------------------------------
-- ALPOGE--BUCKMASTER SMOOTH-FORCED 3D EULER RESULT: THEOREM INTERFACE.
--
-- Public result, September 2026, reported by Buckmaster/Alpoge and discussed
-- by Terence Tao: finite-time blowup for 3D incompressible Euler with a forcing
-- that remains smooth through the terminal time.
--
-- This owner does NOT import or reproduce their Lean proof.  It gives their
-- result a first-class target on the general Euler carrier so that a later
-- paper/Lean transcription can inhabit the theorem without changing the PDE
-- ontology.  Attribution remains external.
------------------------------------------------------------------------

record AlpogeBuckmasterForcedEulerTheorem
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (Time : Set)
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    blowupWitness : Euler.SmoothForcedEulerBlowupWitness Time system

    axisymmetricInitialData : Set
    initialSwirlNonzero : Set
    initialMeridionalVelocityZero : Set
    compactSupportInFixedSolidTorus : Set

    forcingAxisymmetric : Set
    forcingSmoothThroughTerminalTime : Set
    forcingSupportedInFixedSolidTorus : Set

    circulationRemainsBoundedBeforeTerminalTime : Set
    meridionalVelocityRemainsBoundedBeforeTerminalTime : Set
    circulationGradientBecomesUnbounded : Set
    vorticityBecomesUnbounded : Set
    bkmBlowupCriterionTriggered : Set

open AlpogeBuckmasterForcedEulerTheorem public

------------------------------------------------------------------------
-- Relation to the existing NS comparison owner.
------------------------------------------------------------------------

r521AlreadyTrackedReleasedForcedEulerResult : Bool
r521AlreadyTrackedReleasedForcedEulerResult = true

r521AlreadyContainedExternalEulerConstruction : Bool
r521AlreadyContainedExternalEulerConstruction = false

externalEulerTheoremNowHasGeneralDASHIInterface : Bool
externalEulerTheoremNowHasGeneralDASHIInterface = true

externalLeanProofTranscribedIntoDASHIHere : Bool
externalLeanProofTranscribedIntoDASHIHere = false

externalConstructionMechanismReproducedHere : Bool
externalConstructionMechanismReproducedHere = false

forcedEulerBlowupPaysUnforcedNSLeafA : Bool
forcedEulerBlowupPaysUnforcedNSLeafA = false

externalLeanProofTranscribedIntoDASHIHereIsFalse :
  externalLeanProofTranscribedIntoDASHIHere ≡ false
externalLeanProofTranscribedIntoDASHIHereIsFalse = refl

externalConstructionMechanismReproducedHereIsFalse :
  externalConstructionMechanismReproducedHere ≡ false
externalConstructionMechanismReproducedHereIsFalse = refl

forcedEulerBlowupPaysUnforcedNSLeafAIsFalse :
  forcedEulerBlowupPaysUnforcedNSLeafA ≡ false
forcedEulerBlowupPaysUnforcedNSLeafAIsFalse = refl
