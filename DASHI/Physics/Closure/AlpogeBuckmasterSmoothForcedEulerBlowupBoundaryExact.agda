module DASHI.Physics.Closure.AlpogeBuckmasterSmoothForcedEulerBlowupBoundaryExact where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.NSTriadKNSmoothForcedBlowupAdversarialBoundaryRound521Exact as R521

------------------------------------------------------------------------
-- ALPOGE--BUCKMASTER SMOOTH-FORCED 3D EULER RESULT: EXTERNAL THEOREM BOUNDARY.
--
-- Attribution / snowball rule:
--   * the Fourier/Galerkin nonlinear carrier is historical DASHI work;
--   * this September owner receives NO origin/priority credit for Euler;
--   * the released smooth-forced Euler blowup theorem/construction remains
--     attributed externally to Alpoge--Buckmaster and its cited antecedents;
--   * shared carrier or similar cancellation structure does not manufacture
--     theorem identity, access, copying, or priority.
--
-- This module therefore sits directly on the pre-existing Galerkin carrier.
-- It does not introduce a second Euler equation ontology.
------------------------------------------------------------------------

record AlpogeBuckmasterForcedEulerTheorem
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (Time : Set)
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    timeDerivative forcing : Z3.FourierMode → C3.Complex3 F

    projectedForcedEulerODE :
      (k : Z3.FourierMode) → Galerkin.modeListed system k →
      timeDerivative k
      ≡ C3.complex3Add
          (Galerkin.projectedNonlinearity system k)
          (forcing k)

    terminalTime : Time
    divergenceFreePreserved : Set
    realityConditionPreserved : Set
    forcingTransverse : Set

    smoothInitialVelocity : Set
    smoothForcingThroughTerminalTime : Set
    finiteEnergyBeforeTerminalTime : Set
    classicalSolutionBeforeTerminalTime : Set
    uniquenessInClaimedClassBeforeTerminalTime : Set

    axisymmetricInitialData : Set
    initialSwirlNonzero : Set
    initialMeridionalVelocityZero : Set
    compactSupportInFixedSolidTorus : Set

    forcingAxisymmetric : Set
    forcingSupportedInFixedSolidTorus : Set

    circulationRemainsBoundedBeforeTerminalTime : Set
    meridionalVelocityRemainsBoundedBeforeTerminalTime : Set
    circulationGradientBecomesUnbounded : Set
    vorticityBecomesUnbounded : Set
    bkmBlowupCriterionTriggered : Set

open AlpogeBuckmasterForcedEulerTheorem public

------------------------------------------------------------------------
-- Attribution / status.
------------------------------------------------------------------------

historicalDASHIGalerkinCarrierPredatesThisAdapter : Bool
historicalDASHIGalerkinCarrierPredatesThisAdapter = true

thisAdapterReceivesEulerOriginPriorityCredit : Bool
thisAdapterReceivesEulerOriginPriorityCredit = false

r521AlreadyTrackedReleasedForcedEulerResult : Bool
r521AlreadyTrackedReleasedForcedEulerResult = true

r521AlreadyContainedExternalEulerConstruction : Bool
r521AlreadyContainedExternalEulerConstruction = false

externalLeanProofTranscribedIntoDASHIHere : Bool
externalLeanProofTranscribedIntoDASHIHere = false

externalConstructionMechanismReproducedHere : Bool
externalConstructionMechanismReproducedHere = false

forcedEulerBlowupPaysUnforcedNSLeafA : Bool
forcedEulerBlowupPaysUnforcedNSLeafA = false

thisAdapterReceivesEulerOriginPriorityCreditIsFalse :
  thisAdapterReceivesEulerOriginPriorityCredit ≡ false
thisAdapterReceivesEulerOriginPriorityCreditIsFalse = refl

externalLeanProofTranscribedIntoDASHIHereIsFalse :
  externalLeanProofTranscribedIntoDASHIHere ≡ false
externalLeanProofTranscribedIntoDASHIHereIsFalse = refl

externalConstructionMechanismReproducedHereIsFalse :
  externalConstructionMechanismReproducedHere ≡ false
externalConstructionMechanismReproducedHereIsFalse = refl

forcedEulerBlowupPaysUnforcedNSLeafAIsFalse :
  forcedEulerBlowupPaysUnforcedNSLeafA ≡ false
forcedEulerBlowupPaysUnforcedNSLeafAIsFalse = refl
