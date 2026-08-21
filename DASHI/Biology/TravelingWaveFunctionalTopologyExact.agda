module DASHI.Biology.TravelingWaveFunctionalTopologyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Earl K. Miller, Scott L. Brincat, Jefferson E. Roy,
-- "Analog Cognition and Consciousness" (2026 preprint/review lineage).
-- DOI: 10.31234/osf.io/z48x7_v3.
--
-- Dimitris A. Pinotsis, Earl K. Miller,
-- "Ephaptic coupling can explain variability in neural activity",
-- Cerebral Cortex (2026).
-- DOI: 10.1093/cercor/bhag098.
--
-- DASHI CONTRIBUTION
--
-- Give finite theorem witnesses for the mechanistic layer requested beneath the
-- existing conscious-access coalition:
--
--   fixed structural edge + changing field gate -> changing effective edge;
--   slow/control gate suppresses or releases a fast/content channel;
--   torus pullback moves a local stencil without changing the carrier;
--   opposite finite phases cancel by actual superposition;
--   the same neural state can have a different successor under a field change.
--
-- These are exact finite structural theorems.  The cited neuroscience motivates
-- the bridge vocabulary but is not imported as proof that cortical cognition is
-- exhausted by this model, that all traveling waves are ephaptic, or that wave
-- control is identical to phenomenal consciousness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Physics.ShiftDiscreteWaveStep as Discrete
import DASHI.Physics.WaveAlgorithmLift as Wave

boolNot : Bool → Bool
boolNot false = true
boolNot true = false

boolAnd : Bool → Bool → Bool
boolAnd false second = false
boolAnd true second = second

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Fixed structural substrate, field-dependent effective coupling.
------------------------------------------------------------------------

effectiveCoupling : Bool → Bool → Bool
effectiveCoupling structuralEdge fieldGate =
  boolAnd structuralEdge fieldGate

canonicalStructuralEdge : Bool
canonicalStructuralEdge = true

openFieldGate : Bool
openFieldGate = true

closedFieldGate : Bool
closedFieldGate = false

openGateEffectiveEdgePresent :
  effectiveCoupling canonicalStructuralEdge openFieldGate ≡ true
openGateEffectiveEdgePresent = refl

closedGateEffectiveEdgeAbsent :
  effectiveCoupling canonicalStructuralEdge closedFieldGate ≡ false
closedGateEffectiveEdgeAbsent = refl

sameStructureDifferentFieldChangesEffectiveTopology :
  effectiveCoupling canonicalStructuralEdge openFieldGate
  ≡ effectiveCoupling canonicalStructuralEdge closedFieldGate → ⊥
sameStructureDifferentFieldChangesEffectiveTopology equality =
  trueNotFalse equality

------------------------------------------------------------------------
-- Cross-frequency control prototype: beta/control gate over gamma/content.
------------------------------------------------------------------------

gammaEffective : Bool → Bool → Bool
gammaEffective slowControl highContent =
  boolAnd (boolNot slowControl) highContent

contentReleasedWhenSlowControlAbsent :
  gammaEffective false true ≡ true
contentReleasedWhenSlowControlAbsent = refl

contentSuppressedWhenSlowControlPresent :
  gammaEffective true true ≡ false
contentSuppressedWhenSlowControlPresent = refl

sameHighContentDifferentSlowControlChangesReadout :
  gammaEffective false true ≡ gammaEffective true true → ⊥
sameHighContentDifferentSlowControlChangesReadout equality =
  trueNotFalse equality

------------------------------------------------------------------------
-- A literal traveling stencil on the completed 3 x 3 torus.
------------------------------------------------------------------------

canonicalStencil : Torus.Field Bool
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueZero Torus.residueZero)) = true
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueMinus Torus.residueMinus)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueMinus Torus.residueZero)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueMinus Torus.residuePlus)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueZero Torus.residueMinus)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueZero Torus.residuePlus)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residuePlus Torus.residueMinus)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residuePlus Torus.residueZero)) = false
canonicalStencil
  (Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residuePlus Torus.residuePlus)) = false
canonicalStencil Torus.completionChannel = false

centerChannel : Torus.CompletedTorusChannel
centerChannel =
  Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueZero Torus.residueZero)

minusFirstChannel : Torus.CompletedTorusChannel
minusFirstChannel =
  Torus.ordinaryTorusChannel
    (Torus.torusPoint Torus.residueMinus Torus.residueZero)

stencilInitiallyAtCenter : canonicalStencil centerChannel ≡ true
stencilInitiallyAtCenter = refl

firstPullbackMovesStencilToMinusFirst :
  Torus.pullbackFirst canonicalStencil minusFirstChannel ≡ true
firstPullbackMovesStencilToMinusFirst = refl

firstPullbackLeavesOldCenter :
  Torus.pullbackFirst canonicalStencil centerChannel ≡ false
firstPullbackLeavesOldCenter = refl

stencilMoveIsNontrivialAtCenter :
  Torus.pullbackFirst canonicalStencil centerChannel
  ≡ canonicalStencil centerChannel → ⊥
stencilMoveIsNontrivialAtCenter equality = falseNotTrue equality

completionRemainsOutsideCanonicalStencil :
  Torus.pullbackFirst canonicalStencil Torus.completionChannel ≡ false
completionRemainsOutsideCanonicalStencil = refl

------------------------------------------------------------------------
-- Analog/interference witness on the already-existing discrete wave carrier.
------------------------------------------------------------------------

oppositePhaseSuperpositionCancels :
  Discrete.waveAdd
    (Wave.encodeTritWave Wave.pos)
    (Wave.encodeTritWave Wave.neg)
  ≡ Wave.zeroWave
oppositePhaseSuperpositionCancels = refl

zeroPlusPositiveDoesNotCancel :
  Discrete.waveAdd
    (Wave.encodeTritWave Wave.zero)
    (Wave.encodeTritWave Wave.pos)
  ≡ Wave.encodeTritWave Wave.pos
zeroPlusPositiveDoesNotCancel = refl

------------------------------------------------------------------------
-- Minimal field-to-successor causal witness.
------------------------------------------------------------------------

fieldControlledStep : Bool → Bool → Bool
fieldControlledStep neuralState fieldState =
  ifField fieldState neuralState
  where
  ifField : Bool → Bool → Bool
  ifField false state = state
  ifField true state = boolNot state

sameNeuronFieldOffSuccessor : fieldControlledStep false false ≡ false
sameNeuronFieldOffSuccessor = refl

sameNeuronFieldOnSuccessor : fieldControlledStep false true ≡ true
sameNeuronFieldOnSuccessor = refl

fieldChangeCanChangeFutureNeuralState :
  fieldControlledStep false false ≡ fieldControlledStep false true → ⊥
fieldChangeCanChangeFutureNeuralState equality = falseNotTrue equality

record TravelingWaveFunctionalBoundary : Set where
  constructor travelingWaveFunctionalBoundary
  field
    finiteGateIsMeasuredBetaGammaLaw : Set
    finiteGateIsNotMeasuredBetaGammaLaw :
      finiteGateIsMeasuredBetaGammaLaw → Set

    finiteFeedbackProvesUniversalEphapticMechanism : Set
    finiteFeedbackDoesNotProveUniversalEphapticMechanism :
      finiteFeedbackProvesUniversalEphapticMechanism → Set

    movingStencilIsPhenomenalConsciousness : Set
    movingStencilIsNotPhenomenalConsciousness :
      movingStencilIsPhenomenalConsciousness → Set

canonicalTravelingWaveFunctionalBoundary : TravelingWaveFunctionalBoundary
canonicalTravelingWaveFunctionalBoundary =
  travelingWaveFunctionalBoundary
    ⊥ (λ impossible → impossible)
    ⊥ (λ impossible → impossible)
    ⊥ (λ impossible → impossible)
