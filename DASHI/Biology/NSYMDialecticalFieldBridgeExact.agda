module DASHI.Biology.NSYMDialecticalFieldBridgeExact where

open import DASHI.Core.Prelude
open import Data.Nat.Properties using (*-identityˡ)

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry

------------------------------------------------------------------------
-- Finite screw-motion/vorticity carrier.

data PlanarPhase : Set where
  eastPhase : PlanarPhase
  northPhase : PlanarPhase
  westPhase : PlanarPhase
  southPhase : PlanarPhase

rotatePhase : PlanarPhase → PlanarPhase
rotatePhase eastPhase = northPhase
rotatePhase northPhase = westPhase
rotatePhase westPhase = southPhase
rotatePhase southPhase = eastPhase

rotatePhaseFour : (p : PlanarPhase) →
  rotatePhase (rotatePhase (rotatePhase (rotatePhase p))) ≡ p
rotatePhaseFour eastPhase = refl
rotatePhaseFour northPhase = refl
rotatePhaseFour westPhase = refl
rotatePhaseFour southPhase = refl

data Handedness : Set where
  rightHanded : Handedness
  leftHanded : Handedness

record VorticityState : Set where
  constructor vorticityState
  field
    planarPhase : PlanarPhase
    axialLevel : Nat
    intensity : Nat
    handedness : Handedness

open VorticityState public

screwStep : VorticityState → VorticityState
screwStep (vorticityState phase z omega hand) =
  vorticityState (rotatePhase phase) (suc z) omega hand

fourScrewSteps : VorticityState → VorticityState
fourScrewSteps state =
  screwStep (screwStep (screwStep (screwStep state)))

phaseReturnsWhileAxialLevelLifts :
  (state : VorticityState) →
  planarPhase (fourScrewSteps state) ≡ planarPhase state
  ×
  axialLevel (fourScrewSteps state)
  ≡ suc (suc (suc (suc (axialLevel state))))
phaseReturnsWhileAxialLevelLifts
  (vorticityState eastPhase z omega hand) = refl , refl
phaseReturnsWhileAxialLevelLifts
  (vorticityState northPhase z omega hand) = refl , refl
phaseReturnsWhileAxialLevelLifts
  (vorticityState westPhase z omega hand) = refl , refl
phaseReturnsWhileAxialLevelLifts
  (vorticityState southPhase z omega hand) = refl , refl

stretchByStrain : Nat → VorticityState → VorticityState
stretchByStrain strain
  (vorticityState phase z omega hand) =
  vorticityState phase z (strain * omega) hand

unitStrainPreservesIntensity :
  (state : VorticityState) →
  intensity (stretchByStrain 1 state) ≡ intensity state
unitStrainPreservesIntensity (vorticityState phase z omega hand) =
  *-identityˡ omega

------------------------------------------------------------------------
-- Finite lattice-gauge carrier.

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

record PlaquetteEdges : Set where
  constructor plaquetteEdges
  field
    edge0 : Bool
    edge1 : Bool
    edge2 : Bool
    edge3 : Bool

open PlaquetteEdges public

plaquetteCurvature : PlaquetteEdges → Bool
plaquetteCurvature (plaquetteEdges a b c d) =
  xor (xor a b) (xor c d)

flatPlaquette : PlaquetteEdges
flatPlaquette = plaquetteEdges false false false false

curvedPlaquette : PlaquetteEdges
curvedPlaquette = plaquetteEdges true false false false

flatPlaquetteHasNoCurvature : plaquetteCurvature flatPlaquette ≡ false
flatPlaquetteHasNoCurvature = refl

curvedPlaquetteHasCurvature : plaquetteCurvature curvedPlaquette ≡ true
curvedPlaquetteHasCurvature = refl

flipAllEdges : PlaquetteEdges → PlaquetteEdges
flipAllEdges (plaquetteEdges a b c d) =
  plaquetteEdges (xor true a) (xor true b) (xor true c) (xor true d)

canonicalGaugeFlipPreservesCurvature :
  plaquetteCurvature (flipAllEdges curvedPlaquette)
  ≡ plaquetteCurvature curvedPlaquette
canonicalGaugeFlipPreservesCurvature = refl

------------------------------------------------------------------------
-- Finite spectral/mass-gap package.

data GaugeExcitation : Set where
  vacuum : GaugeExcitation
  glueballCandidate : GaugeExcitation
  higherInvariantPacket : GaugeExcitation

excitationEnergy : GaugeExcitation → Nat
excitationEnergy vacuum = 0
excitationEnergy glueballCandidate = 1
excitationEnergy higherInvariantPacket = 3

finiteMassGap : Nat
finiteMassGap = excitationEnergy glueballCandidate ∸ excitationEnergy vacuum

finiteMassGapIsOne : finiteMassGap ≡ 1
finiteMassGapIsOne = refl

record IrrepConstrainedPacket : Set where
  constructor irrepConstrainedPacket
  field
    packetEnergy : Nat
    packetSector : Symmetry.SymmetrySector
    gaugeInvariantPacket : Bool
    asymptoticallyFreePacket : Bool

open IrrepConstrainedPacket public

canonicalGaugeInvariantPacket : IrrepConstrainedPacket
canonicalGaugeInvariantPacket =
  irrepConstrainedPacket
    1
    (Symmetry.symmetrySector Symmetry.A1 Symmetry.positiveOrientation)
    true
    false

------------------------------------------------------------------------
-- Boundaries for the Clay-facing interpretation.

record NSYMDialecticalBoundary : Set where
  constructor nsymDialecticalBoundary
  field
    screwMotionSolvesNavierStokesClay : Bool
    screwMotionSolvesNavierStokesClayIsFalse :
      screwMotionSolvesNavierStokesClay ≡ false

    rightHandRuleMakesThreeDimensionalFlowTrivial : Bool
    rightHandRuleMakesThreeDimensionalFlowTrivialIsFalse :
      rightHandRuleMakesThreeDimensionalFlowTrivial ≡ false

    finiteGaugeGapConstructsContinuumQuantumYangMills : Bool
    finiteGaugeGapConstructsContinuumQuantumYangMillsIsFalse :
      finiteGaugeGapConstructsContinuumQuantumYangMills ≡ false

    irrepLabelAloneDeterminesParticleEnergy : Bool
    irrepLabelAloneDeterminesParticleEnergyIsFalse :
      irrepLabelAloneDeterminesParticleEnergy ≡ false

    coarseGrainingAndLatentPathsDeriveAllQuantumPredictions : Bool
    coarseGrainingAndLatentPathsDeriveAllQuantumPredictionsIsFalse :
      coarseGrainingAndLatentPathsDeriveAllQuantumPredictions ≡ false

    latticeGaugeTheoryIsRelevantConstructionRoute : Bool
    latticeGaugeTheoryIsRelevantConstructionRouteIsTrue :
      latticeGaugeTheoryIsRelevantConstructionRoute ≡ true

open NSYMDialecticalBoundary public

canonicalNSYMDialecticalBoundary : NSYMDialecticalBoundary
canonicalNSYMDialecticalBoundary =
  nsymDialecticalBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
