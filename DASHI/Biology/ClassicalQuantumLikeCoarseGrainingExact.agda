module DASHI.Biology.ClassicalQuantumLikeCoarseGrainingExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.DeterministicCoarseGrainingBoundary as Existing
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry

------------------------------------------------------------------------
-- Reuse the repository's exact deterministic coarse-graining no-go.

existingCoarseGrainingBoundary : Existing.DeterministicCoarseGrainingBoundary
existingCoarseGrainingBoundary =
  Existing.canonicalDeterministicCoarseGrainingBoundary

------------------------------------------------------------------------
-- Context updates need not commute even in a finite classical state machine.

contextA : Triadic.KernelTrit → Triadic.KernelTrit
contextA Triadic.negativeTrit = Triadic.zeroTrit
contextA Triadic.zeroTrit = Triadic.positiveTrit
contextA Triadic.positiveTrit = Triadic.positiveTrit

contextB : Triadic.KernelTrit → Triadic.KernelTrit
contextB = Triadic.negateTrit

AAfterBAtNegative :
  contextA (contextB Triadic.negativeTrit) ≡ Triadic.positiveTrit
AAfterBAtNegative = refl

BAfterAAtNegative :
  contextB (contextA Triadic.negativeTrit) ≡ Triadic.zeroTrit
BAfterAAtNegative = refl

positiveNotZero : ¬ (Triadic.positiveTrit ≡ Triadic.zeroTrit)
positiveNotZero ()

contextOrderDoesNotCommuteAtNegative :
  ¬ (contextA (contextB Triadic.negativeTrit)
     ≡ contextB (contextA Triadic.negativeTrit))
contextOrderDoesNotCommuteAtNegative = positiveNotZero

------------------------------------------------------------------------
-- Same visible state, different latent path, different next observation.

data LatentPath : Set where
  directPath : LatentPath
  reflectedPath : LatentPath

record PathRefinedState : Set where
  constructor pathRefinedState
  field
    visibleTrit : Triadic.KernelTrit
    latentPath : LatentPath

open PathRefinedState public

pathDependentStep : PathRefinedState → PathRefinedState
pathDependentStep
  (pathRefinedState Triadic.zeroTrit directPath) =
  pathRefinedState Triadic.positiveTrit directPath
pathDependentStep
  (pathRefinedState Triadic.zeroTrit reflectedPath) =
  pathRefinedState Triadic.negativeTrit reflectedPath
pathDependentStep (pathRefinedState x path) =
  pathRefinedState x path

visibleDirectZero : PathRefinedState
visibleDirectZero = pathRefinedState Triadic.zeroTrit directPath

visibleReflectedZero : PathRefinedState
visibleReflectedZero = pathRefinedState Triadic.zeroTrit reflectedPath

pathsShareVisibleZero :
  visibleTrit visibleDirectZero ≡ visibleTrit visibleReflectedZero
pathsShareVisibleZero = refl

pathsHaveDifferentNextVisibleStates :
  visibleTrit (pathDependentStep visibleDirectZero) ≡ Triadic.positiveTrit
  ×
  visibleTrit (pathDependentStep visibleReflectedZero) ≡ Triadic.negativeTrit
pathsHaveDifferentNextVisibleStates = refl , refl

------------------------------------------------------------------------
-- Symmetry and constraints lower the accessible finite-state ceiling.

data AccessibilitySector : Set where
  unconstrainedNineSheet : AccessibilitySector
  typedHexagramSector : AccessibilitySector
  tenSymmetryChannels : AccessibilitySector

accessibleStateCount : AccessibilitySector → Nat
accessibleStateCount unconstrainedNineSheet = 19683
accessibleStateCount typedHexagramSector = 729
accessibleStateCount tenSymmetryChannels = 10

unconstrainedCeilingIs19683 :
  accessibleStateCount unconstrainedNineSheet ≡ 19683
unconstrainedCeilingIs19683 = refl

typedSectorCeilingIs729 :
  accessibleStateCount typedHexagramSector ≡ 729
typedSectorCeilingIs729 = refl

------------------------------------------------------------------------
-- Representation-labelled finite energy packets.

record RepresentationPacket : Set where
  constructor representationPacket
  field
    energyLevel : Nat
    sector : Symmetry.SymmetrySector
    gaugeInvariant : Bool
    freelyPropagating : Bool

open RepresentationPacket public

canonicalPacket : RepresentationPacket
canonicalPacket =
  representationPacket
    1
    (Symmetry.symmetrySector Symmetry.E2 Symmetry.positiveOrientation)
    true
    false

record QuantumLikeBoundary : Set where
  constructor quantumLikeBoundary
  field
    contextNoncommutationProvesQuantumMechanics : Bool
    contextNoncommutationProvesQuantumMechanicsIsFalse :
      contextNoncommutationProvesQuantumMechanics ≡ false

    latentPathDependenceIsQuantumInterference : Bool
    latentPathDependenceIsQuantumInterferenceIsFalse :
      latentPathDependenceIsQuantumInterference ≡ false

    representationPacketIsPhysicalQuantumParticle : Bool
    representationPacketIsPhysicalQuantumParticleIsFalse :
      representationPacketIsPhysicalQuantumParticle ≡ false

    BornRuleDerived : Bool
    BornRuleDerivedIsFalse : BornRuleDerived ≡ false

    tensorProductCompositionDerived : Bool
    tensorProductCompositionDerivedIsFalse :
      tensorProductCompositionDerived ≡ false

    BellOrContextualitySeparationDerived : Bool
    BellOrContextualitySeparationDerivedIsFalse :
      BellOrContextualitySeparationDerived ≡ false

open QuantumLikeBoundary public

canonicalQuantumLikeBoundary : QuantumLikeBoundary
canonicalQuantumLikeBoundary =
  quantumLikeBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
