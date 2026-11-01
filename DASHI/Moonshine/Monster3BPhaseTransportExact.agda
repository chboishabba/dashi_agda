module DASHI.Moonshine.Monster3BPhaseTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.  ISBN: 978-1-4684-9458-7.  No DOI asserted here.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Make explicit the distinction between the subgroup fixing a chosen 3B
-- generator and the full normalizer of its cyclic subgroup.  An element that
-- sends g to g^-1 exchanges the zeta and zeta^2 eigenspaces.  Therefore one
-- nontrivial eigenspace is naturally a module for the phase-preserving
-- inertia subgroup, while their direct sum is preserved by the full
-- normalizer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)


data C3Phase : Set where
  invariantPhase : C3Phase
  zetaPhase : C3Phase
  zetaSquaredPhase : C3Phase

inversePhase : C3Phase → C3Phase
inversePhase invariantPhase = invariantPhase
inversePhase zetaPhase = zetaSquaredPhase
inversePhase zetaSquaredPhase = zetaPhase

inversePhaseInvolutive : (phase : C3Phase) →
  inversePhase (inversePhase phase) ≡ phase
inversePhaseInvolutive invariantPhase = refl
inversePhaseInvolutive zetaPhase = refl
inversePhaseInvolutive zetaSquaredPhase = refl

phaseDimension : C3Phase → Nat
phaseDimension invariantPhase = 65663
phaseDimension zetaPhase = 65610
phaseDimension zetaSquaredPhase = 65610

inversePreservesPhaseDimension : (phase : C3Phase) →
  phaseDimension (inversePhase phase) ≡ phaseDimension phase
inversePreservesPhaseDimension invariantPhase = refl
inversePreservesPhaseDimension zetaPhase = refl
inversePreservesPhaseDimension zetaSquaredPhase = refl

nontrivialPairDimension : Nat
nontrivialPairDimension =
  phaseDimension zetaPhase + phaseDimension zetaSquaredPhase

nontrivialPairDimensionIs131220 : nontrivialPairDimension ≡ 131220
nontrivialPairDimensionIs131220 = refl


data CyclicNormalizerMode : Set where
  fixesGenerator : CyclicNormalizerMode
  invertsGenerator : CyclicNormalizerMode

transportPhase : CyclicNormalizerMode → C3Phase → C3Phase
transportPhase fixesGenerator phase = phase
transportPhase invertsGenerator phase = inversePhase phase

fixingModePreservesZeta :
  transportPhase fixesGenerator zetaPhase ≡ zetaPhase
fixingModePreservesZeta = refl

invertingModeSwapsZeta :
  transportPhase invertsGenerator zetaPhase ≡ zetaSquaredPhase
invertingModeSwapsZeta = refl

invertingModeSwapsZetaSquared :
  transportPhase invertsGenerator zetaSquaredPhase ≡ zetaPhase
invertingModeSwapsZetaSquared = refl

transportPreservesDimensions :
  (mode : CyclicNormalizerMode) →
  (phase : C3Phase) →
  phaseDimension (transportPhase mode phase) ≡ phaseDimension phase
transportPreservesDimensions fixesGenerator phase = refl
transportPreservesDimensions invertsGenerator phase =
  inversePreservesPhaseDimension phase

record PhaseTransportBoundary : Set where
  constructor phaseTransportBoundary
  field
    oneNontrivialSectorIsAutomaticallyFullNormalizerModule : Bool
    oneNontrivialSectorIsAutomaticallyFullNormalizerModuleIsFalse :
      oneNontrivialSectorIsAutomaticallyFullNormalizerModule ≡ false
    nontrivialPairIsNormalizerStableCandidate : Bool
    nontrivialPairIsNormalizerStableCandidateIsTrue :
      nontrivialPairIsNormalizerStableCandidate ≡ true
    actualMonsterNormalizerActionImported : Bool
    actualMonsterNormalizerActionImportedIsFalse :
      actualMonsterNormalizerActionImported ≡ false

canonicalPhaseTransportBoundary : PhaseTransportBoundary
canonicalPhaseTransportBoundary =
  phaseTransportBoundary false refl true refl false refl
