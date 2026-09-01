module DASHI.Cognition.PNF.ContextualFractranSemanticSpectralIntertwinerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SignedSSP
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Bridge
import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Character
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster

------------------------------------------------------------------------
-- Semantic phase does not automatically determine spectral frequency.
-- A selector is explicit.  Once supplied, the existing signed-voxel theorem
-- gives the actual C3 -> Monster phase inversion intertwiner.
------------------------------------------------------------------------

record SemanticSpectralSelector : Set where
  constructor semanticSpectralSelector
  field
    frequencyOfRolePair : Context.OrientedRolePair → Bridge.AxisFrequency

open SemanticSpectralSelector public

contextualMultiplicityMonsterIntertwines :
  (selector : SemanticSpectralSelector) →
  (roles : Context.OrientedRolePair) →
  (multiplicity : SignedSSP.SignedMultiplicity) →
  Fourier.phaseToMonster
    (Character.axisCharacterValue
      (Bridge.conjugateFrequency (frequencyOfRolePair selector roles))
      (Context.coarseSSPTrit multiplicity))
  ≡ Monster.transportPhase Monster.invertsGenerator
      (Fourier.phaseToMonster
        (Character.axisCharacterValue
          (frequencyOfRolePair selector roles)
          (Context.coarseSSPTrit multiplicity)))
contextualMultiplicityMonsterIntertwines selector roles multiplicity =
  Signed.monsterAxisReflectionIntertwines
    (frequencyOfRolePair selector roles)
    (Context.coarseSSPTrit multiplicity)

record SemanticSpectralBoundary : Set where
  constructor semanticSpectralBoundary
  field
    semanticRolePhaseUsesExistingSignedSSPTrit : Bool
    spectralFrequencySelectorIsIndependentTypedData : Bool
    contextualPhaseCanReuseExistingMonsterIntertwiner : Bool
    rolePairAutomaticallyDeterminesMonsterFrequency : Bool
    semanticHyperformFabricIsMonsterRepresentation : Bool

canonicalSemanticSpectralBoundary : SemanticSpectralBoundary
canonicalSemanticSpectralBoundary =
  semanticSpectralBoundary true true true false false
