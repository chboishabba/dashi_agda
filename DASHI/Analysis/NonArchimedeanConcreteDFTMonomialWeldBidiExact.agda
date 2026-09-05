module DASHI.Analysis.NonArchimedeanConcreteDFTMonomialWeldBidiExact where

------------------------------------------------------------------------
-- CONCRETE DFT -> MONOMIAL SAME-OBJECT FRONTIER
--
-- Source `DFT.lean` already owns:
--   * reindex : ZMod(2^(n-1)) ~= ZMod(2^(n-2)) x ZMod 2
--   * mapped concrete twisted matrix over C
--   * reindexed concrete twisted matrix
--   * F tensor I_2 and its star
--   * (F tensor I_2)(F tensor I_2)^* = I
--   * the literal conjugated matrix
--
-- DASHI additionally already owns finite matrix action faithfulness.  Hence
-- entrywise expansion of the full conjugated matrix is only a fallback route:
-- equality on every genuine character-basis vector compiles to literal matrix
-- equality.  The live source-specific work is semantic label attachment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data ConcreteDFTMonomialObligation : Set where
  identifyOddCharacterTauOddSemantics : ConcreteDFTMonomialObligation
  constructArithmeticOddOrbitChart : ConcreteDFTMonomialObligation
  identifyTwistedCoordinatesWithCharacterBasis : ConcreteDFTMonomialObligation
  proveSameActionOnCompleteBasis : ConcreteDFTMonomialObligation
  proveConcreteMonomialMatrixEquality : ConcreteDFTMonomialObligation
  attachOrbitPeriodToSameLabels : ConcreteDFTMonomialObligation
  attachOrbitWeightToSameLabels : ConcreteDFTMonomialObligation

  computeConcreteConjugatedEntries : ConcreteDFTMonomialObligation
  rebuildDFTMatrix : ConcreteDFTMonomialObligation
  rebuildIndexEquivalence : ConcreteDFTMonomialObligation
  rebuildUnitarity : ConcreteDFTMonomialObligation
  assumeEigenvalueMagnitude : ConcreteDFTMonomialObligation


data ObligationDisposition : Set where
  live : ObligationDisposition
  downstream : ObligationDisposition
  compiled : ObligationDisposition
  fallback : ObligationDisposition
  pruned : ObligationDisposition
  forbiddenShortcut : ObligationDisposition

obligationDisposition : ConcreteDFTMonomialObligation → ObligationDisposition
obligationDisposition identifyOddCharacterTauOddSemantics = live
obligationDisposition constructArithmeticOddOrbitChart = live
obligationDisposition identifyTwistedCoordinatesWithCharacterBasis = live
obligationDisposition proveSameActionOnCompleteBasis = downstream
obligationDisposition proveConcreteMonomialMatrixEquality = compiled
obligationDisposition attachOrbitPeriodToSameLabels = downstream
obligationDisposition attachOrbitWeightToSameLabels = downstream
obligationDisposition computeConcreteConjugatedEntries = fallback
obligationDisposition rebuildDFTMatrix = pruned
obligationDisposition rebuildIndexEquivalence = pruned
obligationDisposition rebuildUnitarity = pruned
obligationDisposition assumeEigenvalueMagnitude = forbiddenShortcut

record ConcreteDFTMonomialWeld : Set₁ where
  field
    SpatialIndex : Set
    CharacterIndex : Set
    Scalar : Set

    spatialMatrixEntry : SpatialIndex → SpatialIndex → Scalar
    conjugatedMatrixEntry : CharacterIndex → CharacterIndex → Scalar
    monomialMatrixEntry : CharacterIndex → CharacterIndex → Scalar

    spatialToCharacterIndex : SpatialIndex → CharacterIndex
    characterToSpatialIndex : CharacterIndex → SpatialIndex

    spatialAfterCharacter :
      (k : CharacterIndex) →
      spatialToCharacterIndex (characterToSpatialIndex k) ≡ k

    characterAfterSpatial :
      (x : SpatialIndex) →
      characterToSpatialIndex (spatialToCharacterIndex x) ≡ x

    concreteConjugatedEqualsMonomial :
      (k l : CharacterIndex) →
      conjugatedMatrixEntry k l ≡ monomialMatrixEntry k l

open ConcreteDFTMonomialWeld public

record SameLabelOrbitReceipts (W : ConcreteDFTMonomialWeld) : Set₁ where
  field
    PeriodReceipt : CharacterIndex W → Set
    OrbitWeightReceipt : CharacterIndex W → Set

    periodUsesWeldLabels :
      (k : CharacterIndex W) → PeriodReceipt k → Set

    weightUsesWeldLabels :
      (k : CharacterIndex W) → OrbitWeightReceipt k → Set

open SameLabelOrbitReceipts public

record ConcreteSpectralCircleProducer : Set₁ where
  field
    weld : ConcreteDFTMonomialWeld
    orbitReceipts : SameLabelOrbitReceipts weld
    monomialPowerOrSpectrumCompilerReceipt : Set

open ConcreteSpectralCircleProducer public

highestAlphaDFTMonomialPath : List ConcreteDFTMonomialObligation
highestAlphaDFTMonomialPath =
  constructArithmeticOddOrbitChart ∷
  identifyOddCharacterTauOddSemantics ∷
  identifyTwistedCoordinatesWithCharacterBasis ∷
  proveSameActionOnCompleteBasis ∷
  attachOrbitPeriodToSameLabels ∷
  attachOrbitWeightToSameLabels ∷
  []

entrywiseExpansionIsFallback :
  obligationDisposition computeConcreteConjugatedEntries ≡ fallback
entrywiseExpansionIsFallback = refl

matrixEqualityIsCompiled :
  obligationDisposition proveConcreteMonomialMatrixEquality ≡ compiled
matrixEqualityIsCompiled = refl

assumeFinalMagnitudeForbidden :
  obligationDisposition assumeEigenvalueMagnitude ≡ forbiddenShortcut
assumeFinalMagnitudeForbidden = refl

record BidiBoundary : Set where
  constructor bidiBoundary
  field
    sourceDFTReindexOwned : Bool
    sourceDFTBasisOwned : Bool
    sourceDFTUnitarityOwned : Bool
    sourceConcreteConjugatedMatrixOwned : Bool
    finiteBasisActionFaithfulnessOwnedInDASHI : Bool
    concreteConjugatedToMonomialEqualityOwned : Bool
    finalMagnitudeMayBeUsedAsProducerForItsOwnDerivation : Bool

canonicalBidiBoundary : BidiBoundary
canonicalBidiBoundary =
  bidiBoundary true true true true true false false
