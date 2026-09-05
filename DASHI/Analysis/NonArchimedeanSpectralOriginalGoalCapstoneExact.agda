module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- The finite non-Archimedean spectral core is dependency-closed in DASHI.
-- Post-closure, the remaining claim-strength issue is no longer the value 1/2
-- itself.  The source contains several distinct half-valued coordinates, and
-- only an explicit same-object theorem may identify them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OriginalGoalLeaf : Set where
  functionLevelCharacterAction : OriginalGoalLeaf
  oddCharacterTauOddIff : OriginalGoalLeaf
  correctedOddCharacterDFT : OriginalGoalLeaf
  binarySheetTauOddEquivalence : OriginalGoalLeaf
  concreteSourceSheetAdapter : OriginalGoalLeaf
  twistedRestrictionIntertwiner : OriginalGoalLeaf
  canonicalOddOrbitPackage : OriginalGoalLeaf
  signedFullReturn : OriginalGoalLeaf
  completeCharacterBasisActionEquality : OriginalGoalLeaf
  concreteDFTConjugatedEqualsMonomial : OriginalGoalLeaf
  characteristicDeterminantFactorization : OriginalGoalLeaf
  literalOneStepSpectrumUnion : OriginalGoalLeaf

  directedRadiusSizeExponentHalf : OriginalGoalLeaf
  cyclotomicSigmaHalf : OriginalGoalLeaf
  prolateCriticalLineHalf : OriginalGoalLeaf
  fullTransferRadiusSqrtTwo : OriginalGoalLeaf
  cyclotomicToProlateSigmaAnchor : OriginalGoalLeaf
  undirectedGapExponentAlpha : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  sourceOwned : OriginalGoalStatus
  owned : OriginalGoalStatus
  compiled : OriginalGoalStatus
  repoReusable : OriginalGoalStatus
  sourcePlaceholderButRepoCompiled : OriginalGoalStatus
  rejectedReading : OriginalGoalStatus
  sourceUnproved : OriginalGoalStatus
  liveSameObjectWeld : OriginalGoalStatus

leafStatus : OriginalGoalLeaf → OriginalGoalStatus
leafStatus functionLevelCharacterAction = sourceOwned
leafStatus oddCharacterTauOddIff = compiled
leafStatus correctedOddCharacterDFT = repoReusable
leafStatus binarySheetTauOddEquivalence = owned
leafStatus concreteSourceSheetAdapter = compiled
leafStatus twistedRestrictionIntertwiner = compiled
leafStatus canonicalOddOrbitPackage = compiled
leafStatus signedFullReturn = compiled
leafStatus completeCharacterBasisActionEquality = compiled
leafStatus concreteDFTConjugatedEqualsMonomial = compiled
leafStatus characteristicDeterminantFactorization = compiled
leafStatus literalOneStepSpectrumUnion = sourcePlaceholderButRepoCompiled

leafStatus directedRadiusSizeExponentHalf = rejectedReading
leafStatus cyclotomicSigmaHalf = compiled
leafStatus prolateCriticalLineHalf = sourceOwned
leafStatus fullTransferRadiusSqrtTwo = sourceUnproved
leafStatus cyclotomicToProlateSigmaAnchor = liveSameObjectWeld
leafStatus undirectedGapExponentAlpha = sourceOwned

priority : List OriginalGoalLeaf
priority =
  cyclotomicToProlateSigmaAnchor ∷ []

record FiniteCoreClosure : Set where
  constructor finiteCoreClosure
  field
    sourceSheetAdapterNeedsNewMathematics : Bool
    sourceSheetAdapterCompilesFromCheckedDefinitions : Bool
    canonicalOrbitLaneClosed : Bool
    signedReturnLaneClosed : Bool
    correctedCharacterDFTReusesExistingTheory : Bool
    commonSpatialIntertwinerClosed : Bool
    literalMonomialEqualityClosed : Bool
    characteristicRootUnionClosed : Bool
    finiteSpectralCoreHasRemainingMathematicalProducer : Bool

canonicalFiniteCoreClosure : FiniteCoreClosure
canonicalFiniteCoreClosure =
  finiteCoreClosure false true true true true true true true false

finiteCoreHasNoRemainingMathematicalProducer :
  FiniteCoreClosure.finiteSpectralCoreHasRemainingMathematicalProducer
    canonicalFiniteCoreClosure
  ≡ false
finiteCoreHasNoRemainingMathematicalProducer = refl

record SigmaClosureBoundary : Set where
  constructor sigmaClosureBoundary
  field
    primitiveTwistedRadiusAtTwoIsSqrtTwoOwned : Bool
    localCyclotomicHalfCompiled : Bool
    prolateCriticalHalfOwned : Bool
    fullTransferOperatorRadiusSqrtTwoOwned : Bool
    radiusNSizePowerHalfReadingValid : Bool
    commonSemilocalTensorImpliesSigmaIdentification : Bool
    sameObjectAnchorLocated : Bool

canonicalSigmaClosureBoundary : SigmaClosureBoundary
canonicalSigmaClosureBoundary =
  sigmaClosureBoundary true true true false false false false

localAndProlateHalvesDoNotAutoWeld :
  SigmaClosureBoundary.sameObjectAnchorLocated canonicalSigmaClosureBoundary
  ≡ false
localAndProlateHalvesDoNotAutoWeld = refl

fullTransferRadiusSqrtTwoStillUnproved :
  SigmaClosureBoundary.fullTransferOperatorRadiusSqrtTwoOwned
    canonicalSigmaClosureBoundary
  ≡ false
fullTransferRadiusSqrtTwoStillUnproved = refl

sizeExponentHalfReadingRejected :
  SigmaClosureBoundary.radiusNSizePowerHalfReadingValid
    canonicalSigmaClosureBoundary
  ≡ false
sizeExponentHalfReadingRejected = refl
