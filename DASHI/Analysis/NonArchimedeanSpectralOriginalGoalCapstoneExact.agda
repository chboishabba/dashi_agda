module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL / POST-CLOSURE CAPSTONE
--
-- The finite non-Archimedean spectral core is dependency-closed in DASHI.
-- Post-closure audits now separate sigma semantics, continuous-transfer claims,
-- and finite Markov/mixing consumers.  The old unit-prefactor L2 route is
-- refuted; the viable repair is a finite level-dependent prefactor assembled
-- through the unitary Fourier shell-energy chart.
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

  meanZeroInvariant : OriginalGoalLeaf
  unitPrefactorOneStepL2 : OriginalGoalLeaf
  explicitLevelSquaredPrefactor : OriginalGoalLeaf
  prefactoredL2ShellCompiler : OriginalGoalLeaf
  parsevalShellEnergyWeld : OriginalGoalLeaf
  prefactoredL2WholeOperator : OriginalGoalLeaf
  killedKernelSurvivalBound : OriginalGoalLeaf
  gibbsUniqueness : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  sourceOwned : OriginalGoalStatus
  owned : OriginalGoalStatus
  compiled : OriginalGoalStatus
  repoReusable : OriginalGoalStatus
  sourcePlaceholderButRepoCompiled : OriginalGoalStatus
  rejectedReading : OriginalGoalStatus
  refuted : OriginalGoalStatus
  sourceUnproved : OriginalGoalStatus
  liveSameObjectWeld : OriginalGoalStatus
  liveIndependentProducer : OriginalGoalStatus
  downstream : OriginalGoalStatus

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
leafStatus fullTransferRadiusSqrtTwo = rejectedReading
leafStatus cyclotomicToProlateSigmaAnchor = liveSameObjectWeld
leafStatus undirectedGapExponentAlpha = sourceOwned

leafStatus meanZeroInvariant = compiled
leafStatus unitPrefactorOneStepL2 = refuted
leafStatus explicitLevelSquaredPrefactor = owned
leafStatus prefactoredL2ShellCompiler = compiled
leafStatus parsevalShellEnergyWeld = liveSameObjectWeld
leafStatus prefactoredL2WholeOperator = downstream
leafStatus killedKernelSurvivalBound = liveIndependentProducer
leafStatus gibbsUniqueness = liveIndependentProducer

priority : List OriginalGoalLeaf
priority =
  parsevalShellEnergyWeld ∷
  prefactoredL2WholeOperator ∷
  killedKernelSurvivalBound ∷
  cyclotomicToProlateSigmaAnchor ∷
  gibbsUniqueness ∷
  []

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

record MixingRepairBoundary : Set where
  constructor mixingRepairBoundary
  field
    meanZeroInvariantCompiled : Bool
    unitPrefactorOneStepContractionValid : Bool
    explicitFiniteLevelPrefactorOwned : Bool
    shellPowerCompilerOwned : Bool
    genericFiniteEnergyAssemblyOwned : Bool
    parsevalShellEnergySameObjectWeldOwned : Bool
    wholePrefactoredL2BoundOwned : Bool
    killedKernelBoundOwned : Bool

canonicalMixingRepairBoundary : MixingRepairBoundary
canonicalMixingRepairBoundary =
  mixingRepairBoundary true false true true true false false false

unitPrefactorMixingRouteClosedNegative :
  MixingRepairBoundary.unitPrefactorOneStepContractionValid
    canonicalMixingRepairBoundary
  ≡ false
unitPrefactorMixingRouteClosedNegative = refl

prefactoredMixingRouteStillLiveAtParsevalWeld :
  MixingRepairBoundary.parsevalShellEnergySameObjectWeldOwned
    canonicalMixingRepairBoundary
  ≡ false
prefactoredMixingRouteStillLiveAtParsevalWeld = refl

localAndProlateHalvesDoNotAutoWeld :
  SigmaClosureBoundary.sameObjectAnchorLocated canonicalSigmaClosureBoundary
  ≡ false
localAndProlateHalvesDoNotAutoWeld = refl

sizeExponentHalfReadingRejected :
  SigmaClosureBoundary.radiusNSizePowerHalfReadingValid
    canonicalSigmaClosureBoundary
  ≡ false
sizeExponentHalfReadingRejected = refl
