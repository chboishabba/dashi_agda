module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL / POST-CLOSURE CAPSTONE
--
-- The finite non-Archimedean spectral core is dependency-closed in DASHI.
-- Post-closure audits now distinguish:
--
--   * false unit-prefactor / universal-tail claims (refuted);
--   * repaired finite prefactored L2, covariance and TV consumers (closed);
--   * constructive set-dependent stopping tails (closed);
--   * polynomial stopping moments (one standard analytic consumer leaf);
--   * sigma same-object promotion and infinite Gibbs uniqueness (still live).
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
  hilbertCorrelationDecay : OriginalGoalLeaf
  stationaryCovarianceDecay : OriginalGoalLeaf
  totalVariationMixing : OriginalGoalLeaf

  universalStoppingSurvivalBound : OriginalGoalLeaf
  forwardTranslationReachabilityCompiler : OriginalGoalLeaf
  zmodCyclicPredecessorAdapter : OriginalGoalLeaf
  zmodFiniteEnumerationAdapter : OriginalGoalLeaf
  finiteUniformHittingBlockCompiler : OriginalGoalLeaf
  binaryOutcomeEnumeration : OriginalGoalLeaf
  survivorCountDecay : OriginalGoalLeaf
  prefixHitAbsorptionWeld : OriginalGoalLeaf
  probabilityNormalization : OriginalGoalLeaf
  setDependentConstructiveTail : OriginalGoalLeaf
  polynomialStoppingMoments : OriginalGoalLeaf
  universalHalfLogTwoMGFDomain : OriginalGoalLeaf

  finiteUniqueUniformStationary : OriginalGoalLeaf
  gibbsUniqueness : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  sourceOwned : OriginalGoalStatus
  owned : OriginalGoalStatus
  compiled : OriginalGoalStatus
  repoReusable : OriginalGoalStatus
  sourceLibraryCompiled : OriginalGoalStatus
  sourcePlaceholderButRepoCompiled : OriginalGoalStatus
  rejectedReading : OriginalGoalStatus
  refuted : OriginalGoalStatus
  liveSameObjectWeld : OriginalGoalStatus
  liveIndependentProducer : OriginalGoalStatus
  liveStandardConsumer : OriginalGoalStatus

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
leafStatus parsevalShellEnergyWeld = sourceLibraryCompiled
leafStatus prefactoredL2WholeOperator = compiled
leafStatus hilbertCorrelationDecay = sourceLibraryCompiled
leafStatus stationaryCovarianceDecay = sourceLibraryCompiled
leafStatus totalVariationMixing = sourceLibraryCompiled

leafStatus universalStoppingSurvivalBound = refuted
leafStatus forwardTranslationReachabilityCompiler = compiled
leafStatus zmodCyclicPredecessorAdapter = sourceLibraryCompiled
leafStatus zmodFiniteEnumerationAdapter = sourceOwned
leafStatus finiteUniformHittingBlockCompiler = repoReusable
leafStatus binaryOutcomeEnumeration = repoReusable
leafStatus survivorCountDecay = repoReusable
leafStatus prefixHitAbsorptionWeld = compiled
leafStatus probabilityNormalization = repoReusable
leafStatus setDependentConstructiveTail = compiled
leafStatus polynomialStoppingMoments = liveStandardConsumer
leafStatus universalHalfLogTwoMGFDomain = refuted

leafStatus finiteUniqueUniformStationary = sourceLibraryCompiled
leafStatus gibbsUniqueness = liveIndependentProducer

priority : List OriginalGoalLeaf
priority =
  polynomialStoppingMoments ∷
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
    parsevalShellEnergySameObjectWeldOwned : Bool
    wholePrefactoredL2BoundOwned : Bool
    stationaryCovarianceDecayOwned : Bool
    totalVariationMixingOwned : Bool
    universalStoppingTailValid : Bool
    forwardTranslationCompilerOwned : Bool
    finiteUniformHittingBlockMathOwned : Bool
    binaryOutcomeEnumerationOwned : Bool
    survivorCountDecayOwned : Bool
    zmodCyclicAdapterOwned : Bool
    zmodFiniteEnumerationOwned : Bool
    prefixHitAbsorptionWeldOwned : Bool
    probabilityNormalizationOwned : Bool
    setDependentConstructiveTailOwned : Bool
    allPolynomialStoppingMomentsOwned : Bool
    universalHalfLogTwoMGFDomainValid : Bool

canonicalMixingRepairBoundary : MixingRepairBoundary
canonicalMixingRepairBoundary =
  mixingRepairBoundary
    true false true true true true true true false
    true true true true true true true true true false false

unitPrefactorMixingRouteClosedNegative :
  MixingRepairBoundary.unitPrefactorOneStepContractionValid
    canonicalMixingRepairBoundary
  ≡ false
unitPrefactorMixingRouteClosedNegative = refl

prefactoredMixingRouteClosedPositive :
  MixingRepairBoundary.wholePrefactoredL2BoundOwned
    canonicalMixingRepairBoundary
  ≡ true
prefactoredMixingRouteClosedPositive = refl

totalVariationRouteClosedPositive :
  MixingRepairBoundary.totalVariationMixingOwned
    canonicalMixingRepairBoundary
  ≡ true
totalVariationRouteClosedPositive = refl

universalStoppingTailClosedNegative :
  MixingRepairBoundary.universalStoppingTailValid
    canonicalMixingRepairBoundary
  ≡ false
universalStoppingTailClosedNegative = refl

constructiveStoppingTailClosedPositive :
  MixingRepairBoundary.setDependentConstructiveTailOwned
    canonicalMixingRepairBoundary
  ≡ true
constructiveStoppingTailClosedPositive = refl

polynomialMomentsRemainConsumerLeaf :
  MixingRepairBoundary.allPolynomialStoppingMomentsOwned
    canonicalMixingRepairBoundary
  ≡ false
polynomialMomentsRemainConsumerLeaf = refl

universalHalfLogTwoMGFDomainRejected :
  MixingRepairBoundary.universalHalfLogTwoMGFDomainValid
    canonicalMixingRepairBoundary
  ≡ false
universalHalfLogTwoMGFDomainRejected = refl

localAndProlateHalvesDoNotAutoWeld :
  SigmaClosureBoundary.sameObjectAnchorLocated canonicalSigmaClosureBoundary
  ≡ false
localAndProlateHalvesDoNotAutoWeld = refl

sizeExponentHalfReadingRejected :
  SigmaClosureBoundary.radiusNSizePowerHalfReadingValid
    canonicalSigmaClosureBoundary
  ≡ false
sizeExponentHalfReadingRejected = refl
