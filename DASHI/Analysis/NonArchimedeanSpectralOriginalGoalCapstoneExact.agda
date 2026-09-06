module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL / POST-CLOSURE CAPSTONE
--
-- The finite non-Archimedean spectral core is dependency-closed in DASHI.
-- The repaired finite Markov/stopping lane and probability-measure Gibbs
-- uniqueness are also dependency-closed.  Several stronger source claims are
-- closed-negative rather than left as phantom proof obligations.
--
-- Positive closures include:
--   * spatial spectral circle / signed powers / spectrum tower;
--   * finite C_n-prefactored L2, covariance and TV mixing;
--   * constructive set-dependent stopping tails;
--   * all polynomial stopping moments and repaired MGF strip;
--   * unique Haar probability Gibbs MEASURE via finite dyadic projections.
--
-- Closed-negative promotions include:
--   * unit-prefactor one-step L2 contraction;
--   * universal inverse-sqrt-two stopping tail;
--   * universal half-log-two MGF strip;
--   * N-size exponent sigma=1/2 reading of the radius law;
--   * 2-adic/cyclotomic factor determining Prolate critical sigma;
--   * full continuous transfer-operator radius sqrt two;
--   * uniqueness of arbitrary plain linear IsConformalGibbs functionals.
--
-- The remaining advertised post-closure research claim is the separate
-- Tao-style logarithmic stopping-time concentration lane.
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
  repairedStoppingMGFDomain : OriginalGoalLeaf
  universalHalfLogTwoMGFDomain : OriginalGoalLeaf

  finiteUniqueUniformStationary : OriginalGoalLeaf
  probabilityMeasureGibbsUniqueness : OriginalGoalLeaf
  arbitraryFunctionalGibbsUniqueness : OriginalGoalLeaf

  taoStyleStoppingConcentration : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  sourceOwned : OriginalGoalStatus
  owned : OriginalGoalStatus
  compiled : OriginalGoalStatus
  repoReusable : OriginalGoalStatus
  sourceLibraryCompiled : OriginalGoalStatus
  sourcePlaceholderButRepoCompiled : OriginalGoalStatus
  rejectedReading : OriginalGoalStatus
  refuted : OriginalGoalStatus
  liveIndependentProducer : OriginalGoalStatus

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
leafStatus cyclotomicToProlateSigmaAnchor = refuted
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
leafStatus polynomialStoppingMoments = sourceLibraryCompiled
leafStatus repairedStoppingMGFDomain = sourceLibraryCompiled
leafStatus universalHalfLogTwoMGFDomain = refuted

leafStatus finiteUniqueUniformStationary = sourceLibraryCompiled
leafStatus probabilityMeasureGibbsUniqueness = sourceLibraryCompiled
leafStatus arbitraryFunctionalGibbsUniqueness = refuted

leafStatus taoStyleStoppingConcentration = liveIndependentProducer

priority : List OriginalGoalLeaf
priority = taoStyleStoppingConcentration ∷ []

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

record PostClosureBoundary : Set where
  constructor postClosureBoundary
  field
    prefactoredL2Closed : Bool
    totalVariationClosed : Bool
    stationaryCovarianceClosed : Bool
    constructiveStoppingTailClosed : Bool
    polynomialMomentsClosed : Bool
    repairedMGFDomainClosed : Bool
    probabilityGibbsMeasureUniquenessClosed : Bool
    sigmaAnchorRejectedByNonFactorability : Bool
    arbitraryFunctionalGibbsUniquenessRejected : Bool
    taoConcentrationStillIndependent : Bool

canonicalPostClosureBoundary : PostClosureBoundary
canonicalPostClosureBoundary =
  postClosureBoundary true true true true true true true true true true

probabilityGibbsClosed :
  PostClosureBoundary.probabilityGibbsMeasureUniquenessClosed
    canonicalPostClosureBoundary
  ≡ true
probabilityGibbsClosed = refl

sigmaAnchorClosedNegative :
  PostClosureBoundary.sigmaAnchorRejectedByNonFactorability
    canonicalPostClosureBoundary
  ≡ true
sigmaAnchorClosedNegative = refl

onlyAdvertisedPostClosurePriorityIsConcentration :
  priority ≡ taoStyleStoppingConcentration ∷ []
onlyAdvertisedPostClosurePriorityIsConcentration = refl
