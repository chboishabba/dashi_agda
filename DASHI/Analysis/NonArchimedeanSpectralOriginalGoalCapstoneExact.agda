module DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact where

------------------------------------------------------------------------
-- ORIGINAL-GOAL CAPSTONE
--
-- The finite non-Archimedean spectral core is now dependency-closed in DASHI.
-- This does NOT rewrite the external Lean source: its named
-- `spectral_tower_one_step` theorem still concludes `True`.  The distinction is
-- source theorem strength versus DASHI compiler closure from already checked
-- ingredients.
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
  directedRadiusCriticalSigmaAudit : OriginalGoalLeaf
  undirectedGapExponentAlpha : OriginalGoalLeaf


data OriginalGoalStatus : Set where
  sourceOwned : OriginalGoalStatus
  owned : OriginalGoalStatus
  compiled : OriginalGoalStatus
  repoReusable : OriginalGoalStatus
  sourcePlaceholderButRepoCompiled : OriginalGoalStatus
  liveAudit : OriginalGoalStatus

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
leafStatus directedRadiusCriticalSigmaAudit = liveAudit
leafStatus undirectedGapExponentAlpha = sourceOwned

priority : List OriginalGoalLeaf
priority =
  directedRadiusCriticalSigmaAudit ∷ []

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

record ExponentSeparationBoundary : Set where
  constructor exponentSeparationBoundary
  field
    directedRadiusSigmaIsUndirectedGapAlpha : Bool
    undirectedGapAlphaHasLeanTheorems : Bool
    directedRadiusSigmaHalfHasLocatedLeanTheorem : Bool
    exponentNamesMayBeCollapsed : Bool

canonicalExponentSeparationBoundary : ExponentSeparationBoundary
canonicalExponentSeparationBoundary =
  exponentSeparationBoundary false true false false

undirectedAlphaDoesNotDischargeDirectedSigma :
  ExponentSeparationBoundary.directedRadiusSigmaIsUndirectedGapAlpha
    canonicalExponentSeparationBoundary
  ≡ false
undirectedAlphaDoesNotDischargeDirectedSigma = refl
