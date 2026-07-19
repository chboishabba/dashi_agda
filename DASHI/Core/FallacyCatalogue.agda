module DASHI.Core.FallacyCatalogue where

open import DASHI.Core.ArgumentObstructionCore

------------------------------------------------------------------------
-- Stable constructors for the fallacies enumerated by the source list.
-- Names are identifiers only: detection remains evidence-bearing and
-- context-sensitive through ArgumentObstructionCore.Obstruction.
------------------------------------------------------------------------

data FallacyKind : Set where
  appealToProbability argumentFromFallacy baseRateFallacy conjunctionFallacy maskedManFallacy
  affirmingDisjunct affirmingConsequent denyingAntecedent existentialFallacy
  affirmativeConclusionNegativePremise exclusivePremises fourTerms illicitMajor illicitMinor
  negativeConclusionAffirmativePremises undistributedMiddle politiciansSyllogism modalFallacy modalScopeFallacy
  argumentFromIncredulity argumentToModeration continuumFallacy suppressedCorrelative divineFallacy
  doubleCounting ecologicalFallacy equivocation ambiguousMiddle definitionalRetreat motteAndBailey
  accentFallacy persuasiveDefinition etymologicalFallacy compositionFallacy divisionFallacy
  falseAttribution quotingOutOfContext falseAuthority falseDilemma falseEquivalence feedbackFallacy
  historiansFallacy historicalFallacy baconianFallacy homunculusFallacy inflationOfConflict ifByWhiskey
  incompleteComparison intentionalityFallacy kettleLogic ludicFallacy lumpOfLabour McNamaraFallacy
  mindProjectionFallacy moralisticFallacy movingGoalposts nirvanaFallacy packageDeal proofByAssertion
  prosecutorsFallacy provingTooMuch psychologistsFallacy referentialFallacy reification
  retrospectiveDeterminism slipperySlope specialPleading
  beggingQuestion circularReasoning loadedLabel manyQuestions
  accident noTrueScotsman cherryPicking nutPicking survivorshipBias falseAnalogy hastyGeneralisation
  anecdotalFallacy inductiveFallacy misleadingVividness overwhelmingException exhaustiveEffort
  thoughtTerminatingCliche
  cumHoc postHoc reverseCausation ignoringCommonCause singleCause furtiveFallacy magicalThinking
  observationalInterpretation regressionFallacy gamblersFallacy inverseGamblersFallacy pHacking
  gardenForkingPaths sunkCostFallacy
  appealToStone invincibleIgnorance argumentFromIgnorance argumentFromRepetition argumentFromSilence
  irrelevantConclusion redHerring adHominem circumstantialAdHominem poisoningWell appealToMotive
  tonePolicing traitorousCritic bulverism appealToAuthority appealToAccomplishment courtiersReply
  appealToConsequences appealToEmotion appealToFear appealToFlattery appealToPity appealToRidicule
  appealToSpite judgmentalLanguage poohPooh styleOverSubstance wishfulThinking appealToNature
  appealToNovelty appealToPoverty appealToTradition appealToWealth appealToForce appealToPopularity
  associationFallacy logicChopping ipseDixit chronologicalSnobbery relativePrivation geneticFallacy
  entitledOpinion naturalisticFallacy isOughtFallacy naturalisticFallacyFallacy strawMan
  texasSharpshooter tuQuoque twoWrongs vacuousTruth
  : FallacyKind

primaryAxis : FallacyKind → FallacyAxis
primaryAxis appealToProbability = modal
primaryAxis argumentFromFallacy = formalForm
primaryAxis baseRateFallacy = probabilistic
primaryAxis conjunctionFallacy = probabilistic
primaryAxis maskedManFallacy = semantic
primaryAxis affirmingDisjunct = propositional
primaryAxis affirmingConsequent = propositional
primaryAxis denyingAntecedent = propositional
primaryAxis existentialFallacy = quantification
primaryAxis affirmativeConclusionNegativePremise = syllogistic
primaryAxis exclusivePremises = syllogistic
primaryAxis fourTerms = syllogistic
primaryAxis illicitMajor = syllogistic
primaryAxis illicitMinor = syllogistic
primaryAxis negativeConclusionAffirmativePremises = syllogistic
primaryAxis undistributedMiddle = syllogistic
primaryAxis politiciansSyllogism = relevance
primaryAxis modalFallacy = modal
primaryAxis modalScopeFallacy = modal
primaryAxis argumentFromIncredulity = premiseGrounding
primaryAxis argumentToModeration = comparison
primaryAxis continuumFallacy = classification
primaryAxis suppressedCorrelative = classification
primaryAxis divineFallacy = causal
primaryAxis doubleCounting = resourceAccounting
primaryAxis ecologicalFallacy = scopeProjection
primaryAxis equivocation = semantic
primaryAxis ambiguousMiddle = semantic
primaryAxis definitionalRetreat = semantic
primaryAxis motteAndBailey = semantic
primaryAxis accentFallacy = semantic
primaryAxis persuasiveDefinition = semantic
primaryAxis etymologicalFallacy = semantic
primaryAxis compositionFallacy = scopeProjection
primaryAxis divisionFallacy = scopeProjection
primaryAxis falseAttribution = evidential
primaryAxis quotingOutOfContext = evidential
primaryAxis falseAuthority = authority
primaryAxis falseDilemma = classification
primaryAxis falseEquivalence = comparison
primaryAxis feedbackFallacy = evidential
primaryAxis historiansFallacy = historical
primaryAxis historicalFallacy = causal
primaryAxis baconianFallacy = historical
primaryAxis homunculusFallacy = agency
primaryAxis inflationOfConflict = evidential
primaryAxis ifByWhiskey = semantic
primaryAxis incompleteComparison = comparison
primaryAxis intentionalityFallacy = semantic
primaryAxis kettleLogic = contradiction
primaryAxis ludicFallacy = probabilistic
primaryAxis lumpOfLabour = resourceAccounting
primaryAxis McNamaraFallacy = evidential
primaryAxis mindProjectionFallacy = scopeProjection
primaryAxis moralisticFallacy = normative
primaryAxis movingGoalposts = pragmatic
primaryAxis nirvanaFallacy = optimisation
primaryAxis packageDeal = classification
primaryAxis proofByAssertion = premiseGrounding
primaryAxis prosecutorsFallacy = probabilistic
primaryAxis provingTooMuch = generalisation
primaryAxis psychologistsFallacy = scopeProjection
primaryAxis referentialFallacy = semantic
primaryAxis reification = agency
primaryAxis retrospectiveDeterminism = temporal
primaryAxis slipperySlope = causal
primaryAxis specialPleading = premiseGrounding
primaryAxis beggingQuestion = premiseGrounding
primaryAxis circularReasoning = formalForm
primaryAxis loadedLabel = semantic
primaryAxis manyQuestions = premiseGrounding
primaryAxis accident = generalisation
primaryAxis noTrueScotsman = classification
primaryAxis cherryPicking = evidential
primaryAxis nutPicking = generalisation
primaryAxis survivorshipBias = statistical
primaryAxis falseAnalogy = comparison
primaryAxis hastyGeneralisation = generalisation
primaryAxis anecdotalFallacy = evidential
primaryAxis inductiveFallacy = generalisation
primaryAxis misleadingVividness = emotional
primaryAxis overwhelmingException = generalisation
primaryAxis exhaustiveEffort = optimisation
primaryAxis thoughtTerminatingCliche = pragmatic
primaryAxis cumHoc = causal
primaryAxis postHoc = temporal
primaryAxis reverseCausation = causal
primaryAxis ignoringCommonCause = causal
primaryAxis singleCause = causal
primaryAxis furtiveFallacy = causal
primaryAxis magicalThinking = causal
primaryAxis observationalInterpretation = statistical
primaryAxis regressionFallacy = statistical
primaryAxis gamblersFallacy = probabilistic
primaryAxis inverseGamblersFallacy = probabilistic
primaryAxis pHacking = statistical
primaryAxis gardenForkingPaths = statistical
primaryAxis sunkCostFallacy = optimisation
primaryAxis appealToStone = relevance
primaryAxis invincibleIgnorance = evidential
primaryAxis argumentFromIgnorance = evidential
primaryAxis argumentFromRepetition = premiseGrounding
primaryAxis argumentFromSilence = evidential
primaryAxis irrelevantConclusion = relevance
primaryAxis redHerring = relevanceDiversion
primaryAxis adHominem = relevance
primaryAxis circumstantialAdHominem = relevance
primaryAxis poisoningWell = relevance
primaryAxis appealToMotive = relevance
primaryAxis tonePolicing = relevance
primaryAxis traitorousCritic = relevance
primaryAxis bulverism = relevance
primaryAxis appealToAuthority = authority
primaryAxis appealToAccomplishment = authority
primaryAxis courtiersReply = authority
primaryAxis appealToConsequences = relevance
primaryAxis appealToEmotion = emotional
primaryAxis appealToFear = emotional
primaryAxis appealToFlattery = emotional
primaryAxis appealToPity = emotional
primaryAxis appealToRidicule = emotional
primaryAxis appealToSpite = emotional
primaryAxis judgmentalLanguage = emotional
primaryAxis poohPooh = emotional
primaryAxis styleOverSubstance = emotional
primaryAxis wishfulThinking = emotional
primaryAxis appealToNature = normative
primaryAxis appealToNovelty = temporal
primaryAxis appealToPoverty = relevance
primaryAxis appealToTradition = temporal
primaryAxis appealToWealth = relevance
primaryAxis appealToForce = pragmatic
primaryAxis appealToPopularity = authority
primaryAxis associationFallacy = classification
primaryAxis logicChopping = relevance
primaryAxis ipseDixit = premiseGrounding
primaryAxis chronologicalSnobbery = historical
primaryAxis relativePrivation = relevance
primaryAxis geneticFallacy = historical
primaryAxis entitledOpinion = pragmatic
primaryAxis naturalisticFallacy = normative
primaryAxis isOughtFallacy = normative
primaryAxis naturalisticFallacyFallacy = formalForm
primaryAxis strawMan = relevance
primaryAxis texasSharpshooter = statistical
primaryAxis tuQuoque = relevance
primaryAxis twoWrongs = normative
primaryAxis vacuousTruth = quantification
