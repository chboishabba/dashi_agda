module DASHI.Reasoning.FallacyExamples where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Reasoning.FallacyCatalogue

------------------------------------------------------------------------
-- A small concrete argument carrier for examples
------------------------------------------------------------------------

data ExampleToken : Set where
  premiseA : ExampleToken
  premiseB : ExampleToken
  ruleImplies : ExampleToken
  ruleOr : ExampleToken
  conclusionA : ExampleToken
  conclusionB : ExampleToken
  receiptA : ExampleToken
  timeBefore : ExampleToken
  localFibre : ExampleToken
  globalSurface : ExampleToken
  causalEdge : ExampleToken
  modalPossible : ExampleToken
  semanticSurface : ExampleToken

exampleArgument : ArgumentObject
exampleArgument =
  record
    { Premise = ExampleToken
    ; Rule = ExampleToken
    ; Conclusion = ExampleToken
    ; Receipt = ExampleToken
    ; Temporal = ExampleToken
    ; Scope = ExampleToken
    ; Causal = ExampleToken
    ; Modal = ExampleToken
    ; Semantic = ExampleToken
    ; premiseCarrier = premiseA ∷ premiseB ∷ []
    ; ruleOperatorSet = ruleImplies ∷ ruleOr ∷ []
    ; conclusionTarget = conclusionA
    ; receiptStructure = receiptA ∷ []
    ; temporalOrdering = timeBefore ∷ []
    ; scopeProjection = localFibre ∷ globalSurface ∷ []
    ; causalTopology = causalEdge ∷ []
    ; modalQuantifierStructure = modalPossible ∷ []
    ; semanticValuation = semanticSurface ∷ []
    }

judgementFor : ObstructionManifold → FallacyJudgement
judgementFor O =
  record
    { argument = exampleArgument
    ; obstruction = O
    }

boundaryFor :
  (O : ObstructionManifold) →
  promotionState O ≡ Σ-candidate →
  String →
  NoPromotionBoundary (judgementFor O)
boundaryFor O blocked reason =
  record
    { blocked = blocked
    ; routeDoesNotProveConclusion = reason
    }

------------------------------------------------------------------------
-- Formal obstruction examples
------------------------------------------------------------------------

affirmingConsequentObstruction : ObstructionManifold
affirmingConsequentObstruction =
  record emptyObstructionManifold
    { formalSector = affirmingConsequent ∷ [] }

affirmingConsequentCandidate :
  promotionState affirmingConsequentObstruction ≡ Σ-candidate
affirmingConsequentCandidate = refl

denyingAntecedentObstruction : ObstructionManifold
denyingAntecedentObstruction =
  record emptyObstructionManifold
    { formalSector = denyingAntecedent ∷ [] }

denyingAntecedentCandidate :
  promotionState denyingAntecedentObstruction ≡ Σ-candidate
denyingAntecedentCandidate = refl

affirmingDisjunctObstruction : ObstructionManifold
affirmingDisjunctObstruction =
  record emptyObstructionManifold
    { formalSector = affirmingDisjunct ∷ [] }

------------------------------------------------------------------------
-- Quantifier obstruction examples
------------------------------------------------------------------------

existentialFallacyObstruction : ObstructionManifold
existentialFallacyObstruction =
  record emptyObstructionManifold
    { quantifierSector =
        existentialFallacy ∷ universalToExistentialWithoutWitness ∷ []
    }

existentialFallacyCandidate :
  promotionState existentialFallacyObstruction ≡ Σ-candidate
existentialFallacyCandidate = refl

------------------------------------------------------------------------
-- Scope/projection obstruction examples
------------------------------------------------------------------------

scopeObstruction : ObstructionManifold
scopeObstruction =
  record emptyObstructionManifold
    { scopeSector =
        composition ∷ division ∷ falseEquivalence ∷ []
    }

scopeObstructionCandidate : promotionState scopeObstruction ≡ Σ-candidate
scopeObstructionCandidate = refl

------------------------------------------------------------------------
-- Causal obstruction examples
------------------------------------------------------------------------

causalObstruction : ObstructionManifold
causalObstruction =
  record emptyObstructionManifold
    { causalSector =
        cumHoc ∷ postHoc ∷ reverseCausation ∷ singleCause ∷ []
    }

causalObstructionCandidate : promotionState causalObstruction ≡ Σ-candidate
causalObstructionCandidate = refl

------------------------------------------------------------------------
-- Relevance obstruction examples
------------------------------------------------------------------------

relevanceObstruction : ObstructionManifold
relevanceObstruction =
  record emptyObstructionManifold
    { relevanceSector =
        redHerring ∷ adHominem ∷ strawMan ∷ whataboutism ∷ []
    }

relevanceObstructionCandidate : promotionState relevanceObstruction ≡ Σ-candidate
relevanceObstructionCandidate = refl

------------------------------------------------------------------------
-- Premise / receipt obstruction examples
------------------------------------------------------------------------

receiptObstruction : ObstructionManifold
receiptObstruction =
  record emptyObstructionManifold
    { premiseReceiptSector =
        bareAssertion
        ∷ falseAttribution
        ∷ weakAuthority
        ∷ anecdote
        ∷ cherryPicking
        ∷ noAdmissibleReceiptPath
        ∷ []
    }

receiptObstructionCandidate : promotionState receiptObstruction ≡ Σ-candidate
receiptObstructionCandidate = refl

------------------------------------------------------------------------
-- Temporal obstruction examples
------------------------------------------------------------------------

temporalObstruction : ObstructionManifold
temporalObstruction =
  record emptyObstructionManifold
    { temporalSector =
        chronologyAsNecessity ∷ retrospectiveDeterminism ∷ gamblersFallacy ∷ []
    }

temporalObstructionCandidate : promotionState temporalObstruction ≡ Σ-candidate
temporalObstructionCandidate = refl

------------------------------------------------------------------------
-- Modal obstruction examples
------------------------------------------------------------------------

modalObstruction : ObstructionManifold
modalObstruction =
  record emptyObstructionManifold
    { modalSector =
        possibleThereforeActual
        ∷ probableThereforeCertain
        ∷ necessitySufficiencyConfusion
        ∷ modalScopeFailure
        ∷ []
    }

modalObstructionCandidate : promotionState modalObstruction ≡ Σ-candidate
modalObstructionCandidate = refl

------------------------------------------------------------------------
-- Semantic/equivocation obstruction examples
------------------------------------------------------------------------

semanticObstruction : ObstructionManifold
semanticObstruction =
  record emptyObstructionManifold
    { semanticSector =
        equivocation ∷ motteAndBailey ∷ semanticDrift ∷ []
    }

semanticObstructionCandidate : promotionState semanticObstruction ≡ Σ-candidate
semanticObstructionCandidate = refl

------------------------------------------------------------------------
-- Polarity / contradiction obstruction examples
------------------------------------------------------------------------

polarityObstruction : ObstructionManifold
polarityObstruction =
  record emptyObstructionManifold
    { polaritySector =
        unresolvedContradiction ∷ kettleLogic ∷ specialPleading ∷ doubleStandard ∷ []
    }

polarityObstructionCandidate : promotionState polarityObstruction ≡ Σ-candidate
polarityObstructionCandidate = refl

------------------------------------------------------------------------
-- Global catalogue and clear route witness
------------------------------------------------------------------------

fullFallacySpaceObstruction : ObstructionManifold
fullFallacySpaceObstruction =
  record
    { formalSector =
        affirmingConsequent ∷ denyingAntecedent ∷ affirmingDisjunct ∷ []
    ; quantifierSector =
        existentialFallacy ∷ universalToExistentialWithoutWitness ∷ []
    ; scopeSector =
        composition ∷ division ∷ falseEquivalence ∷ []
    ; causalSector =
        cumHoc ∷ postHoc ∷ reverseCausation ∷ singleCause ∷ []
    ; relevanceSector =
        redHerring ∷ adHominem ∷ strawMan ∷ whataboutism ∷ []
    ; premiseReceiptSector =
        bareAssertion ∷ weakAuthority ∷ cherryPicking ∷ noAdmissibleReceiptPath ∷ []
    ; temporalSector =
        retrospectiveDeterminism ∷ gamblersFallacy ∷ []
    ; modalSector =
        possibleThereforeActual ∷ modalScopeFailure ∷ []
    ; semanticSector =
        equivocation ∷ motteAndBailey ∷ identityAssumedAcrossContext ∷ []
    ; polaritySector =
        unresolvedContradiction ∷ kettleLogic ∷ doubleStandard ∷ []
    }

fullFallacySpaceCandidate :
  promotionState fullFallacySpaceObstruction ≡ Σ-candidate
fullFallacySpaceCandidate = refl

fullFallacySpaceBoundary :
  NoPromotionBoundary (judgementFor fullFallacySpaceObstruction)
fullFallacySpaceBoundary =
  boundaryFor
    fullFallacySpaceObstruction
    fullFallacySpaceCandidate
    "Detected fallacy obstruction: this route does not prove the conclusion."

clearArgumentJudgement : FallacyJudgement
clearArgumentJudgement = judgementFor emptyObstructionManifold

clearArgumentPromoted :
  promotedOnlyWhenClear clearArgumentJudgement ≡ Σ-promoted
clearArgumentPromoted = refl

clearArgumentCertificate : PromotionCertificate clearArgumentJudgement
clearArgumentCertificate =
  record
    { clear = refl
    ; noDetectedObstruction = refl
    }

fallaciousCompressionReading : CompressionReading
fallaciousCompressionReading =
  record
    { uncertaintyReduced = false
    ; structurePreserved = false
    ; contradictionExploded = true
    ; hiddenAssumption = true
    ; invalidProjection = true
    ; semanticInstability = true
    ; causalHallucination = true
    ; receiptLoss = true
    }

fallaciousCompressionBlocked :
  compressionAdmissible fallaciousCompressionReading ≡ false
fallaciousCompressionBlocked = refl
