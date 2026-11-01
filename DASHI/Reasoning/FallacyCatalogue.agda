module DASHI.Reasoning.FallacyCatalogue where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Argument carrier
------------------------------------------------------------------------

record ArgumentObject : Set₁ where
  field
    Premise : Set
    Rule : Set
    Conclusion : Set
    Receipt : Set
    Temporal : Set
    Scope : Set
    Causal : Set
    Modal : Set
    Semantic : Set

    premiseCarrier : List Premise
    ruleOperatorSet : List Rule
    conclusionTarget : Conclusion
    receiptStructure : List Receipt
    temporalOrdering : List Temporal
    scopeProjection : List Scope
    causalTopology : List Causal
    modalQuantifierStructure : List Modal
    semanticValuation : List Semantic

open ArgumentObject public

------------------------------------------------------------------------
-- Typed obstruction sectors
------------------------------------------------------------------------

data FormalFallacy : Set where
  affirmingConsequent : FormalFallacy
  denyingAntecedent : FormalFallacy
  affirmingDisjunct : FormalFallacy
  invalidOperatorTransport : FormalFallacy

data QuantifierFallacy : Set where
  existentialFallacy : QuantifierFallacy
  universalToExistentialWithoutWitness : QuantifierFallacy
  distributionShift : QuantifierFallacy

data ScopeFallacy : Set where
  composition : ScopeFallacy
  division : ScopeFallacy
  falseEquivalence : ScopeFallacy
  fibreSurfaceProjectionError : ScopeFallacy

data CausalFallacy : Set where
  cumHoc : CausalFallacy
  postHoc : CausalFallacy
  reverseCausation : CausalFallacy
  singleCause : CausalFallacy
  adjacencyAsTransport : CausalFallacy

data RelevanceFallacy : Set where
  redHerring : RelevanceFallacy
  adHominem : RelevanceFallacy
  strawMan : RelevanceFallacy
  appealToEmotion : RelevanceFallacy
  whataboutism : RelevanceFallacy
  wrongTargetSurface : RelevanceFallacy

data PremiseReceiptFallacy : Set where
  bareAssertion : PremiseReceiptFallacy
  falseAttribution : PremiseReceiptFallacy
  weakAuthority : PremiseReceiptFallacy
  anecdote : PremiseReceiptFallacy
  cherryPicking : PremiseReceiptFallacy
  noAdmissibleReceiptPath : PremiseReceiptFallacy

data TemporalFallacy : Set where
  chronologyAsNecessity : TemporalFallacy
  retrospectiveDeterminism : TemporalFallacy
  gamblersFallacy : TemporalFallacy

data ModalFallacy : Set where
  possibleThereforeActual : ModalFallacy
  probableThereforeCertain : ModalFallacy
  necessitySufficiencyConfusion : ModalFallacy
  modalScopeFailure : ModalFallacy

data SemanticFallacy : Set where
  equivocation : SemanticFallacy
  motteAndBailey : SemanticFallacy
  semanticDrift : SemanticFallacy
  identityAssumedAcrossContext : SemanticFallacy

data PolarityFallacy : Set where
  unresolvedContradiction : PolarityFallacy
  kettleLogic : PolarityFallacy
  specialPleading : PolarityFallacy
  doubleStandard : PolarityFallacy

data Obstruction : Set where
  ΩF : FormalFallacy → Obstruction
  ΩQ : QuantifierFallacy → Obstruction
  ΩS : ScopeFallacy → Obstruction
  ΩC : CausalFallacy → Obstruction
  ΩR : RelevanceFallacy → Obstruction
  ΩP : PremiseReceiptFallacy → Obstruction
  ΩT : TemporalFallacy → Obstruction
  ΩM : ModalFallacy → Obstruction
  ΩE : SemanticFallacy → Obstruction
  Ω± : PolarityFallacy → Obstruction

record ObstructionManifold : Set where
  field
    formalSector : List FormalFallacy
    quantifierSector : List QuantifierFallacy
    scopeSector : List ScopeFallacy
    causalSector : List CausalFallacy
    relevanceSector : List RelevanceFallacy
    premiseReceiptSector : List PremiseReceiptFallacy
    temporalSector : List TemporalFallacy
    modalSector : List ModalFallacy
    semanticSector : List SemanticFallacy
    polaritySector : List PolarityFallacy

open ObstructionManifold public

emptyObstructionManifold : ObstructionManifold
emptyObstructionManifold =
  record
    { formalSector = []
    ; quantifierSector = []
    ; scopeSector = []
    ; causalSector = []
    ; relevanceSector = []
    ; premiseReceiptSector = []
    ; temporalSector = []
    ; modalSector = []
    ; semanticSector = []
    ; polaritySector = []
    }

------------------------------------------------------------------------
-- Promotion judgement
------------------------------------------------------------------------

data PromotionState : Set where
  Σ-candidate : PromotionState
  Σ-promoted : PromotionState

hasObstruction : ObstructionManifold → Bool
hasObstruction O with formalSector O
... | _ ∷ _ = true
... | [] with quantifierSector O
... | _ ∷ _ = true
... | [] with scopeSector O
... | _ ∷ _ = true
... | [] with causalSector O
... | _ ∷ _ = true
... | [] with relevanceSector O
... | _ ∷ _ = true
... | [] with premiseReceiptSector O
... | _ ∷ _ = true
... | [] with temporalSector O
... | _ ∷ _ = true
... | [] with modalSector O
... | _ ∷ _ = true
... | [] with semanticSector O
... | _ ∷ _ = true
... | [] with polaritySector O
... | _ ∷ _ = true
... | [] = false

promotionState : ObstructionManifold → PromotionState
promotionState O with hasObstruction O
... | true = Σ-candidate
... | false = Σ-promoted

record FallacyJudgement : Set₁ where
  field
    argument : ArgumentObject
    obstruction : ObstructionManifold

  promotedOnlyWhenClear : PromotionState
  promotedOnlyWhenClear = promotionState obstruction

open FallacyJudgement public

record NoPromotionBoundary (J : FallacyJudgement) : Set where
  field
    blocked : promotedOnlyWhenClear J ≡ Σ-candidate
    routeDoesNotProveConclusion : String

open NoPromotionBoundary public

record PromotionCertificate (J : FallacyJudgement) : Set where
  field
    clear : promotedOnlyWhenClear J ≡ Σ-promoted
    noDetectedObstruction : hasObstruction (obstruction J) ≡ false

open PromotionCertificate public

record CompressionReading : Set where
  field
    uncertaintyReduced : Bool
    structurePreserved : Bool
    contradictionExploded : Bool
    hiddenAssumption : Bool
    invalidProjection : Bool
    semanticInstability : Bool
    causalHallucination : Bool
    receiptLoss : Bool

  compressionAdmissible : Bool
  compressionAdmissible with uncertaintyReduced | structurePreserved | contradictionExploded
  ... | true | true | false = true
  ... | _ | _ | _ = false

open CompressionReading public
