module DASHI.Reasoning.FallacyObstructionCatalogue where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- DASHI fallacy typed obstruction catalogue.
--
-- This module is intentionally a catalogue surface, not a proof engine.  It
-- gives an argument object enough typed structure to talk about premises,
-- rules, conclusions, receipts, time, scope, causal claims, modal claims,
-- and semantic tokens; then it names the canonical obstruction sectors that
-- block promotion.

data QuantifierMode : Set where
  universal :
    QuantifierMode

  existential :
    QuantifierMode

  generic :
    QuantifierMode

  witnessBound :
    QuantifierMode

record QuantifierStructure (Statement Witness : Set) : Set where
  field
    quantifiedStatement :
      Statement

    quantifierMode :
      QuantifierMode

    witnesses :
      List Witness

open QuantifierStructure public

data ScopeBoundary : Set where
  localScope :
    ScopeBoundary

  globalScope :
    ScopeBoundary

  receiptScope :
    ScopeBoundary

  externalScope :
    ScopeBoundary

record ScopeStructure (ScopeToken : Set) : Set where
  field
    declaredScope :
      ScopeToken

    permittedBoundaries :
      List ScopeBoundary

    exportedBoundaries :
      List ScopeBoundary

open ScopeStructure public

data CausalDirection : Set where
  causeToEffect :
    CausalDirection

  effectToCause :
    CausalDirection

  commonCause :
    CausalDirection

  correlationOnly :
    CausalDirection

record CausalLink (Statement CauseToken : Set) : Set where
  field
    cause :
      Statement

    effect :
      Statement

    causeToken :
      CauseToken

    causalDirection :
      CausalDirection

open CausalLink public

record CausalStructure (Statement CauseToken : Set) : Set where
  field
    causalLinks :
      List (CausalLink Statement CauseToken)

    causalBoundary :
      List String

open CausalStructure public

data ModalForce : Set where
  necessary :
    ModalForce

  possible :
    ModalForce

  contingent :
    ModalForce

  impossible :
    ModalForce

record ModalClaim (Statement ModalityToken : Set) : Set where
  field
    modalStatement :
      Statement

    modalityToken :
      ModalityToken

    modalForce :
      ModalForce

open ModalClaim public

record ModalStructure (Statement ModalityToken : Set) : Set where
  field
    modalClaims :
      List (ModalClaim Statement ModalityToken)

    modalBoundary :
      List String

open ModalStructure public

data SemanticRole : Set where
  termDefinition :
    SemanticRole

  termUse :
    SemanticRole

  analogyUse :
    SemanticRole

  equivocationRisk :
    SemanticRole

record SemanticTokenUse (SemanticToken : Set) : Set where
  field
    semanticToken :
      SemanticToken

    semanticRole :
      SemanticRole

open SemanticTokenUse public

record SemanticStructure (SemanticToken : Set) : Set where
  field
    semanticTokenUses :
      List (SemanticTokenUse SemanticToken)

    semanticBoundary :
      List String

open SemanticStructure public

record ArgumentObject : Setω where
  field
    Statement :
      Set

    Rule :
      Set

    Receipt :
      Set

    TimeToken :
      Set

    ScopeToken :
      Set

    CauseToken :
      Set

    ModalityToken :
      Set

    SemanticToken :
      Set

    Witness :
      Set

    premises :
      List Statement

    rules :
      List Rule

    conclusion :
      Statement

    receipt :
      Receipt

    time :
      TimeToken

    scope :
      ScopeStructure ScopeToken

    quantifier :
      QuantifierStructure Statement Witness

    causal :
      CausalStructure Statement CauseToken

    modal :
      ModalStructure Statement ModalityToken

    semantic :
      SemanticStructure SemanticToken

    argumentBoundary :
      List String

open ArgumentObject public

data ObstructionSector : Set where
  formalSector :
    ObstructionSector

  quantifierSector :
    ObstructionSector

  scopeSector :
    ObstructionSector

  causalitySector :
    ObstructionSector

  relevanceSector :
    ObstructionSector

  premiseReceiptSector :
    ObstructionSector

  temporalSector :
    ObstructionSector

  modalSector :
    ObstructionSector

  semanticEquivocationSector :
    ObstructionSector

  polarityContradictionSector :
    ObstructionSector

  noPromotionSector :
    ObstructionSector

canonicalObstructionSectors :
  List ObstructionSector
canonicalObstructionSectors =
  formalSector
  ∷ quantifierSector
  ∷ scopeSector
  ∷ causalitySector
  ∷ relevanceSector
  ∷ premiseReceiptSector
  ∷ temporalSector
  ∷ modalSector
  ∷ semanticEquivocationSector
  ∷ polarityContradictionSector
  ∷ noPromotionSector
  ∷ []

data FallacyObstruction : Set where
  invalidRuleApplication :
    FallacyObstruction

  conclusionNotDerivedFromRules :
    FallacyObstruction

  universalFromExistentialWitness :
    FallacyObstruction

  existentialWitnessDropped :
    FallacyObstruction

  localToGlobalScopeLeak :
    FallacyObstruction

  externalReceiptScopeImportedAsInternal :
    FallacyObstruction

  correlationPromotedToCause :
    FallacyObstruction

  causalDirectionReversed :
    FallacyObstruction

  irrelevantPremiseSupport :
    FallacyObstruction

  missingPremiseSupport :
    FallacyObstruction

  missingReceipt :
    FallacyObstruction

  receiptDoesNotBindConclusion :
    FallacyObstruction

  temporalOrderViolation :
    FallacyObstruction

  staleReceiptUsedAsCurrent :
    FallacyObstruction

  possiblePromotedToNecessary :
    FallacyObstruction

  modalContextCollapsed :
    FallacyObstruction

  semanticEquivocation :
    FallacyObstruction

  analogyPromotedToDefinition :
    FallacyObstruction

  polarityFlip :
    FallacyObstruction

  explicitContradiction :
    FallacyObstruction

  promotionWithoutDischarge :
    FallacyObstruction

sectorOf :
  FallacyObstruction →
  ObstructionSector
sectorOf invalidRuleApplication =
  formalSector
sectorOf conclusionNotDerivedFromRules =
  formalSector
sectorOf universalFromExistentialWitness =
  quantifierSector
sectorOf existentialWitnessDropped =
  quantifierSector
sectorOf localToGlobalScopeLeak =
  scopeSector
sectorOf externalReceiptScopeImportedAsInternal =
  scopeSector
sectorOf correlationPromotedToCause =
  causalitySector
sectorOf causalDirectionReversed =
  causalitySector
sectorOf irrelevantPremiseSupport =
  relevanceSector
sectorOf missingPremiseSupport =
  premiseReceiptSector
sectorOf missingReceipt =
  premiseReceiptSector
sectorOf receiptDoesNotBindConclusion =
  premiseReceiptSector
sectorOf temporalOrderViolation =
  temporalSector
sectorOf staleReceiptUsedAsCurrent =
  temporalSector
sectorOf possiblePromotedToNecessary =
  modalSector
sectorOf modalContextCollapsed =
  modalSector
sectorOf semanticEquivocation =
  semanticEquivocationSector
sectorOf analogyPromotedToDefinition =
  semanticEquivocationSector
sectorOf polarityFlip =
  polarityContradictionSector
sectorOf explicitContradiction =
  polarityContradictionSector
sectorOf promotionWithoutDischarge =
  noPromotionSector

canonicalFallacyObstructions :
  List FallacyObstruction
canonicalFallacyObstructions =
  invalidRuleApplication
  ∷ conclusionNotDerivedFromRules
  ∷ universalFromExistentialWitness
  ∷ existentialWitnessDropped
  ∷ localToGlobalScopeLeak
  ∷ externalReceiptScopeImportedAsInternal
  ∷ correlationPromotedToCause
  ∷ causalDirectionReversed
  ∷ irrelevantPremiseSupport
  ∷ missingPremiseSupport
  ∷ missingReceipt
  ∷ receiptDoesNotBindConclusion
  ∷ temporalOrderViolation
  ∷ staleReceiptUsedAsCurrent
  ∷ possiblePromotedToNecessary
  ∷ modalContextCollapsed
  ∷ semanticEquivocation
  ∷ analogyPromotedToDefinition
  ∷ polarityFlip
  ∷ explicitContradiction
  ∷ promotionWithoutDischarge
  ∷ []

data Polarity : Set where
  positive :
    Polarity

  negative :
    Polarity

  neutral :
    Polarity

record PolarizedStatement (Statement : Set) : Set where
  field
    polarizedStatement :
      Statement

    polarity :
      Polarity

open PolarizedStatement public

record ContradictionPair (Statement : Set) : Set where
  field
    positiveSide :
      PolarizedStatement Statement

    negativeSide :
      PolarizedStatement Statement

    positiveSideIsPositive :
      polarity positiveSide ≡ positive

    negativeSideIsNegative :
      polarity negativeSide ≡ negative

    contradictionBoundary :
      List String

open ContradictionPair public

FallacyPromotionEligible :
  FallacyObstruction →
  Set
FallacyPromotionEligible _ =
  ⊥

noFallacyPromotion :
  (obstruction : FallacyObstruction) →
  FallacyPromotionEligible obstruction →
  ⊥
noFallacyPromotion _ impossible =
  impossible

data FallacyCatalogueStatus : Set where
  typedObstructionCatalogueOnlyNoPromotion :
    FallacyCatalogueStatus

record FallacyObstructionReceipt : Setω where
  field
    argument :
      ArgumentObject

    obstruction :
      FallacyObstruction

    obstructionSector :
      ObstructionSector

    obstructionSector-v :
      obstructionSector ≡ sectorOf obstruction

    status :
      FallacyCatalogueStatus

    status-v :
      status ≡ typedObstructionCatalogueOnlyNoPromotion

    promotesConclusion :
      Bool

    promotesConclusionIsFalse :
      promotesConclusion ≡ false

    noPromotionBoundary :
      List String

open FallacyObstructionReceipt public

data CanonicalAtom : Set where
  premiseAtom :
    CanonicalAtom

  conclusionAtom :
    CanonicalAtom

  causeAtom :
    CanonicalAtom

data CanonicalRule : Set where
  canonicalInferenceRule :
    CanonicalRule

data CanonicalReceipt : Set where
  canonicalReceipt :
    CanonicalReceipt

data CanonicalTime : Set where
  canonicalTime :
    CanonicalTime

data CanonicalScopeToken : Set where
  canonicalScopeToken :
    CanonicalScopeToken

data CanonicalCauseToken : Set where
  canonicalCauseToken :
    CanonicalCauseToken

data CanonicalModalityToken : Set where
  canonicalModalityToken :
    CanonicalModalityToken

data CanonicalSemanticToken : Set where
  canonicalSemanticToken :
    CanonicalSemanticToken

data CanonicalWitness : Set where
  canonicalWitness :
    CanonicalWitness

canonicalScopeStructure :
  ScopeStructure CanonicalScopeToken
canonicalScopeStructure =
  record
    { declaredScope =
        canonicalScopeToken
    ; permittedBoundaries =
        localScope ∷ receiptScope ∷ []
    ; exportedBoundaries =
        localScope ∷ []
    }

canonicalQuantifierStructure :
  QuantifierStructure CanonicalAtom CanonicalWitness
canonicalQuantifierStructure =
  record
    { quantifiedStatement =
        premiseAtom
    ; quantifierMode =
        witnessBound
    ; witnesses =
        canonicalWitness ∷ []
    }

canonicalCausalLink :
  CausalLink CanonicalAtom CanonicalCauseToken
canonicalCausalLink =
  record
    { cause =
        causeAtom
    ; effect =
        conclusionAtom
    ; causeToken =
        canonicalCauseToken
    ; causalDirection =
        causeToEffect
    }

canonicalCausalStructure :
  CausalStructure CanonicalAtom CanonicalCauseToken
canonicalCausalStructure =
  record
    { causalLinks =
        canonicalCausalLink ∷ []
    ; causalBoundary =
        "causal claims remain typed support, not promotion authority"
        ∷ []
    }

canonicalModalClaim :
  ModalClaim CanonicalAtom CanonicalModalityToken
canonicalModalClaim =
  record
    { modalStatement =
        conclusionAtom
    ; modalityToken =
        canonicalModalityToken
    ; modalForce =
        possible
    }

canonicalModalStructure :
  ModalStructure CanonicalAtom CanonicalModalityToken
canonicalModalStructure =
  record
    { modalClaims =
        canonicalModalClaim ∷ []
    ; modalBoundary =
        "possible claims do not promote to necessary claims"
        ∷ []
    }

canonicalSemanticTokenUse :
  SemanticTokenUse CanonicalSemanticToken
canonicalSemanticTokenUse =
  record
    { semanticToken =
        canonicalSemanticToken
    ; semanticRole =
        termUse
    }

canonicalSemanticStructure :
  SemanticStructure CanonicalSemanticToken
canonicalSemanticStructure =
  record
    { semanticTokenUses =
        canonicalSemanticTokenUse ∷ []
    ; semanticBoundary =
        "term use remains distinct from definition and analogy"
        ∷ []
    }

canonicalArgumentObject :
  ArgumentObject
canonicalArgumentObject =
  record
    { Statement =
        CanonicalAtom
    ; Rule =
        CanonicalRule
    ; Receipt =
        CanonicalReceipt
    ; TimeToken =
        CanonicalTime
    ; ScopeToken =
        CanonicalScopeToken
    ; CauseToken =
        CanonicalCauseToken
    ; ModalityToken =
        CanonicalModalityToken
    ; SemanticToken =
        CanonicalSemanticToken
    ; Witness =
        CanonicalWitness
    ; premises =
        premiseAtom ∷ []
    ; rules =
        canonicalInferenceRule ∷ []
    ; conclusion =
        conclusionAtom
    ; receipt =
        canonicalReceipt
    ; time =
        canonicalTime
    ; scope =
        canonicalScopeStructure
    ; quantifier =
        canonicalQuantifierStructure
    ; causal =
        canonicalCausalStructure
    ; modal =
        canonicalModalStructure
    ; semantic =
        canonicalSemanticStructure
    ; argumentBoundary =
        "argument object records structure only"
        ∷ "fallacy obstruction receipts do not certify the conclusion"
        ∷ []
    }

canonicalContradictionPair :
  ContradictionPair CanonicalAtom
canonicalContradictionPair =
  record
    { positiveSide =
        record
          { polarizedStatement =
              conclusionAtom
          ; polarity =
              positive
          }
    ; negativeSide =
        record
          { polarizedStatement =
              conclusionAtom
          ; polarity =
              negative
          }
    ; positiveSideIsPositive =
        refl
    ; negativeSideIsNegative =
        refl
    ; contradictionBoundary =
        "same conclusion token is present under positive and negative polarity"
        ∷ []
    }

canonicalSemanticEquivocationReceipt :
  FallacyObstructionReceipt
canonicalSemanticEquivocationReceipt =
  record
    { argument =
        canonicalArgumentObject
    ; obstruction =
        semanticEquivocation
    ; obstructionSector =
        semanticEquivocationSector
    ; obstructionSector-v =
        refl
    ; status =
        typedObstructionCatalogueOnlyNoPromotion
    ; status-v =
        refl
    ; promotesConclusion =
        false
    ; promotesConclusionIsFalse =
        refl
    ; noPromotionBoundary =
        "semantic-equivalence or equivocation detection is a typed obstruction"
        ∷ "no theorem, external authority, or conclusion promotion is constructed"
        ∷ []
    }

canonicalNoPromotionReceipt :
  FallacyObstructionReceipt
canonicalNoPromotionReceipt =
  record
    { argument =
        canonicalArgumentObject
    ; obstruction =
        promotionWithoutDischarge
    ; obstructionSector =
        noPromotionSector
    ; obstructionSector-v =
        refl
    ; status =
        typedObstructionCatalogueOnlyNoPromotion
    ; status-v =
        refl
    ; promotesConclusion =
        false
    ; promotesConclusionIsFalse =
        refl
    ; noPromotionBoundary =
        "promotion requires discharged formal, receipt, temporal, modal, semantic, and scope obligations"
        ∷ "this catalogue only names blockers and canonical receipt shapes"
        ∷ []
    }

canonicalCatalogueClosedUnderNamedSectors :
  canonicalObstructionSectors
  ≡
  formalSector
  ∷ quantifierSector
  ∷ scopeSector
  ∷ causalitySector
  ∷ relevanceSector
  ∷ premiseReceiptSector
  ∷ temporalSector
  ∷ modalSector
  ∷ semanticEquivocationSector
  ∷ polarityContradictionSector
  ∷ noPromotionSector
  ∷ []
canonicalCatalogueClosedUnderNamedSectors =
  refl

canonicalCatalogueStatus :
  FallacyCatalogueStatus
canonicalCatalogueStatus =
  typedObstructionCatalogueOnlyNoPromotion

canonicalCatalogueStatus-v :
  canonicalCatalogueStatus
  ≡
  typedObstructionCatalogueOnlyNoPromotion
canonicalCatalogueStatus-v =
  refl

