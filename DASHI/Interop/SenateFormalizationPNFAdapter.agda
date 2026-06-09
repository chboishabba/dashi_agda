module DASHI.Interop.SenateFormalizationPNFAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Non-promoting source-unit adapter for the Senate Lean formalization.
--
-- The local paste is a Lean 4 bundle over the CRS Senate reference-source
-- report.  It is recorded here as JMD's Senate formalization, in the same
-- attribution style as the local JMD Moonshine / monster receipt surfaces.
-- Local orientation references are the `monster` submodule pinned from
-- `meta-introspector/monster` and the sibling `../dashi_lean4` Lean4 bridge.
--
-- This module only records how such formal declarations can enter the local
-- PNF/residual carrier as provenance-bearing source-side evidence.  It does
-- not promote any declaration to legal authority, Wikidata authority, or a
-- runtime ITIR parser receipt.

formalizerAttribution : String
formalizerAttribution =
  "JMD Senate formalization"

localMetaIntrospectorReference : String
localMetaIntrospectorReference =
  "monster submodule: meta-introspector/monster"

localLean4Reference : String
localLean4Reference =
  "../dashi_lean4"

data FormalArtifactLanguage : Set where
  lean4 : FormalArtifactLanguage
  agda : FormalArtifactLanguage

data FormalDeclarationKind : Set where
  inductiveDeclaration : FormalDeclarationKind
  structureDeclaration : FormalDeclarationKind
  definitionDeclaration : FormalDeclarationKind
  theoremDeclaration : FormalDeclarationKind
  lemmaDeclaration : FormalDeclarationKind

record FormalizedSourceUnit : Set where
  constructor formalizedSourceUnit
  field
    artifactLanguage : FormalArtifactLanguage
    artifactPath : String
    declarationName : String
    declarationKind : FormalDeclarationKind
    bodyHash : String
    sourceComment : String
    legalAuthorityPromoted : Bool
    liveEditAuthority : Bool

open FormalizedSourceUnit public

sourceUnitIsReviewOnly : FormalizedSourceUnit → Set
sourceUnitIsReviewOnly unit =
  legalAuthorityPromoted unit ≡ false

sourceUnitHasNoLiveEditAuthority : FormalizedSourceUnit → Set
sourceUnitHasNoLiveEditAuthority unit =
  liveEditAuthority unit ≡ false

data SenatePredicateFamily : Set where
  senateProceduralSource : SenatePredicateFamily
  floorEnforceability : SenatePredicateFamily
  rulemakingAuthoritySource : SenatePredicateFamily
  voteThresholdRequired : SenatePredicateFamily
  recognitionPriority : SenatePredicateFamily
  committeeRulePublicationRequirement : SenatePredicateFamily
  precedentWeightOrder : SenatePredicateFamily

predicateKey : SenatePredicateFamily → String
predicateKey senateProceduralSource =
  "senate_procedural_source"
predicateKey floorEnforceability =
  "floor_enforceability"
predicateKey rulemakingAuthoritySource =
  "rulemaking_authority_source"
predicateKey voteThresholdRequired =
  "vote_threshold_required"
predicateKey recognitionPriority =
  "recognition_priority"
predicateKey committeeRulePublicationRequirement =
  "committee_rule_publication_requirement"
predicateKey precedentWeightOrder =
  "precedent_weight_order"

predicateSignature :
  SenatePredicateFamily → Residual.StructuralSignature
predicateSignature voteThresholdRequired =
  Residual.sig-agent-goal
predicateSignature recognitionPriority =
  Residual.sig-agent-goal
predicateSignature _ =
  Residual.sig-agent-theme

predicateTheme : SenatePredicateFamily → Residual.TypedArg
predicateTheme senateProceduralSource =
  Residual.opaqueArg "source-class"
predicateTheme floorEnforceability =
  Residual.opaqueArg "floor-enforceable"
predicateTheme rulemakingAuthoritySource =
  Residual.opaqueArg "constitutional-rulemaking-authority"
predicateTheme voteThresholdRequired =
  Residual.opaqueArg "threshold"
predicateTheme recognitionPriority =
  Residual.opaqueArg "senator-role-priority"
predicateTheme committeeRulePublicationRequirement =
  Residual.opaqueArg "committee-rule-publication"
predicateTheme precedentWeightOrder =
  Residual.opaqueArg "precedent-weight"

sourceUnitToPredicatePNF :
  FormalizedSourceUnit →
  SenatePredicateFamily →
  Residual.PredicatePNF
sourceUnitToPredicatePNF unit family =
  Residual.predicatePNF
    (predicateKey family)
    (predicateSignature family)
    (Residual.opaqueArg (declarationName unit))
    (predicateTheme family)
    Residual.absent
    Residual.positive
    Residual.attributedEvidence
    (sourceComment unit)

------------------------------------------------------------------------
-- Stable local fixture index for representative declarations from the paste.

senatePasteCID : String
senatePasteCID =
  "bafk13b5a0a162737e82e0727da19524aae9"

proceduralSourceUnit : FormalizedSourceUnit
proceduralSourceUnit =
  formalizedSourceUnit
    lean4
    "RequestProject/Basic.lean"
    "ProceduralSource"
    inductiveDeclaration
    "fixture-hash-procedural-source"
    "CRS Senate source taxonomy formalized as a Lean inductive"
    false
    false

sixFloorEnforceableUnit : FormalizedSourceUnit
sixFloorEnforceableUnit =
  formalizedSourceUnit
    lean4
    "RequestProject/Basic.lean"
    "six_floor_enforceable"
    theoremDeclaration
    "fixture-hash-six-floor-enforceable"
    "Lean theorem: six procedural sources are floor enforceable"
    false
    false

rulesClotureHarderUnit : FormalizedSourceUnit
rulesClotureHarderUnit =
  formalizedSourceUnit
    lean4
    "RequestProject/Voting.lean"
    "cloture_on_rules_harder_than_general"
    theoremDeclaration
    "fixture-hash-cloture-on-rules-harder"
    "Lean theorem: cloture on rules has stricter threshold than general cloture"
    false
    false

committeeRecordMandatoryUnit : FormalizedSourceUnit
committeeRecordMandatoryUnit =
  formalizedSourceUnit
    lean4
    "RequestProject/Committees.lean"
    "only_record_mandatory"
    theoremDeclaration
    "fixture-hash-only-record-mandatory"
    "Lean theorem: Congressional Record is the mandatory committee-rules publication venue"
    false
    false

precedentWeightUnit : FormalizedSourceUnit
precedentWeightUnit =
  formalizedSourceUnit
    lean4
    "RequestProject/Basic.lean"
    "precedent_weight_strict_total"
    theoremDeclaration
    "fixture-hash-precedent-weight-strict-total"
    "Lean theorem: precedent origins have strict comparable weight order"
    false
    false

senateFormalizationSourceUnits : List FormalizedSourceUnit
senateFormalizationSourceUnits =
  proceduralSourceUnit
  ∷ sixFloorEnforceableUnit
  ∷ rulesClotureHarderUnit
  ∷ committeeRecordMandatoryUnit
  ∷ precedentWeightUnit
  ∷ []

proceduralSourceReviewOnly :
  sourceUnitIsReviewOnly proceduralSourceUnit
proceduralSourceReviewOnly = refl

proceduralSourceNoLiveEditAuthority :
  sourceUnitHasNoLiveEditAuthority proceduralSourceUnit
proceduralSourceNoLiveEditAuthority = refl

------------------------------------------------------------------------
-- Residual fixtures over the existing SensibLaw carrier.

floorEnforceabilityAtom : Residual.PredicatePNF
floorEnforceabilityAtom =
  sourceUnitToPredicatePNF
    sixFloorEnforceableUnit
    floorEnforceability

floorEnforceabilityReceipt : Residual.PNFEmissionReceipt
floorEnforceabilityReceipt =
  Residual.pnfEmissionReceipt
    "senate-lean-source-unit-fixture"
    "dashi-agda-senate-pnf-adapter"
    "RequestProject/Basic.lean:six_floor_enforceable"
    floorEnforceabilityAtom

directFloorEnforceabilityAtom : Residual.PredicatePNF
directFloorEnforceabilityAtom =
  Residual.predicatePNF
    (predicateKey floorEnforceability)
    (predicateSignature floorEnforceability)
    (Residual.opaqueArg "six_floor_enforceable")
    (predicateTheme floorEnforceability)
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "direct text-side carrier fixture for floor enforceability"

directFloorEnforceabilityReceipt : Residual.PNFEmissionReceipt
directFloorEnforceabilityReceipt =
  Residual.pnfEmissionReceipt
    "senate-text-side-fixture"
    "dashi-agda-senate-pnf-adapter"
    "text-side:floor-enforceability"
    directFloorEnforceabilityAtom

voteThresholdAtom : Residual.PredicatePNF
voteThresholdAtom =
  sourceUnitToPredicatePNF
    rulesClotureHarderUnit
    voteThresholdRequired

voteThresholdReceipt : Residual.PNFEmissionReceipt
voteThresholdReceipt =
  Residual.pnfEmissionReceipt
    "senate-lean-source-unit-fixture"
    "dashi-agda-senate-pnf-adapter"
    "RequestProject/Voting.lean:cloture_on_rules_harder_than_general"
    voteThresholdAtom

negatedFloorEnforceabilityAtom : Residual.PredicatePNF
negatedFloorEnforceabilityAtom =
  Residual.predicatePNF
    (predicateKey floorEnforceability)
    (predicateSignature floorEnforceability)
    (Residual.opaqueArg "six_floor_enforceable")
    (predicateTheme floorEnforceability)
    Residual.absent
    Residual.negated
    Residual.attributedEvidence
    "negative control fixture, not a Senate claim"

negatedFloorEnforceabilityReceipt : Residual.PNFEmissionReceipt
negatedFloorEnforceabilityReceipt =
  Residual.pnfEmissionReceipt
    "senate-negative-control-fixture"
    "dashi-agda-senate-pnf-adapter"
    "negative-control:floor-enforceability"
    negatedFloorEnforceabilityAtom

senateExactResidual :
  Residual.receiptResidual
    floorEnforceabilityReceipt
    floorEnforceabilityReceipt
  ≡
  Residual.exact
senateExactResidual = refl

senatePartialResidual :
  Residual.receiptResidual
    floorEnforceabilityReceipt
    directFloorEnforceabilityReceipt
  ≡
  Residual.partial
senatePartialResidual = refl

senateNoTypedMeetResidual :
  Residual.receiptResidual
    floorEnforceabilityReceipt
    voteThresholdReceipt
  ≡
  Residual.noTypedMeet
senateNoTypedMeetResidual = refl

senateContradictionResidual :
  Residual.receiptResidual
    floorEnforceabilityReceipt
    negatedFloorEnforceabilityReceipt
  ≡
  Residual.contradiction
senateContradictionResidual = refl

record SenateFormalizationPNFAdapterSurface : Set where
  field
    sourceUnits : List FormalizedSourceUnit
    sourceUnitsAreCanonical :
      sourceUnits ≡ senateFormalizationSourceUnits
    carrierMapper :
      FormalizedSourceUnit →
      SenatePredicateFamily →
      Residual.PredicatePNF
    exactFixture :
      Residual.receiptResidual
        floorEnforceabilityReceipt
        floorEnforceabilityReceipt
      ≡
      Residual.exact
    partialFixture :
      Residual.receiptResidual
        floorEnforceabilityReceipt
        directFloorEnforceabilityReceipt
      ≡
      Residual.partial
    noTypedMeetFixture :
      Residual.receiptResidual
        floorEnforceabilityReceipt
        voteThresholdReceipt
      ≡
      Residual.noTypedMeet
    contradictionFixture :
      Residual.receiptResidual
        floorEnforceabilityReceipt
        negatedFloorEnforceabilityReceipt
      ≡
      Residual.contradiction
    legalAuthorityPromotion : Bool
    legalAuthorityPromotionIsFalse :
      legalAuthorityPromotion ≡ false
    wikidataLiveEditAuthority : Bool
    wikidataLiveEditAuthorityIsFalse :
      wikidataLiveEditAuthority ≡ false
    bridgeContract : List String
    formalizerAttributionStatement : String
    localReferenceSurfaces : List String

canonicalSenateFormalizationPNFAdapterSurface :
  SenateFormalizationPNFAdapterSurface
canonicalSenateFormalizationPNFAdapterSurface =
  record
    { sourceUnits =
        senateFormalizationSourceUnits
    ; sourceUnitsAreCanonical =
        refl
    ; carrierMapper =
        sourceUnitToPredicatePNF
    ; exactFixture =
        senateExactResidual
    ; partialFixture =
        senatePartialResidual
    ; noTypedMeetFixture =
        senateNoTypedMeetResidual
    ; contradictionFixture =
        senateContradictionResidual
    ; legalAuthorityPromotion =
        false
    ; legalAuthorityPromotionIsFalse =
        refl
    ; wikidataLiveEditAuthority =
        false
    ; wikidataLiveEditAuthorityIsFalse =
        refl
    ; bridgeContract =
        "Lean declaration maps to a source unit before it maps to PredicatePNF"
        ∷ "PredicatePNF carriers are review evidence, not promoted legal truth"
        ∷ "Residual comparison is bounded to supplied carriers and fixtures"
        ∷ "Wikidata grounding may attach entity navigation only, never predicate authority"
        ∷ []
    ; formalizerAttributionStatement =
        formalizerAttribution
    ; localReferenceSurfaces =
        localMetaIntrospectorReference
        ∷ localLean4Reference
        ∷ []
    }
