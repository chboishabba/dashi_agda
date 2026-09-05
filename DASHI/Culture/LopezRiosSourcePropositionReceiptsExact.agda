module DASHI.Culture.LopezRiosSourcePropositionReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.LopezRiosMarxistPsychologySourceAtlasExact as Atlas

------------------------------------------------------------------------
-- LOPEZ-RIOS PROPOSITION-LEVEL SOURCE RECEIPTS
--
-- This owner refines the article-level atlas into bounded proposition IDs.
-- It does not claim sentence/page precision beyond what has been source-
-- recovered in the atlas.  Each receipt points back to the article owner and
-- states only the bounded proposition role used by downstream DASHI modules.
--
-- Crucially:
--   SourceProposition != DASHIInterpretation != DASHITheorem.
------------------------------------------------------------------------

data LopezRiosPropositionId : Set where
  LR22AntiDialecticalIdealist
  LR22ApoliticalCharacter
  LR22Servility
  LR22PsychologisingMystification
  LR22CapitalistOverdetermination
  LR22LacanianPsychoanalysisRole
  LR25StructuralCausality
  LR25NeoliberalisationOfPsychology
  LR25Psychologisation
  LR25DepoliticisationPrivatisationOfDistress
  : LopezRiosPropositionId

data ReceiptKind : Set where
  boundedSourceProposition
  dashiInterpretiveBridge
  dashiFiniteTheorem
  empiricalPopulationClaim
  : ReceiptKind

record SourcePropositionReceipt : Set where
  constructor source-proposition-receipt
  field
    propositionId : LopezRiosPropositionId
    source : Source.AttributedSource
    boundedClaim : String
    sourceRoleOnly : Bool
    receiptKind : ReceiptKind

open SourcePropositionReceipt public

lr22AntiDialecticalIdealist : SourcePropositionReceipt
lr22AntiDialecticalIdealist =
  source-proposition-receipt
    LR22AntiDialecticalIdealist
    Atlas.fourContradictionsSource
    "psychology is criticised in the named contradiction as anti-dialectical / idealist"
    true
    boundedSourceProposition

lr22ApoliticalCharacter : SourcePropositionReceipt
lr22ApoliticalCharacter =
  source-proposition-receipt
    LR22ApoliticalCharacter
    Atlas.fourContradictionsSource
    "psychology is criticised in the named contradiction for an apolitical character"
    true
    boundedSourceProposition

lr22Servility : SourcePropositionReceipt
lr22Servility =
  source-proposition-receipt
    LR22Servility
    Atlas.fourContradictionsSource
    "psychology is criticised in the named contradiction for servility to existing social relations"
    true
    boundedSourceProposition

lr22PsychologisingMystification : SourcePropositionReceipt
lr22PsychologisingMystification =
  source-proposition-receipt
    LR22PsychologisingMystification
    Atlas.fourContradictionsSource
    "psychologisation is presented as a mystifying contradiction between Marxism and psychology"
    true
    boundedSourceProposition

lr22CapitalistOverdetermination : SourcePropositionReceipt
lr22CapitalistOverdetermination =
  source-proposition-receipt
    LR22CapitalistOverdetermination
    Atlas.fourContradictionsSource
    "the psychology field is discussed as overdetermined under capitalism"
    true
    boundedSourceProposition

lr22LacanianPsychoanalysisRole : SourcePropositionReceipt
lr22LacanianPsychoanalysisRole =
  source-proposition-receipt
    LR22LacanianPsychoanalysisRole
    Atlas.fourContradictionsSource
    "Lacanian psychoanalysis is assigned a stated theoretical role in the critique"
    true
    boundedSourceProposition

lr25StructuralCausality : SourcePropositionReceipt
lr25StructuralCausality =
  source-proposition-receipt
    LR25StructuralCausality
    Atlas.positivePsychologySource
    "structural causality is used in the later critique of neoliberalised psychology"
    true
    boundedSourceProposition

lr25NeoliberalisationOfPsychology : SourcePropositionReceipt
lr25NeoliberalisationOfPsychology =
  source-proposition-receipt
    LR25NeoliberalisationOfPsychology
    Atlas.positivePsychologySource
    "positive psychology is analysed within a neoliberalisation-of-psychology critique"
    true
    boundedSourceProposition

lr25Psychologisation : SourcePropositionReceipt
lr25Psychologisation =
  source-proposition-receipt
    LR25Psychologisation
    Atlas.positivePsychologySource
    "psychologisation is identified among the effects analysed in the neoliberalised-psychology critique"
    true
    boundedSourceProposition

lr25DepoliticisationPrivatisationOfDistress : SourcePropositionReceipt
lr25DepoliticisationPrivatisationOfDistress =
  source-proposition-receipt
    LR25DepoliticisationPrivatisationOfDistress
    Atlas.positivePsychologySource
    "depoliticisation and privatisation of distress are identified among the effects analysed"
    true
    boundedSourceProposition

lopezRiosPropositionReceipts : List SourcePropositionReceipt
lopezRiosPropositionReceipts =
  lr22AntiDialecticalIdealist ∷
  lr22ApoliticalCharacter ∷
  lr22Servility ∷
  lr22PsychologisingMystification ∷
  lr22CapitalistOverdetermination ∷
  lr22LacanianPsychoanalysisRole ∷
  lr25StructuralCausality ∷
  lr25NeoliberalisationOfPsychology ∷
  lr25Psychologisation ∷
  lr25DepoliticisationPrivatisationOfDistress ∷
  []

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data SourceReceiptIsDASHITheorem : Set where
data SourceReceiptIsEmpiricalPopulationLaw : Set where
data FormalSimilarityTransfersHistoricalAuthorship : Set where

sourceReceiptDoesNotBecomeDASHITheorem : SourceReceiptIsDASHITheorem → ⊥
sourceReceiptDoesNotBecomeDASHITheorem ()

sourceReceiptDoesNotBecomePopulationLaw : SourceReceiptIsEmpiricalPopulationLaw → ⊥
sourceReceiptDoesNotBecomePopulationLaw ()

formalSimilarityDoesNotTransferAuthorship :
  FormalSimilarityTransfersHistoricalAuthorship → ⊥
formalSimilarityDoesNotTransferAuthorship ()

record LopezRiosSourcePropositionBoundary : Set where
  constructor lopez-rios-source-proposition-boundary
  field
    propositionIdsAreBoundedToRecoveredArticleClaims : Bool
    propositionReceiptsCreateProofAuthority : Bool
    propositionReceiptsCreateEmpiricalPopulationAuthority : Bool
    dashiNonfactorabilityAttributedToLopezRios : Bool
    exactSentenceOrPageLocationClaimedBeyondRecovery : Bool

canonicalLopezRiosSourcePropositionBoundary :
  LopezRiosSourcePropositionBoundary
canonicalLopezRiosSourcePropositionBoundary =
  lopez-rios-source-proposition-boundary
    true false false false false
