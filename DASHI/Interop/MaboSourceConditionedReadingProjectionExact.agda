module DASHI.Interop.MaboSourceConditionedReadingProjectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SemanticReaderElucidatoryConeExact as Reader
import DASHI.Interop.SensibLawMaboProgressiveExplanationProjectionExact as Mabo

------------------------------------------------------------------------
-- SOURCE-CONDITIONED MABO READING PROJECTION
--
-- Runtime counterpart:
--   ITIR-suite/itir-svelte/src/lib/workbench/maboSourceProjection.js
--
-- The retained SensibLaw corpus currently pays only a coarse Mabo coordinate:
-- native title is recognised and terra-nullius is rejected in the corpus
-- summary.  It does not contain the exact judgment span/revision necessary to
-- pay the detailed radical-title proposition chain.  The reader may therefore
-- display a shallow explanation while exact Source/Why requests defer with an
-- acquisition/review residual rather than manufacturing authority coordinates.
------------------------------------------------------------------------

record CanonicalMaboCorpusPayment : Set where
  constructor canonicalMaboCorpusPayment
  field
    corpusReference : String
    citationReference : String
    recognisedNativeTitleCoordinatePaid : Bool
    rejectedTerraNulliusCoordinatePaid : Bool
    exactRadicalTitleSpanPaid : Bool
    detailedFiveStageChainPaid : Bool
    corpusSummaryIsExactAuthoritySpan : Bool

open CanonicalMaboCorpusPayment public

canonicalCorpusPayment : CanonicalMaboCorpusPayment
canonicalCorpusPayment = canonicalMaboCorpusPayment
  "sensiblaw:data/corpus/mabo_v_queensland_no2.json"
  "Mabo v Queensland (No 2) [1992] HCA 23"
  true
  true
  false
  false
  false

data ReaderAction : Set where
  explainAction
  contextAction
  sourceAction
  whyAction : ReaderAction

data ReaderDisposition : Set where
  executeDisposition
  deferExactAuthoritySpan
  deferDetailedPropositionChain : ReaderDisposition

sourceConditionedDisposition : ReaderAction → ReaderDisposition
sourceConditionedDisposition explainAction = executeDisposition
sourceConditionedDisposition contextAction = executeDisposition
sourceConditionedDisposition sourceAction = deferExactAuthoritySpan
sourceConditionedDisposition whyAction = deferDetailedPropositionChain

sourceDefers : sourceConditionedDisposition sourceAction ≡ deferExactAuthoritySpan
sourceDefers = refl

whyDefers : sourceConditionedDisposition whyAction ≡ deferDetailedPropositionChain
whyDefers = refl

explainExecutes : sourceConditionedDisposition explainAction ≡ executeDisposition
explainExecutes = refl

------------------------------------------------------------------------
-- Existing semantic-reader and Mabo owners remain the parent contracts.
------------------------------------------------------------------------

semanticReaderAnchor : Reader.SemanticReaderParity
semanticReaderAnchor = Reader.canonicalSemanticReaderParity

maboRuntimeAnchor : Mabo.RuntimeReadingConeParity
maboRuntimeAnchor = Mabo.canonicalRuntimeReadingConeParity

------------------------------------------------------------------------
-- Firewalls: coarse corpus support cannot be laundered into the unpaid detail.
------------------------------------------------------------------------

data CoarseCorpusPaysExactAuthoritySpanPermission : Set where
data CoarseCorpusPaysDetailedFiveStageChainPermission : Set where
data DeferredSourceRequestCreatesAuthorityPermission : Set where
data ReaderProseCreatesEvidencePaymentPermission : Set where

coarseCorpusCannotPayExactAuthoritySpan :
  CoarseCorpusPaysExactAuthoritySpanPermission → ⊥
coarseCorpusCannotPayExactAuthoritySpan ()

coarseCorpusCannotPayDetailedFiveStageChain :
  CoarseCorpusPaysDetailedFiveStageChainPermission → ⊥
coarseCorpusCannotPayDetailedFiveStageChain ()

deferredSourceRequestCannotCreateAuthority :
  DeferredSourceRequestCreatesAuthorityPermission → ⊥
deferredSourceRequestCannotCreateAuthority ()

readerProseCannotCreateEvidencePayment :
  ReaderProseCreatesEvidencePaymentPermission → ⊥
readerProseCannotCreateEvidencePayment ()

------------------------------------------------------------------------
-- Certification coordinates stay explicit.
------------------------------------------------------------------------

itirRuntimeReference : String
itirRuntimeReference =
  "ITIR-suite/itir-svelte/src/lib/workbench/maboSourceProjection.js"

sensibLawCorpusReference : String
sensibLawCorpusReference = "data/corpus/mabo_v_queensland_no2.json"

sourceWritten : Bool
sourceWritten = true

runtimeExactHeadReceiptObserved : Bool
runtimeExactHeadReceiptObserved = false

agdaKernelReceiptObserved : Bool
agdaKernelReceiptObserved = false
