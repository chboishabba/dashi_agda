module DASHI.Interop.PNFConciseFactAlgebraCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Candidate-only concise fact algebra.
--
-- This module keeps the compression chain fail-closed.  It records a raw
-- source row, a PNF normal form, a quotient/fibre surface, a residual join
-- summary, a generator fact, a rendered cited fact, and one aggregate
-- receipt.  The surface is candidate-only and does not promote truth,
-- source authority, support authority, admissibility authority, or LLM
-- authority.

record NormalFormFact : Set where
  constructor mkNormalFormFact
  field
    sourceRow :
      String

    sourceSpan :
      String

    citations :
      List String

    receipts :
      List String

    normalForm :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

record FactQuotient : Set where
  constructor mkFactQuotient
  field
    normalFormFact :
      NormalFormFact

    quotientLabel :
      String

    quotientSpan :
      String

    quotientCitations :
      List String

    quotientReceipts :
      List String

    quotientSurface :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

record ProjectionFibre : Set where
  constructor mkProjectionFibre
  field
    factQuotient :
      FactQuotient

    fibreLabel :
      String

    fibreSpan :
      String

    fibreCitations :
      List String

    fibreReceipts :
      List String

    fibreSurface :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    truthAuthority :
      Bool

    sourceAuthority :
      Bool

    supportAuthority :
      Bool

    admissibilityAuthority :
      Bool

    llmAuthority :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

    truthAuthorityIsFalse :
      truthAuthority ≡ false

    sourceAuthorityIsFalse :
      sourceAuthority ≡ false

    supportAuthorityIsFalse :
      supportAuthority ≡ false

    admissibilityAuthorityIsFalse :
      admissibilityAuthority ≡ false

    llmAuthorityIsFalse :
      llmAuthority ≡ false

record ResidualJoinSummary : Set where
  constructor mkResidualJoinSummary
  field
    projectionFibre :
      ProjectionFibre

    residualLevel :
      Residual.ResidualLevel

    residualSpan :
      String

    residualCitations :
      List String

    residualReceipts :
      List String

    residualSummary :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

record GeneratorFact : Set where
  constructor mkGeneratorFact
  field
    residualJoinSummary :
      ResidualJoinSummary

    generatorLabel :
      String

    generatorSpan :
      String

    generatorCitations :
      List String

    generatorReceipts :
      List String

    generatorSurface :
      String

    generatorCandidateRow :
      CandidateOnly.CandidateOnlyRow

    generatorCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt generatorCandidateRow

    generatorAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    candidateOnly :
      Bool

    promoted :
      Bool

    truthAuthority :
      Bool

    sourceAuthority :
      Bool

    supportAuthority :
      Bool

    admissibilityAuthority :
      Bool

    llmAuthority :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

    truthAuthorityIsFalse :
      truthAuthority ≡ false

    sourceAuthorityIsFalse :
      sourceAuthority ≡ false

    supportAuthorityIsFalse :
      supportAuthority ≡ false

    admissibilityAuthorityIsFalse :
      admissibilityAuthority ≡ false

    llmAuthorityIsFalse :
      llmAuthority ≡ false

record RenderedCitedFact : Set where
  constructor mkRenderedCitedFact
  field
    generatorFact :
      GeneratorFact

    renderedLabel :
      String

    renderedSpan :
      String

    renderedCitations :
      List String

    renderedReceipts :
      List String

    renderedSurface :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    truthAuthority :
      Bool

    sourceAuthority :
      Bool

    supportAuthority :
      Bool

    admissibilityAuthority :
      Bool

    llmAuthority :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

    truthAuthorityIsFalse :
      truthAuthority ≡ false

    sourceAuthorityIsFalse :
      sourceAuthority ≡ false

    supportAuthorityIsFalse :
      supportAuthority ≡ false

    admissibilityAuthorityIsFalse :
      admissibilityAuthority ≡ false

    llmAuthorityIsFalse :
      llmAuthority ≡ false

record ConciseFactAlgebraAggregateReceipt : Set where
  constructor mkConciseFactAlgebraAggregateReceipt
  field
    rawSourceRow :
      String

    sourceSpan :
      String

    citations :
      List String

    receipts :
      List String

    normalFormFact :
      NormalFormFact

    factQuotient :
      FactQuotient

    projectionFibre :
      ProjectionFibre

    residualJoinSummary :
      ResidualJoinSummary

    generatorFact :
      GeneratorFact

    renderedCitedFact :
      RenderedCitedFact

    aggregateLabel :
      String

    spans :
      List String

    candidateOnly :
      Bool

    promoted :
      Bool

    truthAuthority :
      Bool

    sourceAuthority :
      Bool

    supportAuthority :
      Bool

    admissibilityAuthority :
      Bool

    llmAuthority :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promotedIsFalse :
      promoted ≡ false

    truthAuthorityIsFalse :
      truthAuthority ≡ false

    sourceAuthorityIsFalse :
      sourceAuthority ≡ false

    supportAuthorityIsFalse :
      supportAuthority ≡ false

    admissibilityAuthorityIsFalse :
      admissibilityAuthority ≡ false

    llmAuthorityIsFalse :
      llmAuthority ≡ false

------------------------------------------------------------------------
-- Stage constructors.

normalFormFactFromRawSourceRow :
  String →
  String →
  List String →
  List String →
  String →
  NormalFormFact
normalFormFactFromRawSourceRow rawRow sourceSpan citations receipts normalForm =
  record
    { sourceRow = rawRow
    ; sourceSpan = sourceSpan
    ; citations = citations
    ; receipts = receipts
    ; normalForm = normalForm
    ; candidateOnly = true
    ; promoted = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    }

factQuotientFromNormalFormFact :
  NormalFormFact →
  String →
  String →
  List String →
  List String →
  String →
  FactQuotient
factQuotientFromNormalFormFact normalFormFact quotientLabel quotientSpan
  quotientCitations quotientReceipts quotientSurface =
  record
    { normalFormFact = normalFormFact
    ; quotientLabel = quotientLabel
    ; quotientSpan = quotientSpan
    ; quotientCitations = quotientCitations
    ; quotientReceipts = quotientReceipts
    ; quotientSurface = quotientSurface
    ; candidateOnly = true
    ; promoted = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    }

projectionFibreFromFactQuotient :
  FactQuotient →
  String →
  String →
  List String →
  List String →
  String →
  ProjectionFibre
projectionFibreFromFactQuotient factQuotient fibreLabel fibreSpan fibreCitations
  fibreReceipts fibreSurface =
  record
    { factQuotient = factQuotient
    ; fibreLabel = fibreLabel
    ; fibreSpan = fibreSpan
    ; fibreCitations = fibreCitations
    ; fibreReceipts = fibreReceipts
    ; fibreSurface = fibreSurface
    ; candidateOnly = true
    ; promoted = false
    ; truthAuthority = false
    ; sourceAuthority = false
    ; supportAuthority = false
    ; admissibilityAuthority = false
    ; llmAuthority = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    ; truthAuthorityIsFalse = refl
    ; sourceAuthorityIsFalse = refl
    ; supportAuthorityIsFalse = refl
    ; admissibilityAuthorityIsFalse = refl
    ; llmAuthorityIsFalse = refl
    }

residualJoinSummaryFromProjectionFibre :
  ProjectionFibre →
  Residual.ResidualLevel →
  String →
  List String →
  List String →
  String →
  ResidualJoinSummary
residualJoinSummaryFromProjectionFibre projectionFibre residualLevel residualSpan
  residualCitations residualReceipts residualSummary =
  record
    { projectionFibre = projectionFibre
    ; residualLevel = residualLevel
    ; residualSpan = residualSpan
    ; residualCitations = residualCitations
    ; residualReceipts = residualReceipts
    ; residualSummary = residualSummary
    ; candidateOnly = true
    ; promoted = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    }

generatorFactFromResidualJoinSummary :
  ResidualJoinSummary →
  String →
  String →
  List String →
  List String →
  String →
  GeneratorFact
generatorFactFromResidualJoinSummary residualJoinSummary generatorLabel
  generatorSpan generatorCitations generatorReceipts generatorSurface =
  let
    generatorCandidateRow =
      CandidateOnly.mkCandidateOnlyRow
        generatorLabel
        "DASHI.Interop.PNFConciseFactAlgebraCore"
        generatorSurface
        CandidateOnly.rowCandidateKind
        CandidateOnly.rowCandidateOnlyStatus
        "candidate-only concise fact generator"
        "no truth, source, support, admissibility, or LLM authority is carried"

    generatorCandidateReceipt =
      CandidateOnly.mkCandidateOnlyReceipt
        generatorCandidateRow
        refl
        refl
        refl
        refl
        refl
        refl
        refl
        refl
  in
  record
    { residualJoinSummary = residualJoinSummary
    ; generatorLabel = generatorLabel
    ; generatorSpan = generatorSpan
    ; generatorCitations = generatorCitations
    ; generatorReceipts = generatorReceipts
    ; generatorSurface = generatorSurface
    ; generatorCandidateRow = generatorCandidateRow
    ; generatorCandidateReceipt = generatorCandidateReceipt
    ; generatorAuthorityBundle =
        AuthorityNA.mkClosedAuthorityNonPromotionBundle generatorLabel
    ; candidateOnly = true
    ; promoted = false
    ; truthAuthority = false
    ; sourceAuthority = false
    ; supportAuthority = false
    ; admissibilityAuthority = false
    ; llmAuthority = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    ; truthAuthorityIsFalse = refl
    ; sourceAuthorityIsFalse = refl
    ; supportAuthorityIsFalse = refl
    ; admissibilityAuthorityIsFalse = refl
    ; llmAuthorityIsFalse = refl
    }

renderedCitedFactFromGeneratorFact :
  GeneratorFact →
  String →
  String →
  List String →
  List String →
  String →
  RenderedCitedFact
renderedCitedFactFromGeneratorFact generatorFact renderedLabel renderedSpan
  renderedCitations renderedReceipts renderedSurface =
  record
    { generatorFact = generatorFact
    ; renderedLabel = renderedLabel
    ; renderedSpan = renderedSpan
    ; renderedCitations = renderedCitations
    ; renderedReceipts = renderedReceipts
    ; renderedSurface = renderedSurface
    ; candidateOnly = true
    ; promoted = false
    ; truthAuthority = false
    ; sourceAuthority = false
    ; supportAuthority = false
    ; admissibilityAuthority = false
    ; llmAuthority = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    ; truthAuthorityIsFalse = refl
    ; sourceAuthorityIsFalse = refl
    ; supportAuthorityIsFalse = refl
    ; admissibilityAuthorityIsFalse = refl
    ; llmAuthorityIsFalse = refl
    }

------------------------------------------------------------------------
-- Canonical closed surface.

canonicalNormalFormFact :
  NormalFormFact
canonicalNormalFormFact =
  normalFormFactFromRawSourceRow
    "raw/source row"
    "source span"
    ("canonical citation 1" ∷ "canonical citation 2" ∷ [])
    ("canonical receipt 1" ∷ [])
    "pnf normal form"

canonicalFactQuotient :
  FactQuotient
canonicalFactQuotient =
  factQuotientFromNormalFormFact
    canonicalNormalFormFact
    "fact quotient"
    "quotient span"
    ("canonical citation 3" ∷ [])
    ("canonical receipt 2" ∷ [])
    "quotient surface"

canonicalProjectionFibre :
  ProjectionFibre
canonicalProjectionFibre =
  projectionFibreFromFactQuotient
    canonicalFactQuotient
    "projection fibre"
    "fibre span"
    ("canonical citation 4" ∷ [])
    ("canonical receipt 3" ∷ [])
    "fibre surface"

canonicalResidualJoinSummary :
  ResidualJoinSummary
canonicalResidualJoinSummary =
  residualJoinSummaryFromProjectionFibre
    canonicalProjectionFibre
    Residual.partial
    "residual join span"
    ("canonical citation 5" ∷ [])
    ("canonical receipt 4" ∷ [])
    "partial residual join summary"

canonicalGeneratorFact :
  GeneratorFact
canonicalGeneratorFact =
  generatorFactFromResidualJoinSummary
    canonicalResidualJoinSummary
    "generator fact"
    "generator span"
    ("canonical citation 6" ∷ [])
    ("canonical receipt 5" ∷ [])
    "generator surface"

canonicalRenderedCitedFact :
  RenderedCitedFact
canonicalRenderedCitedFact =
  renderedCitedFactFromGeneratorFact
    canonicalGeneratorFact
    "rendered cited fact"
    "rendered span"
    ("canonical citation 7" ∷ [])
    ("canonical receipt 6" ∷ [])
    "rendered cited surface"

canonicalConciseFactAlgebraAggregateReceipt :
  ConciseFactAlgebraAggregateReceipt
canonicalConciseFactAlgebraAggregateReceipt =
  record
    { rawSourceRow = "raw/source row"
    ; sourceSpan = "source span"
    ; citations =
        "canonical citation 1"
        ∷ "canonical citation 2"
        ∷ "canonical citation 3"
        ∷ "canonical citation 4"
        ∷ "canonical citation 5"
        ∷ "canonical citation 6"
        ∷ "canonical citation 7"
        ∷ []
    ; receipts =
        "canonical receipt 1"
        ∷ "canonical receipt 2"
        ∷ "canonical receipt 3"
        ∷ "canonical receipt 4"
        ∷ "canonical receipt 5"
        ∷ "canonical receipt 6"
        ∷ []
    ; normalFormFact = canonicalNormalFormFact
    ; factQuotient = canonicalFactQuotient
    ; projectionFibre = canonicalProjectionFibre
    ; residualJoinSummary = canonicalResidualJoinSummary
    ; generatorFact = canonicalGeneratorFact
    ; renderedCitedFact = canonicalRenderedCitedFact
    ; aggregateLabel = "concise fact algebra aggregate receipt"
    ; spans =
        "source span"
        ∷ "quotient span"
        ∷ "fibre span"
        ∷ "residual join span"
        ∷ "generator span"
        ∷ "rendered span"
        ∷ []
    ; candidateOnly = true
    ; promoted = false
    ; truthAuthority = false
    ; sourceAuthority = false
    ; supportAuthority = false
    ; admissibilityAuthority = false
    ; llmAuthority = false
    ; candidateOnlyIsTrue = refl
    ; promotedIsFalse = refl
    ; truthAuthorityIsFalse = refl
    ; sourceAuthorityIsFalse = refl
    ; supportAuthorityIsFalse = refl
    ; admissibilityAuthorityIsFalse = refl
    ; llmAuthorityIsFalse = refl
    }
