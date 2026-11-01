{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedSameObjectReductionExact where

------------------------------------------------------------------------
-- P2 MAX-CUT: LITERATURE ANOMALY + TWO SAME-OBJECT TRANSPORTS
--
-- Attribution boundary:
--
-- Primary authority (already pinned in the imported owner):
--   John C. Collins, Anthony Duncan, Satish D. Joglekar,
--   "Trace and dilatation anomalies in gauge theories",
--   Phys. Rev. D 16 (1977) 438,
--   DOI 10.1103/PhysRevD.16.438.
--
-- That citation supports the renormalized non-Abelian trace-anomaly theorem.
-- It does NOT by itself identify the selected CMP119/R136 stress or F^2
-- observable with the renormalized operator pair.  Those two identifications
-- remain DASHI's same-object/source payments.
--
-- Therefore Q2 should not be charged as one opaque new anomaly equation.  Once
-- the two same-object transports are supplied, the cited theorem compiles the
-- selected Hilbert trace relation automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record SelectedStressF2ToRenormalizedPair
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (authority :
      Anomaly.RenormalizedPureYMTraceAnomalyAuthority embedding convention)
    (selectedHilbertTrace selectedF2 : ℝ) : Set₁ where
  field
    -- These are the model/source-specific payments.  They are not attributed to
    -- Collins--Duncan--Joglekar unless a source explicitly supplies them.
    selectedHilbertTraceIsRenormalizedTrace :
      selectedHilbertTrace
      ≡ Anomaly.renormalizedTraceNumerator authority

    selectedF2IsRenormalizedF2 :
      selectedF2
      ≡ Anomaly.renormalizedF2Numerator authority

open SelectedStressF2ToRenormalizedPair public

selectedHilbertTraceIsSU2BetaF2 :
  ∀ {embedding convention authority selectedHilbertTrace selectedF2} →
  SelectedStressF2ToRenormalizedPair
    {embedding = embedding}
    {convention = convention}
    authority selectedHilbertTrace selectedF2 →
  selectedHilbertTrace
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ selectedF2
selectedHilbertTraceIsSU2BetaF2
    {embedding = embedding}
    {convention = convention}
    {authority = authority}
    reduction =
  trans
    (selectedHilbertTraceIsRenormalizedTrace reduction)
    (trans
      (Anomaly.renormalizedTraceIsSU2BetaF2 authority)
      (cong
        (λ value →
          SU2Trace.realSU2TraceCoefficient embedding convention *ℝ value)
        (sym (selectedF2IsRenormalizedF2 reduction))))

asCMP119ToRenormalizedTraceAnomalyWeld :
  ∀ {embedding convention authority selectedHilbertTrace selectedF2} →
  SelectedStressF2ToRenormalizedPair
    {embedding = embedding}
    {convention = convention}
    authority selectedHilbertTrace selectedF2 →
  Anomaly.CMP119ToRenormalizedTraceAnomalyWeld authority
asCMP119ToRenormalizedTraceAnomalyWeld
    {selectedHilbertTrace = selectedHilbertTrace}
    {selectedF2 = selectedF2}
    reduction = record
  { Anomaly.CMP119ToRenormalizedTraceAnomalyWeld.selectedCMP119QuantumTraceNumerator =
      selectedHilbertTrace
  ; Anomaly.CMP119ToRenormalizedTraceAnomalyWeld.selectedCMP119F2Numerator =
      selectedF2
  ; Anomaly.CMP119ToRenormalizedTraceAnomalyWeld.selectedTraceIsRenormalizedTrace =
      selectedHilbertTraceIsRenormalizedTrace reduction
  ; Anomaly.CMP119ToRenormalizedTraceAnomalyWeld.selectedF2IsRenormalizedF2 =
      selectedF2IsRenormalizedF2 reduction
  }

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

traceAnomalyLiteratureAuthorityReused : Bool
traceAnomalyLiteratureAuthorityReused = true

q2ReducedToStressAndF2RenormalizedTransports : Bool
q2ReducedToStressAndF2RenormalizedTransports = true

citationAlonePaysCMP119SameObjectTransport : Bool
citationAlonePaysCMP119SameObjectTransport = false

freeQuantumTraceScalarRequired : Bool
freeQuantumTraceScalarRequired = false

-- DASHI contribution: the reduction/compiler above.  Source attribution remains
-- with the cited anomaly theorem and with whichever source eventually pays the
-- two selected-object transport equalities.
compilerIsDASHIContributionNotPrimarySourceClaim : Bool
compilerIsDASHIContributionNotPrimarySourceClaim = true
