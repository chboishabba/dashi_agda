{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- PRIMARY AUTHORITY
--
-- John C. Collins, Anthony Duncan, Satish D. Joglekar,
-- "Trace and dilatation anomalies in gauge theories",
-- Physical Review D 16 (1977), 438.
-- DOI: 10.1103/PhysRevD.16.438.
--
-- This authority supports the renormalized non-Abelian trace-anomaly theorem.
-- It does NOT identify a finite CMP119 insertion with the renormalized operator.
------------------------------------------------------------------------

traceAnomalyPrimaryAuthor : String
traceAnomalyPrimaryAuthor =
  "John C. Collins; Anthony Duncan; Satish D. Joglekar"

traceAnomalyPrimaryTitle : String
traceAnomalyPrimaryTitle =
  "Trace and dilatation anomalies in gauge theories"

traceAnomalyPrimaryDOI : String
traceAnomalyPrimaryDOI =
  "10.1103/PhysRevD.16.438"

record RenormalizedPureYMTraceAnomalyAuthority
    (embedding :
      Embed.OrderedRationalRealEmbedding)
    (convention : SU2Trace.RealSU2TraceConvention embedding) : Set₁ where
  field
    renormalizedF2Numerator : ℝ
    renormalizedTraceNumerator : ℝ

    renormalizedTraceIsSU2BetaF2 :
      renormalizedTraceNumerator
      ≡
      SU2Trace.realSU2TraceCoefficient embedding convention
      *ℝ renormalizedF2Numerator

open RenormalizedPureYMTraceAnomalyAuthority public

renormalizedPureYMTraceAnomalyAuthorityLevel : ProofLevel
renormalizedPureYMTraceAnomalyAuthorityLevel = standardImported

------------------------------------------------------------------------
-- CMP119 SAME-OBJECT TRANSPORT
--
-- This is the genuine model-specific physics seam.  Both the selected quantum
-- trace numerator and selected F^2 numerator must be transported to the SAME
-- renormalized operator pair before the literature theorem can be consumed.
------------------------------------------------------------------------

record CMP119ToRenormalizedTraceAnomalyWeld
    {embedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (authority :
      RenormalizedPureYMTraceAnomalyAuthority embedding convention) : Set₁ where
  field
    selectedCMP119QuantumTraceNumerator : ℝ
    selectedCMP119F2Numerator : ℝ

    selectedTraceIsRenormalizedTrace :
      selectedCMP119QuantumTraceNumerator
      ≡ renormalizedTraceNumerator authority

    selectedF2IsRenormalizedF2 :
      selectedCMP119F2Numerator
      ≡ renormalizedF2Numerator authority

open CMP119ToRenormalizedTraceAnomalyWeld public

selectedCMP119TraceIsPhysicalSU2BetaF2 :
  ∀ {embedding convention authority}
    (weld :
      CMP119ToRenormalizedTraceAnomalyWeld
        {embedding = embedding}
        {convention = convention}
        authority) →
  selectedCMP119QuantumTraceNumerator weld
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ selectedCMP119F2Numerator weld
selectedCMP119TraceIsPhysicalSU2BetaF2
    {embedding = embedding} {convention = convention}
    {authority = authority} weld =
  trans
    (selectedTraceIsRenormalizedTrace weld)
    (trans
      (renormalizedTraceIsSU2BetaF2 authority)
      (cong
        (λ value →
          SU2Trace.realSU2TraceCoefficient embedding convention
          *ℝ value)
        (sym (selectedF2IsRenormalizedF2 weld))))

finiteCMP119TraceAnomalyFollowsFromCitationAlone : Bool
finiteCMP119TraceAnomalyFollowsFromCitationAlone = false
