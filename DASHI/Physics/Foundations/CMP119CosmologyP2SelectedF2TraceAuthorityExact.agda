{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2SelectedF2TraceAuthorityExact where

------------------------------------------------------------------------
-- S2/S3a CROSS-POLLINATION.
--
-- The source-first S3a presentation already has the selected completed F^2
-- composite.  Do not introduce a second arbitrary Local-C F^2 scalar and then
-- prove it equal to that selected composite.  Apply the imported renormalized
-- trace/F^2 authority directly to the selected F^2 object.
--
-- Remaining physical same-object content:
--   1. exact Local-C Hilbert trace = imported renormalized trace;
--   2. selected completed F^2 = imported renormalized F^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedMarkedF2Exact as Selected
import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedTraceF2AuthorityCompilerExact as Compiler
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Authority
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record SelectedF2RenormalizedTraceWeld
    {CurvaturePolynomial Position continuityScale CompletedState Composite}
    (source :
      Selected.SelectedMarkedF2Source
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (authority : Authority.RenormalizedPureYMTraceAnomalyAuthority
      embedding convention)
    (localHilbertTrace : ℝ) : Set₁ where
  field
    localHilbertTraceIsRenormalizedTrace :
      localHilbertTrace ≡ Authority.renormalizedTraceNumerator authority

    selectedF2IsRenormalizedF2 :
      Selected.selectedF2 source
      ≡ Authority.renormalizedF2Numerator authority

open SelectedF2RenormalizedTraceWeld public

asLocalCRenormalizedTraceF2Weld :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    {source :
      Selected.SelectedMarkedF2Source
        CurvaturePolynomial Position continuityScale CompletedState Composite}
    {embedding convention authority localHilbertTrace} →
  SelectedF2RenormalizedTraceWeld
    source {embedding = embedding} {convention = convention}
    authority localHilbertTrace →
  Compiler.LocalCRenormalizedTraceF2Weld
    authority localHilbertTrace (Selected.selectedF2 source)
asLocalCRenormalizedTraceF2Weld weld = record
  { Compiler.LocalCRenormalizedTraceF2Weld.localHilbertTraceIsRenormalizedTrace =
      localHilbertTraceIsRenormalizedTrace weld
  ; Compiler.LocalCRenormalizedTraceF2Weld.localF2IsRenormalizedF2 =
      selectedF2IsRenormalizedF2 weld
  }

selectedTraceIsPhysicalSU2BetaF2 :
  ∀ {CurvaturePolynomial Position continuityScale CompletedState Composite}
    {source :
      Selected.SelectedMarkedF2Source
        CurvaturePolynomial Position continuityScale CompletedState Composite}
    {embedding convention authority localHilbertTrace}
    (weld :
      SelectedF2RenormalizedTraceWeld
        source {embedding = embedding} {convention = convention}
        authority localHilbertTrace) →
  localHilbertTrace
  ≡ SU2Trace.realSU2TraceCoefficient embedding convention
      *ℝ Selected.selectedF2 source
selectedTraceIsPhysicalSU2BetaF2 weld =
  Compiler.localTraceIsPhysicalSU2BetaF2
    (asLocalCRenormalizedTraceF2Weld weld)

independentLocalCF2ScalarIdentificationRequired : Bool
independentLocalCF2ScalarIdentificationRequired = false

freshRenormalizedTraceAnomalyIdentityRequired : Bool
freshRenormalizedTraceAnomalyIdentityRequired = false

selectedF2ToRenormalizedF2SameObjectRequired : Bool
selectedF2ToRenormalizedF2SameObjectRequired = true

localHilbertTraceToRenormalizedTraceSameObjectRequired : Bool
localHilbertTraceToRenormalizedTraceSameObjectRequired = true
