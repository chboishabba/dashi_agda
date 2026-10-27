{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedTraceF2AuthorityCompilerExact where

------------------------------------------------------------------------
-- S2 MAX-CUT: THE TRACE-ANOMALY OPERATOR IDENTITY IS ALREADY IMPORTED.
--
-- `CMP119AntigravityRealTraceAnomalySameObjectExact` contains the proof-bearing
-- Collins--Duncan--Joglekar authority
--
--   renormalizedTrace = c_beta * renormalizedF2.
--
-- Therefore the cosmology lane does not owe a fresh Ward/anomaly proof.  It owes
-- only SAME-OBJECT transport of its exact Hilbert stress trace and selected
-- completed F^2 numerator to that renormalized operator pair.  Once those two
-- equalities are supplied, the Local-C identity is pure equality algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Authority
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record LocalCRenormalizedTraceF2Weld
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (authority : Authority.RenormalizedPureYMTraceAnomalyAuthority
      embedding convention)
    (localHilbertTrace localF2 : ℝ) : Set₁ where
  field
    localHilbertTraceIsRenormalizedTrace :
      localHilbertTrace ≡ Authority.renormalizedTraceNumerator authority

    localF2IsRenormalizedF2 :
      localF2 ≡ Authority.renormalizedF2Numerator authority

open LocalCRenormalizedTraceF2Weld public

localTraceIsPhysicalSU2BetaF2 :
  ∀ {embedding convention authority localHilbertTrace localF2} →
  LocalCRenormalizedTraceF2Weld
    {embedding = embedding} {convention = convention}
    authority localHilbertTrace localF2 →
  localHilbertTrace
  ≡ SU2Trace.realSU2TraceCoefficient embedding convention *ℝ localF2
localTraceIsPhysicalSU2BetaF2
    {embedding = embedding} {convention = convention}
    {authority = authority} weld =
  trans
    (localHilbertTraceIsRenormalizedTrace weld)
    (trans
      (Authority.renormalizedTraceIsSU2BetaF2 authority)
      (cong
        (λ value →
          SU2Trace.realSU2TraceCoefficient embedding convention *ℝ value)
        (sym (localF2IsRenormalizedF2 weld))))

renormalizedTraceAnomalyIdentityNeedsFreshProof : Bool
renormalizedTraceAnomalyIdentityNeedsFreshProof = false

remainingS2WorkIsSameObjectTraceF2AuthorityWeld : Bool
remainingS2WorkIsSameObjectTraceF2AuthorityWeld = true

s2EqualityTransportCompilerLevel : ProofLevel
s2EqualityTransportCompilerLevel = machineChecked
