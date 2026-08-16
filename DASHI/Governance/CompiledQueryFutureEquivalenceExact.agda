module DASHI.Governance.CompiledQueryFutureEquivalenceExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: David Blackwell.
-- Title: "Equivalent Comparisons of Experiments".
-- Venue: The Annals of Mathematical Statistics 24(2):265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Blackwell supplies comparison-of-information vocabulary only.  The exact
-- finite compiler below is the existing DASHI producer ported from PR #548.
--
-- This module closes a remaining semantic seam in that producer: the compiler
-- already proves its stabilized depth relation equals canonical future
-- observation equivalence.  Here we transport that result back to the
-- compiler's ACTUAL stabilized code relation, so a governance/query consumer
-- need not reason through an intermediate depth-indexed relation by hand.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact as Compiler
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

compiledRelationExactlyCanonicalFuture :
  ∀ {State Action Observation}
    (compiler : Compiler.CertifiedPartitionRefiner State Action Observation)
    (left right : State) →
  let compiled = Compiler.compileFutureQuotient compiler
      depth = Compiler.stableDepth compiled
  in
  Compiler.RelationIff
    (Compiler.relation compiler
      (Compiler.forwardIterate compiler depth)
      left right)
    (Future.FutureObservationEquivalent
      (Bridge.deterministicSystem
        (Compiler.step compiler)
        (Compiler.actionLabel compiler))
      (Compiler.observe compiler)
      left right)
compiledRelationExactlyCanonicalFuture compiler left right =
  Compiler.composeIff
    (Compiler.codeAtCorrect compiler depth left right)
    (Compiler.relationIff futureForward futureBackward)
  where
    compiled = Compiler.compileFutureQuotient compiler
    depth = Compiler.stableDepth compiled
    canonical = Compiler.canonicalExact compiled left right

    futureForward :
      Refinement.RefinesToDepth depth
        (Compiler.observe compiler) (Compiler.step compiler) left right →
      Future.FutureObservationEquivalent
        (Bridge.deterministicSystem
          (Compiler.step compiler)
          (Compiler.actionLabel compiler))
        (Compiler.observe compiler)
        left right
    futureForward = proj₁ canonical

    futureBackward :
      Future.FutureObservationEquivalent
        (Bridge.deterministicSystem
          (Compiler.step compiler)
          (Compiler.actionLabel compiler))
        (Compiler.observe compiler)
        left right →
      Refinement.RefinesToDepth depth
        (Compiler.observe compiler) (Compiler.step compiler) left right
    futureBackward = proj₂ canonical

compiledRelationImpliesSameFutureLanguage :
  ∀ {State Action Observation}
    (compiler : Compiler.CertifiedPartitionRefiner State Action Observation)
    {left right : State} →
  let compiled = Compiler.compileFutureQuotient compiler
      depth = Compiler.stableDepth compiled
  in
  Compiler.relation compiler
    (Compiler.forwardIterate compiler depth)
    left right →
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem
      (Compiler.step compiler)
      (Compiler.actionLabel compiler))
    (Compiler.observe compiler)
    left right
compiledRelationImpliesSameFutureLanguage compiler {left} {right} =
  Compiler.forward
    (compiledRelationExactlyCanonicalFuture compiler left right)

canonicalFutureLanguageImpliesCompiledRelation :
  ∀ {State Action Observation}
    (compiler : Compiler.CertifiedPartitionRefiner State Action Observation)
    {left right : State} →
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem
      (Compiler.step compiler)
      (Compiler.actionLabel compiler))
    (Compiler.observe compiler)
    left right →
  let compiled = Compiler.compileFutureQuotient compiler
      depth = Compiler.stableDepth compiled
  in
  Compiler.relation compiler
    (Compiler.forwardIterate compiler depth)
    left right
canonicalFutureLanguageImpliesCompiledRelation compiler {left} {right} =
  Compiler.backward
    (compiledRelationExactlyCanonicalFuture compiler left right)

record CompiledQueryFutureBoundary : Set where
  constructor compiledQueryFutureBoundary
  field
    stabilizedCodeRelationEqualsDeclaredFutureLanguage : Bool
    exactnessIsRelativeToDeclaredActionsAndObservation : Bool
    compiledEquivalenceMeansUniversalIdentity : Bool
    compiledEquivalenceCreatesLegalAuthority : Bool
    compiledEquivalenceCreatesNormativeApproval : Bool

canonicalCompiledQueryFutureBoundary : CompiledQueryFutureBoundary
canonicalCompiledQueryFutureBoundary =
  compiledQueryFutureBoundary true true false false false

record CompiledQueryFutureSourceReceipt : Set where
  constructor compiledQueryFutureSourceReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : CompiledQueryFutureBoundary

canonicalCompiledQueryFutureSourceReceipt : CompiledQueryFutureSourceReceipt
canonicalCompiledQueryFutureSourceReceipt =
  compiledQueryFutureSourceReceipt
    (Sources.blackwellExperimentComparison ∷ [])
    canonicalCompiledQueryFutureBoundary
