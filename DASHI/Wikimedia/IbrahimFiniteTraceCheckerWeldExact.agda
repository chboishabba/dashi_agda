module DASHI.Wikimedia.IbrahimFiniteTraceCheckerWeldExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General
import DASHI.Wikimedia.IbrahimFinitePigeonholeProducerExact as Pigeonhole
import DASHI.Wikimedia.IbrahimCycleRotationRelationExact as Rotation

------------------------------------------------------------------------
-- NEW DASHI mathematical checker semantics for a supplied finite
-- first-link edge trace. Original FLN method: Ibrahim, Danforth,
-- Dodds (2017), DOI 10.1016/j.jocs.2016.12.001.
--
-- This is a proof-level contract of accepted trace evidence: each
-- transition contains an equality to the ACTUAL declared next function.
-- The Python wire-format/parser/JSON/hash routines are not themselves
-- kernel-verified by this file. Reusing the checked native edge
-- extraction and preserving source identity is a distinct P1/B1 gate.
------------------------------------------------------------------------

data CheckedEdgePath {Node : Set}
    (next : Node → Node) : Nat → Node → Node → Set where
  pathEnd : ∀ {start} → CheckedEdgePath next zero start start
  pathEdge : ∀ {hops start destination finish} →
    next start ≡ destination →
    CheckedEdgePath next hops destination finish →
    CheckedEdgePath next (suc hops) start finish

pythonTraceStepMatchesAgdaIterate :
  ∀ {Node : Set} {next : Node → Node}
    {hops : Nat} {start finish : Node} →
  CheckedEdgePath next hops start finish →
  Orbit.iterate next hops start ≡ finish
pythonTraceStepMatchesAgdaIterate pathEnd = refl
pythonTraceStepMatchesAgdaIterate {next = next}
    (pathEdge {hops = hops} same tail) =
  trans (cong (Orbit.iterate next hops) same)
    (pythonTraceStepMatchesAgdaIterate tail)

agdaIterateEmitsCheckedPath :
  ∀ {Node : Set}
    (next : Node → Node) (hops : Nat) (start : Node) →
  CheckedEdgePath next hops start
    (Orbit.iterate next hops start)
agdaIterateEmitsCheckedPath next zero start = pathEnd
agdaIterateEmitsCheckedPath next (suc hops) start =
  pathEdge refl (agdaIterateEmitsCheckedPath next hops (next start))

record AcceptedCycleTrace {Node : Set}
    (next : Node → Node) (start : Node) : Set where
  constructor acceptedCycleTrace
  field
    entryHops periodTail : Nat
    representative : Node
    entryPath :
      CheckedEdgePath next entryHops start representative
    returnPath :
      CheckedEdgePath next (suc periodTail) representative representative
open AcceptedCycleTrace public

acceptedTraceImpliesEventualCycle :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  AcceptedCycleTrace next start →
  Orbit.EventualCycle next start
acceptedTraceImpliesEventualCycle trace =
  Orbit.eventualCycle
    (entryHops trace)
    (periodTail trace)
    (representative trace)
    (pythonTraceStepMatchesAgdaIterate (entryPath trace))
    (pythonTraceStepMatchesAgdaIterate (returnPath trace))

acceptedTraceImpliesOrbitRepeat :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  AcceptedCycleTrace next start →
  General.OrbitRepeat next start
acceptedTraceImpliesOrbitRepeat trace =
  General.eventualCycleToCollision
    (acceptedTraceImpliesEventualCycle trace)

eventualCycleEmitsAcceptedTrace :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  Orbit.EventualCycle next start →
  AcceptedCycleTrace next start
eventualCycleEmitsAcceptedTrace {next = next} {start = start}
    certificate =
  acceptedCycleTrace
    (Orbit.entryHops certificate)
    (Orbit.periodTail certificate)
    (Orbit.representative certificate)
    (subst
      (CheckedEdgePath next
        (Orbit.entryHops certificate) start)
      (Orbit.entered certificate)
      (agdaIterateEmitsCheckedPath next
        (Orbit.entryHops certificate) start))
    (subst
      (CheckedEdgePath next
        (suc (Orbit.periodTail certificate))
        (Orbit.representative certificate))
      (Orbit.closed certificate)
      (agdaIterateEmitsCheckedPath next
        (suc (Orbit.periodTail certificate))
        (Orbit.representative certificate)))

certificateGenerationCompleteForFiniteTotalGraphs :
  ∀ {Node : Set}
    (next : Node → Node)
    (carrier : General.CompleteFiniteCarrier Node)
    (start : Node) →
  AcceptedCycleTrace next start
certificateGenerationCompleteForFiniteTotalGraphs next carrier start =
  eventualCycleEmitsAcceptedTrace
    (Pigeonhole.allFiniteStartsEventuallyCycle next carrier start)

terminalCensusMatchesCertificateUpToRotation :
  ∀ {Node : Set}
    (next : Node → Node)
    (carrier : General.CompleteFiniteCarrier Node)
    (start : Node) →
  (accepted : AcceptedCycleTrace next start) →
  Rotation.MutualOrbitRotation next
    (representative accepted)
    (Orbit.representative
      (Pigeonhole.allFiniteStartsEventuallyCycle next carrier start))
terminalCensusMatchesCertificateUpToRotation next carrier start accepted =
  Rotation.terminalCycleUniqueUpToRotation
    (acceptedTraceImpliesEventualCycle accepted)
    (Pigeonhole.allFiniteStartsEventuallyCycle next carrier start)

-- The theorem verifies the semantic meaning of EXPLICIT per-edge
-- equality witnesses. It does not verify JSON ingestion, Python
-- implementation correctness, immutable source-object identity,
-- original author parser parity, or a signed human review licence.
