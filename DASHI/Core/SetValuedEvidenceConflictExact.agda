module DASHI.Core.SetValuedEvidenceConflictExact where

------------------------------------------------------------------------
-- Set-valued evidence keeps support for a family of hypotheses distinct from
-- support for one member, and keeps unresolved conflict explicit rather than
-- silently normalising it away.
--
-- REFERENCE / MOTIVATION
-- Glenn Shafer, "A Mathematical Theory of Evidence", Princeton University
-- Press, 1976.  No DOI is asserted.  The source motivates set-valued evidence;
-- the exact finite carriers and theorems below are DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

record SetValuedEvidence
    (Hypothesis Focal Mass : Set) : Set₁ where
  constructor setValuedEvidence
  field
    Contains : Focal → Hypothesis → Set
    wholeFrame : Focal
    wholeContains : (hypothesis : Hypothesis) → Contains wholeFrame hypothesis
    focalMass : Focal → Mass
    totalMass : Mass
    conflictMass : Mass

open SetValuedEvidence public

record NormalizationAuthority
    {Hypothesis Focal Mass : Set}
    (evidence : SetValuedEvidence Hypothesis Focal Mass) : Set₁ where
  constructor normalizationAuthority
  field
    conflictIsTotal : conflictMass evidence ≡ totalMass evidence → ⊥

open NormalizationAuthority public

totalConflictRefutesNormalizationAuthority :
  ∀ {Hypothesis Focal Mass}
    {evidence : SetValuedEvidence Hypothesis Focal Mass} →
  conflictMass evidence ≡ totalMass evidence →
  NormalizationAuthority evidence →
  ⊥
totalConflictRefutesNormalizationAuthority total authority =
  conflictIsTotal authority total

------------------------------------------------------------------------
-- Concrete finite ambiguity witness: one focal set can support request-or-play
-- without manufacturing a choice between request and play.
------------------------------------------------------------------------

data DemoHypothesis : Set where
  request play genericAttention : DemoHypothesis

data DemoFocal : Set where
  requestOrPlay whole : DemoFocal

DemoContains : DemoFocal → DemoHypothesis → Set
DemoContains requestOrPlay request = ⊤
DemoContains requestOrPlay play = ⊤
DemoContains requestOrPlay genericAttention = ⊥
DemoContains whole request = ⊤
DemoContains whole play = ⊤
DemoContains whole genericAttention = ⊤

requestOrPlaySupportsRequest : DemoContains requestOrPlay request
requestOrPlaySupportsRequest = tt

requestOrPlaySupportsPlay : DemoContains requestOrPlay play
requestOrPlaySupportsPlay = tt

requestOrPlayDoesNotSupportGenericAttention :
  DemoContains requestOrPlay genericAttention → ⊥
requestOrPlayDoesNotSupportGenericAttention evidence = evidence

------------------------------------------------------------------------
-- Reliability degradation is represented by moving admissible mass toward
-- ignorance, never by manufacturing additional support.
------------------------------------------------------------------------

record SupportIgnoranceBudget : Set where
  constructor supportIgnoranceBudget
  field
    supportedMass : Nat
    ignoranceMass : Nat
    total : Nat
    conserved : supportedMass + ignoranceMass ≡ total

open SupportIgnoranceBudget public

record ReliabilityDegradation
    (before after : SupportIgnoranceBudget) : Set where
  constructor reliabilityDegradation
  field
    supportDoesNotIncrease : supportedMass after ≤ supportedMass before
    ignoranceDoesNotDecrease : ignoranceMass before ≤ ignoranceMass after
    totalPreserved : total before ≡ total after

open ReliabilityDegradation public

reliabilityDegradationCannotCreateSupport :
  ∀ {before after} →
  ReliabilityDegradation before after →
  supportedMass after ≤ supportedMass before
reliabilityDegradationCannotCreateSupport = supportDoesNotIncrease

record SetValuedEvidenceBoundary : Set where
  constructor setValuedEvidenceBoundary
  field
    familySupportNeedNotSelectOneHypothesis : Bool
    ignoranceIsNotOpposition : Bool
    conflictIsRetainedBeforeNormalization : Bool
    totalConflictBlocksNormalizationAuthority : Bool
    degradedReliabilityMovesTowardIgnorance : Bool
    evidenceAlgebraDoesNotCreateSemanticAuthority : Bool

canonicalSetValuedEvidenceBoundary : SetValuedEvidenceBoundary
canonicalSetValuedEvidenceBoundary =
  setValuedEvidenceBoundary true true true true true true
