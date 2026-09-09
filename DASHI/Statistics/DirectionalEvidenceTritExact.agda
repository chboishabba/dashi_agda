module DASHI.Statistics.DirectionalEvidenceTritExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)

------------------------------------------------------------------------
-- DIRECTIONAL EVIDENCE TRIT
--
-- The balanced-ternary carrier is reused as an interpretation target only:
--   pos = evidence licenses the declared positive direction;
--   zer = neither declared direction is licensed by the supplied receipt;
--   neg = evidence licenses the declared negative direction.
--
-- `zer` is therefore an unresolved / non-directional evidential state, not a
-- synonym for falsity, refutation, or evidence for the opposite direction.
------------------------------------------------------------------------

data Direction : Set where
  positiveDirection : Direction
  negativeDirection : Direction

record DirectionalEvidenceSemantics (Result Hypothesis : Set) : Set₁ where
  constructor directional-evidence-semantics
  field
    SupportsPositive : Result → Hypothesis → Set
    SupportsNegative : Result → Hypothesis → Set
    Underdetermined : Result → Hypothesis → Set

open DirectionalEvidenceSemantics public

data DirectionalEvidenceDisposition
    {Result Hypothesis : Set}
    (semantics : DirectionalEvidenceSemantics Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Trit → Set where
  positiveEvidence :
    SupportsPositive semantics result hypothesis →
    DirectionalEvidenceDisposition semantics result hypothesis pos
  unresolvedEvidence :
    Underdetermined semantics result hypothesis →
    DirectionalEvidenceDisposition semantics result hypothesis zer
  negativeEvidence :
    SupportsNegative semantics result hypothesis →
    DirectionalEvidenceDisposition semantics result hypothesis neg

------------------------------------------------------------------------
-- Failure to establish one direction is intentionally weaker than evidence for
-- the opposite direction.  The former is represented as a negative capability:
-- no positive/negative witness was obtained; it does not synthesize a witness
-- for the antipode.
------------------------------------------------------------------------

record FailsToEstablishPositive
    {Result Hypothesis : Set}
    (semantics : DirectionalEvidenceSemantics Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor fails-to-establish-positive
  field
    noPositiveWitness : SupportsPositive semantics result hypothesis → ⊥

open FailsToEstablishPositive public

record FailsToEstablishNegative
    {Result Hypothesis : Set}
    (semantics : DirectionalEvidenceSemantics Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor fails-to-establish-negative
  field
    noNegativeWitness : SupportsNegative semantics result hypothesis → ⊥

open FailsToEstablishNegative public

------------------------------------------------------------------------
-- Structural firewalls: there is no generic compiler from failure of support to
-- counterevidence.  A domain-specific bridge must supply an actual opposite
-- directional witness.
------------------------------------------------------------------------

data FailureToSupportPositiveMeansNegativePermission : Set where

data FailureToSupportNegativeMeansPositivePermission : Set where

failureToSupportPositiveDoesNotMeanNegative :
  FailureToSupportPositiveMeansNegativePermission → ⊥
failureToSupportPositiveDoesNotMeanNegative ()

failureToSupportNegativeDoesNotMeanPositive :
  FailureToSupportNegativeMeansPositivePermission → ⊥
failureToSupportNegativeDoesNotMeanPositive ()

------------------------------------------------------------------------
-- Balanced-ternary involution gives the expected polarity geometry while fixing
-- the unresolved centre.
------------------------------------------------------------------------

positiveInvertsToNegative : inv pos ≡ neg
positiveInvertsToNegative = refl

negativeInvertsToPositive : inv neg ≡ pos
negativeInvertsToPositive = refl

unresolvedIsFixedByInversion : inv zer ≡ zer
unresolvedIsFixedByInversion = refl

record DirectionalEvidenceBoundary : Set where
  constructor directional-evidence-boundary
  field
    failureToSupportPositiveIsNegativeEvidence : Bool
    failureToSupportNegativeIsPositiveEvidence : Bool
    unresolvedIsDistinctFromEitherDirection : Bool
    directionalCounterevidenceRequiresWitness : Bool

canonicalDirectionalEvidenceBoundary : DirectionalEvidenceBoundary
canonicalDirectionalEvidenceBoundary =
  directional-evidence-boundary false false true true
