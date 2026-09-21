module DASHI.Law.NonFactorabilityRuntimeTheoremBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Law.ClosedIsNotAdequateExact as Closed

------------------------------------------------------------------------
-- Runtime checked-negative bridge.
--
-- The runtime may carry theorem module/ref/digest attribution, but the formal
-- content of a checked NonFactorability receipt is an actual
-- QueryAdequacyDefect inhabitant.  Metadata booleans are not constructors for
-- that inhabitant.
------------------------------------------------------------------------

record RuntimeNonFactorabilityCandidate : Set where
  constructor runtimeNonFactorabilityCandidate
  field
    queryRef : String
    projectionDigest : String
    theoremModuleRef : String
    theoremRef : String
    theoremArtifactDigest : String
    exactFibreCollisionClaim : Bool
    exactFibreCollisionClaimIsTrue :
      exactFibreCollisionClaim ≡ true
    runtimeClaimsCheckedDefect : Bool
    runtimeClaimsCheckedDefectIsFalse :
      runtimeClaimsCheckedDefect ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open RuntimeNonFactorabilityCandidate public

record KernelCheckedNonFactorability
    {State Observation QueryType Answer : Set}
    (project : State → Observation)
    (semantics : Query.QuerySemantics State QueryType Answer)
    (query : QueryType) : Set₁ where
  constructor kernelCheckedNonFactorability
  field
    runtimeCandidate : RuntimeNonFactorabilityCandidate
    defect :
      Query.QueryAdequacyDefect project semantics query
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open KernelCheckedNonFactorability public

checkedNonfactorabilityDefect :
  ∀ {State Observation QueryType Answer}
    {project : State → Observation}
    {semantics : Query.QuerySemantics State QueryType Answer}
    {query : QueryType} →
  KernelCheckedNonFactorability project semantics query →
  Query.QueryAdequacyDefect project semantics query
checkedNonfactorabilityDefect = defect

checkedNonfactorabilityBlocksFactorsThrough :
  ∀ {State Observation QueryType Answer}
    {project : State → Observation}
    {semantics : Query.QuerySemantics State QueryType Answer}
    {query : QueryType} →
  KernelCheckedNonFactorability project semantics query →
  Query.AdequateFor project semantics query →
  ⊥
checkedNonfactorabilityBlocksFactorsThrough
  {project = project} {semantics = semantics} {query = query} checked =
  Query.queryAdequacyDefectBlocksFactorisation
    {project = project}
    {semantics = semantics}
    {query = query}
    (checkedNonfactorabilityDefect checked)

demoRuntimeCandidate : RuntimeNonFactorabilityCandidate
demoRuntimeCandidate =
  runtimeNonFactorabilityCandidate
    "query:time-sensitive"
    "sha256:time-erased-projection"
    "DASHI.Law.ClosedIsNotAdequateExact"
    "timeErasureDefect"
    "agda-owner:closed-is-not-adequate"
    true refl
    false refl
    true refl
    false refl
    false refl

demoCheckedNonfactorability :
  KernelCheckedNonFactorability
    Closed.timeErasedProject
    Closed.timeSemantics
    Closed.asAtSensitiveQuery
demoCheckedNonfactorability =
  kernelCheckedNonFactorability
    demoRuntimeCandidate
    Closed.timeErasureDefect
    true refl
    false refl
    false refl

demoCheckedDefectRecovered :
  Query.QueryAdequacyDefect
    Closed.timeErasedProject
    Closed.timeSemantics
    Closed.asAtSensitiveQuery
demoCheckedDefectRecovered =
  checkedNonfactorabilityDefect demoCheckedNonfactorability

data MetadataExactFlagAutomaticallyDefect : Set where
data TheoremRefStringAutomaticallyDefect : Set where

metadataFlagCannotConstructDefect :
  MetadataExactFlagAutomaticallyDefect → ⊥
metadataFlagCannotConstructDefect ()

theoremRefCannotConstructDefect :
  TheoremRefStringAutomaticallyDefect → ⊥
theoremRefCannotConstructDefect ()

record NonFactorabilityRuntimeTheoremBridgeBoundary : Set where
  constructor nonFactorabilityRuntimeTheoremBridgeBoundary
  field
    exactFlagAloneIsQueryAdequacyDefect : Bool
    exactFlagAloneIsQueryAdequacyDefectIsFalse :
      exactFlagAloneIsQueryAdequacyDefect ≡ false

    theoremRefStringAloneIsQueryAdequacyDefect : Bool
    theoremRefStringAloneIsQueryAdequacyDefectIsFalse :
      theoremRefStringAloneIsQueryAdequacyDefect ≡ false

    checkedNegativeReceiptRequiresDefectInhabitant : Bool
    checkedNegativeReceiptRequiresDefectInhabitantIsTrue :
      checkedNegativeReceiptRequiresDefectInhabitant ≡ true

    checkedDefectBlocksFactorsThrough : Bool
    checkedDefectBlocksFactorsThroughIsTrue :
      checkedDefectBlocksFactorsThrough ≡ true

    checkedNegativeCreatesSemanticAuthority : Bool
    checkedNegativeCreatesSemanticAuthorityIsFalse :
      checkedNegativeCreatesSemanticAuthority ≡ false

    checkedNegativeCreatesClaimTruth : Bool
    checkedNegativeCreatesClaimTruthIsFalse :
      checkedNegativeCreatesClaimTruth ≡ false

open NonFactorabilityRuntimeTheoremBridgeBoundary public

canonicalNonFactorabilityRuntimeTheoremBridgeBoundary :
  NonFactorabilityRuntimeTheoremBridgeBoundary
canonicalNonFactorabilityRuntimeTheoremBridgeBoundary =
  nonFactorabilityRuntimeTheoremBridgeBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
