module DASHI.Core.RelationalTransportDescentSheafExact where

------------------------------------------------------------------------
-- TRANSPORT-AWARE RELATIONAL DESCENT
--
-- DASHI CONTRIBUTION
--
-- This is the missing bridge between the strict-equality triadic cover and
-- relationship-indexed self transport.  Matching across overlaps is witnessed
-- by typed transports, not by literal equality of local self-sections.
--
-- This is a bounded stack-like descent interface.  It is NOT promoted to a
-- fully certified higher stack, groupoid object, or empirical psychological
-- theorem merely by analogy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RelationalSelfDescentExact as Transport
import DASHI.Foundations.RelationalStageTwelveSiteExact as Cover

record TransportAgreement (State : Set) : Set₁ where
  constructor transport-agreement
  field
    left right : State
    transport : Transport.TypedTransport State
    transportedLeftEqualsRight :
      Transport.forward transport left ≡ right
    agreementReceipt : String

open TransportAgreement public

record TransportMatchingFamily (State : Set) : Set₁ where
  constructor transport-matching-family
  field
    localAB localBC localCA : State
    agreementAtA : TransportAgreement State
    agreementAtB : TransportAgreement State
    agreementAtC : TransportAgreement State

open TransportMatchingFamily public

record TransportRelationalDescent (State Global : Set) : Set₁ where
  field
    glue :
      TransportMatchingFamily State →
      Global

    restrictAB : Global → State
    restrictBC : Global → State
    restrictCA : Global → State

    recoverAB :
      (matching : TransportMatchingFamily State) →
      restrictAB (glue matching) ≡ localAB matching

    recoverBC :
      (matching : TransportMatchingFamily State) →
      restrictBC (glue matching) ≡ localBC matching

    recoverCA :
      (matching : TransportMatchingFamily State) →
      restrictCA (glue matching) ≡ localCA matching

    holonomyResidual :
      TransportMatchingFamily State →
      Transport.HolonomyResidual

    descentReceipt : String

open TransportRelationalDescent public

------------------------------------------------------------------------
-- Strict cover compatibility is sufficient but not definitionally necessary.
------------------------------------------------------------------------

data LiteralEqualityRequiredForEveryOverlap : Set where
data TransportMatchingErasesHolonomy : Set where
data StackLikeInterfaceIsFullyCertifiedHigherStack : Set where

literalEqualityIsNotRequiredByTransportInterface :
  LiteralEqualityRequiredForEveryOverlap → ⊥
literalEqualityIsNotRequiredByTransportInterface ()

transportMatchingDoesNotEraseHolonomy :
  TransportMatchingErasesHolonomy → ⊥
transportMatchingDoesNotEraseHolonomy ()

stackLikeInterfaceDoesNotPromoteToHigherStack :
  StackLikeInterfaceIsFullyCertifiedHigherStack → ⊥
stackLikeInterfaceDoesNotPromoteToHigherStack ()

record RelationalTransportDescentBoundary : Set where
  constructor relational-transport-descent-boundary
  field
    strictEqualityCoverStillAvailable : Bool
    matchingMayUseTypedTransport : Bool
    transportEvidenceRetained : Bool
    holonomyResidualRetained : Bool
    stackLikeMeansCertifiedHigherStack : Bool
    empiricalRelationalSelfTheorySuppliesThisStructure : Bool

canonicalRelationalTransportDescentBoundary :
  RelationalTransportDescentBoundary
canonicalRelationalTransportDescentBoundary =
  relational-transport-descent-boundary true true true true false false
