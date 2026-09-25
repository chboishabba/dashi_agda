module DASHI.Reasoning.TrialecticLocalLogicQualificationExact where

------------------------------------------------------------------------
-- LOCAL LOGIC OVER RELATIONAL SECTIONS
--
-- DASHI CONTRIBUTION
--
-- Tetralemma/sixfold qualification lives over proposition-bearing local
-- sections.  It is not the base trialectic relation and does not globalise
-- merely because support and counter-support occur on different patches.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.TernarySynthesisLogicQualificationExact as Logic
import DASHI.Core.RelationalSelfDescentExact as Relational

record LocalQualifiedSection : Set where
  constructor local-qualified-section
  field
    patch : Relational.RelationalPatch
    propositionReference : String
    scopeReference : String
    provenanceReference : String
    qualification : Logic.SixfoldQualifiedSynthesis

open LocalQualifiedSection public

record SamePropositionTransport
    (left right : LocalQualifiedSection) : Set where
  constructor same-proposition-transport
  field
    sameProposition :
      propositionReference left ≡ propositionReference right
    sameScope :
      scopeReference left ≡ scopeReference right
    transportReceipt : String

open SamePropositionTransport public

data CrossPatchSupportAutomaticallyGlobalises : Set where

crossPatchSupportDoesNotAutomaticallyGlobalise :
  CrossPatchSupportAutomaticallyGlobalises → ⊥
crossPatchSupportDoesNotAutomaticallyGlobalise ()

record TrialecticLocalLogicBoundary : Set where
  constructor trialectic-local-logic-boundary
  field
    tetralemmaIsBaseTrialecticCarrier : Bool
    sixfoldStatusIsRelationalPatch : Bool
    supportOnOnePatchAndCounterSupportOnAnotherCreatesGlobalBoth : Bool
    samePropositionScopeAndTransportRequiredBeforeGlobalJoin : Bool
    logicalQualificationRetainsPriorCarrier : Bool

canonicalTrialecticLocalLogicBoundary : TrialecticLocalLogicBoundary
canonicalTrialecticLocalLogicBoundary =
  trialectic-local-logic-boundary false false false true true
