module DASHI.Mathematics.Complexity.PNotEqualsNPBranchingProgramSourceAttributionExact where

------------------------------------------------------------------------
-- EXTERNAL BRANCHING-PROGRAM / SELF-REFERENCE SOURCE ATTRIBUTION
--
-- Repository attribution rule:
--
--   external source claim
--     != DASHI formal reconstruction
--     != DASHI cross-module inference
--     != new DASHI theorem.
--
-- These coordinates document research lineage only.  No theorem in the P != NP
-- lane depends on these strings for proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record ExternalComplexitySource : Set where
  constructor external-complexity-source
  field
    authors : String
    title : String
    identifier : String
    sourceRole : String
    boundedClaim : String

open ExternalComplexitySource public

liMcKenzieSubfunctionMeasureSource :
  ExternalComplexitySource
liMcKenzieSubfunctionMeasureSource =
  external-complexity-source
    "Yaqiao Li; Pierre McKenzie"
    "Perspective on complexity measures targeting read-once branching programs"
    "doi:10.1016/j.ic.2024.105230"
    "external complexity-measure lineage"
    "Studies read-once branching-program complexity measures, including measures derived from counting subfunctions; does not supply DASHI FutureEquivalent or Q1 theorems."

bolligWegenerOrderingSource :
  ExternalComplexitySource
bolligWegenerOrderingSource =
  external-complexity-source
    "Beate Bollig; Ingo Wegener"
    "Improving the Variable Ordering of OBDDs Is NP-Complete"
    "doi:10.1109/12.537122"
    "external variable-ordering hardness lineage"
    "Proves the stated OBDD variable-ordering improvement problem NP-complete; does not prove hardness of the special DASHI self-diagonal ordering problem."

jonesOperationalSelfReferenceSource :
  ExternalComplexitySource
jonesOperationalSelfReferenceSource =
  external-complexity-source
    "Neil D. Jones"
    "A Swiss Pocket Knife for Computability"
    "arXiv:1309.5128"
    "external operational self-reference lineage"
    "Studies operational and complexity-oriented implementations of s-m-n, self-interpretation, and Kleene's second recursion theorem; does not pay the SAT-specific DASHI body semantics."

record AttributionFirewall : Set where
  constructor attribution-firewall
  field
    externalClaimsRemainExternal : Bool
    dashiReconstructionIndependent : Bool
    crossModuleInferenceSeparate : Bool
    externalMetadataCreatesProofAuthority : Bool

open AttributionFirewall public

pNotEqualsNPAttributionFirewall :
  AttributionFirewall
pNotEqualsNPAttributionFirewall =
  attribution-firewall
    true
    true
    true
    false

externalMetadataDoesNotCreateProofAuthority :
  externalMetadataCreatesProofAuthority
    pNotEqualsNPAttributionFirewall
  ≡
  false
externalMetadataDoesNotCreateProofAuthority =
  refl
