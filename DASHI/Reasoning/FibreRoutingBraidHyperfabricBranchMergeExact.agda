module DASHI.Reasoning.FibreRoutingBraidHyperfabricBranchMergeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Compatibility owner retained for existing imports.  The canonical ontology
-- now lives in LocalFibreHyperfabricExact: fibres are local type-family data
-- over an incidence base, not members of a global event-indexed branch tree.
import DASHI.Reasoning.LocalFibreHyperfabricExact as Local

record BranchEventCompatibilityBoundary : Set where
  constructor branch-event-compatibility-boundary
  field
    branchEventGraphIsCanonicalFibreOntology : Bool
    branchEventGraphIsCanonicalFibreOntologyIsFalse :
      branchEventGraphIsCanonicalFibreOntology ≡ false

    localFibreHyperfabricIsCanonical : Bool
    localFibreHyperfabricIsCanonicalIsTrue :
      localFibreHyperfabricIsCanonical ≡ true

    legacyEightStillOnlyOneDeclaredChart : Bool
    legacyEightStillOnlyOneDeclaredChartIsTrue :
      legacyEightStillOnlyOneDeclaredChart ≡ true

canonicalBranchEventCompatibilityBoundary : BranchEventCompatibilityBoundary
canonicalBranchEventCompatibilityBoundary =
  branch-event-compatibility-boundary false refl true refl true refl

canonicalLocalHyperfabricBoundary : Local.MaleCNSChartBoundary
canonicalLocalHyperfabricBoundary = Local.canonicalMaleCNSChartBoundary
