module DASHI.Biology.Levin.SubstrateIndependentAgency where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Substrate-independent agency is indexed by capacities in an explicit
-- problem space.  It does not erase embodiment and does not promote
-- consciousness or moral status by definition.

record AgencyProfile : Set where
  field
    sensesEnvironment : Bool
    retainsHistory : Bool
    evaluatesOutcomes : Bool
    selectsActions : Bool
    correctsTowardGoal : Bool
    spansMultipleScales : Bool

open AgencyProfile public

record SubstrateIndependentAgencyBoundary : Set where
  field
    canonicalProfile : AgencyProfile
    problemSpaceExplicit : Bool
    interventionLanguageExplicit : Bool
    originIndependentComparison : Bool
    substrateIndependentNotSubstrateIrrelevant : Bool
    agencyNotConsciousness : Bool
    agencyNotMoralStatus : Bool
    candidateOnly : Bool
    reading : String

open SubstrateIndependentAgencyBoundary public

canonicalSubstrateIndependentAgencyBoundary :
  SubstrateIndependentAgencyBoundary
canonicalSubstrateIndependentAgencyBoundary = record
  { canonicalProfile = record
      { sensesEnvironment = true
      ; retainsHistory = true
      ; evaluatesOutcomes = true
      ; selectsActions = true
      ; correctsTowardGoal = true
      ; spansMultipleScales = true
      }
  ; problemSpaceExplicit = true
  ; interventionLanguageExplicit = true
  ; originIndependentComparison = true
  ; substrateIndependentNotSubstrateIrrelevant = true
  ; agencyNotConsciousness = false
  ; agencyNotMoralStatus = false
  ; candidateOnly = true
  ; reading =
      "Agency is compared through typed sensing, memory, evaluation, action, and correction capacities in an explicit problem space; origin and material do not fix the comparison, but embodiment remains causally relevant"
  }

canonicalAgencyNotConsciousness :
  agencyNotConsciousness canonicalSubstrateIndependentAgencyBoundary ≡ false
canonicalAgencyNotConsciousness = refl
