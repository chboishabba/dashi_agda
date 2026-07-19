module DASHI.Biology.Levin.GenericInterestingBehaviourCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.SeparableBoundaryPersistence as Persistence
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden
import DASHI.Biology.Levin.HolonomyReferenceFrameBoundary as Holonomy
import DASHI.Biology.Levin.PolycomputationBiologyAdapter as Poly

record GenericInterestingBehaviourCore : Set where
  field
    persistenceBoundary : Persistence.BoundaryPersistenceBoundary
    nonrecurrenceBoundary : Hidden.NonrecurrenceBoundary
    holonomyBoundary : Holonomy.HolonomyBoundary
    biologyAdapter : Poly.PolycomputationBiologyAdapter
    genericPersistenceIsNotUniversalIntelligenceTheorem : Bool
    interestingnessRequiresOperationalCriterion : Bool
    freeEnergyReadingRequiresModelWitness : Bool
    contextualityRequiresNoncommutingOperationalWitness : Bool
    candidateOnly : Bool
    interpretation : String

canonicalGenericInterestingBehaviourCore : GenericInterestingBehaviourCore
canonicalGenericInterestingBehaviourCore = record
  { persistenceBoundary = Persistence.canonicalBoundaryPersistenceBoundary
  ; nonrecurrenceBoundary = Hidden.canonicalNonrecurrenceBoundary
  ; holonomyBoundary = Holonomy.canonicalHolonomyBoundary
  ; biologyAdapter = Poly.canonicalPolycomputationBiologyAdapter
  ; genericPersistenceIsNotUniversalIntelligenceTheorem = true
  ; interestingnessRequiresOperationalCriterion = true
  ; freeEnergyReadingRequiresModelWitness = true
  ; contextualityRequiresNoncommutingOperationalWitness = true
  ; candidateOnly = true
  ; interpretation = "Sparse observable boundaries, hidden internal history, holonomy and projection-relative computation provide a candidate foundation for diverse biological behaviour without defining all persistence as intelligence"
  }
