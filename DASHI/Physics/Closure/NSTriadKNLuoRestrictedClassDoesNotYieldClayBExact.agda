module DASHI.Physics.Closure.NSTriadKNLuoRestrictedClassDoesNotYieldClayBExact where

------------------------------------------------------------------------
-- SOURCE-SCOPE CONTEXT
--
-- Author: Andrea Cavazzini.
-- Title: "Symmetry, Triadic Sparsity, and Global Regularity for Kida-Pelz
-- Navier-Stokes Flows".
-- DOI: 10.5281/zenodo.19180827.
-- Status: restricted symmetry class and viscosity threshold; not a claim of
-- the unrestricted Fefferman periodic alternative (B).
--
-- PURPOSE
--
-- Prove by an inhabited finite model that a theorem for one restricted datum
-- class does not, by logic alone, produce a theorem for every smooth periodic
-- datum.  A bridge from the unrestricted carrier into the restricted class or
-- a separate theorem for the complement is mathematically load-bearing.
------------------------------------------------------------------------

open import Relation.Nullary.Negation using (¬_)


data PeriodicDatum : Set where
  kidaPelzSymmetricDatum : PeriodicDatum
  unrestrictedDatum : PeriodicDatum


data GlobalSmoothSolution : PeriodicDatum → Set where
  symmetricSolution :
    GlobalSmoothSolution kidaPelzSymmetricDatum

RestrictedSymmetryTheorem : Set
RestrictedSymmetryTheorem =
  GlobalSmoothSolution kidaPelzSymmetricDatum

UniversalPeriodicTheorem : Set
UniversalPeriodicTheorem =
  (datum : PeriodicDatum) → GlobalSmoothSolution datum

restrictedSymmetryTheoremHolds : RestrictedSymmetryTheorem
restrictedSymmetryTheoremHolds =
  symmetricSolution

restrictedSymmetryDoesNotLogicallyYieldUniversalTheorem :
  ¬ UniversalPeriodicTheorem
restrictedSymmetryDoesNotLogicallyYieldUniversalTheorem universal
  with universal unrestrictedDatum
... | ()

record RestrictedClassScopeWitness : Set where
  constructor restrictedClassScopeWitness
  field
    restrictedTheoremInhabited : RestrictedSymmetryTheorem
    universalTheoremNotObtained : ¬ UniversalPeriodicTheorem

canonicalRestrictedClassScopeWitness : RestrictedClassScopeWitness
canonicalRestrictedClassScopeWitness =
  restrictedClassScopeWitness
    restrictedSymmetryTheoremHolds
    restrictedSymmetryDoesNotLogicallyYieldUniversalTheorem
