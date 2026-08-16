module DASHI.Foundations.FiniteRepresentationRestrictionCore where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Give the representation-reduction lane requested by the SSP synthesis:
--
--   ContinuousIrrep
--     → FiniteRestriction
--     → BranchingSpectrum
--     → FixedSpaceSpectrum.
--
-- This is deliberately representation-neutral.  A concrete restriction must
-- supply a finite irrep family, multiplicities, exact dimension conservation,
-- and whatever fixed-subspace probes it claims.  The core does not infer an
-- Ogg/Monster/Hecke theorem from a matching dimension or a clean branching.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

sumWeighted :
  {Irrep : Set} →
  List Irrep →
  (Irrep → Nat) →
  (Irrep → Nat) →
  Nat
sumWeighted [] dimension multiplicity = 0
sumWeighted (irrep ∷ irreps) dimension multiplicity =
  multiplicity irrep * dimension irrep
  + sumWeighted irreps dimension multiplicity

record ContinuousIrrep : Set where
  constructor continuous-irrep
  field
    highestWeight : Nat
    irrepDimension : Nat
    carrierLabel : String
    sourceNote : String

open ContinuousIrrep public

record FiniteIrrepFamily : Set₁ where
  constructor finite-irrep-family
  field
    Irrep : Set
    irreps : List Irrep
    finiteIrrepDimension : Irrep → Nat
    familyLabel : String

open FiniteIrrepFamily public

record BranchingSpectrum
    (source : ContinuousIrrep)
    (target : FiniteIrrepFamily) : Set where
  constructor branching-spectrum
  field
    multiplicity : Irrep target → Nat
    dimensionConserved :
      sumWeighted
        (irreps target)
        (finiteIrrepDimension target)
        multiplicity
      ≡ ContinuousIrrep.irrepDimension source
    branchingReceipt : String

open BranchingSpectrum public

record FixedSpaceSpectrum : Set₁ where
  constructor fixed-space-spectrum
  field
    Probe : Set
    fixedDimension : Probe → Nat
    probeLabel : Probe → String
    fixedSpaceReceipt : String

open FixedSpaceSpectrum public

record FiniteRestriction : Set₁ where
  constructor finite-restriction
  field
    sourceIrrep : ContinuousIrrep
    targetFamily : FiniteIrrepFamily
    branching : BranchingSpectrum sourceIrrep targetFamily
    fixedSpaces : FixedSpaceSpectrum
    restrictionReceipt : String

open FiniteRestriction public

record RepresentationRestrictionAuthorityBoundary : Set where
  field
    dimensionEqualityAloneImpliesRestriction : Bool
    dimensionEqualityAloneImpliesRestrictionIsFalse :
      dimensionEqualityAloneImpliesRestriction ≡ false

    branchingSpectrumMayBeComputedExactly : Bool
    branchingSpectrumMayBeComputedExactlyIsTrue :
      branchingSpectrumMayBeComputedExactly ≡ true

    fixedSpaceSpectrumMayBeComputedExactly : Bool
    fixedSpaceSpectrumMayBeComputedExactlyIsTrue :
      fixedSpaceSpectrumMayBeComputedExactly ≡ true

    finiteRestrictionAutomaticallyExplainsOggSet : Bool
    finiteRestrictionAutomaticallyExplainsOggSetIsFalse :
      finiteRestrictionAutomaticallyExplainsOggSet ≡ false

    finiteRestrictionAutomaticallyConstructsHeckeIntertwiner : Bool
    finiteRestrictionAutomaticallyConstructsHeckeIntertwinerIsFalse :
      finiteRestrictionAutomaticallyConstructsHeckeIntertwiner ≡ false

canonicalRepresentationRestrictionAuthorityBoundary :
  RepresentationRestrictionAuthorityBoundary
canonicalRepresentationRestrictionAuthorityBoundary =
  record
    { dimensionEqualityAloneImpliesRestriction = false
    ; dimensionEqualityAloneImpliesRestrictionIsFalse = refl
    ; branchingSpectrumMayBeComputedExactly = true
    ; branchingSpectrumMayBeComputedExactlyIsTrue = refl
    ; fixedSpaceSpectrumMayBeComputedExactly = true
    ; fixedSpaceSpectrumMayBeComputedExactlyIsTrue = refl
    ; finiteRestrictionAutomaticallyExplainsOggSet = false
    ; finiteRestrictionAutomaticallyExplainsOggSetIsFalse = refl
    ; finiteRestrictionAutomaticallyConstructsHeckeIntertwiner = false
    ; finiteRestrictionAutomaticallyConstructsHeckeIntertwinerIsFalse = refl
    }
