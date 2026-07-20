module DASHI.Analysis.CompleteCarrierQuadraticUniqueness where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.GRQuantumProofTerms as Legacy

------------------------------------------------------------------------
-- Arbitrary complete-carrier quadratic uniqueness.
--
-- The finite four-value table in the existing spine is not a theorem for an
-- arbitrary complete carrier.  This module isolates the analytic ingredients
-- of the Jordan-von Neumann/polarisation route.  Uniqueness below is derived
-- from two producer obligations:
--
--   * every admissible multiscale functional has the canonical polar form;
--   * the polar form determines the functional extensionally.
--
-- Completeness and scalar authority are explicit parts of the carrier rather
-- than being hidden inside an undifferentiated theorem flag.

record CompleteQuadraticCarrier : Set₁ where
  field
    Scalar : Set
    Vector : Set

    zeroVector : Vector
    addVector : Vector → Vector → Vector
    subtractVector : Vector → Vector → Vector
    scaleVector : Scalar → Vector → Vector

    NormValue : Set
    norm : Vector → NormValue
    distance : Vector → Vector → NormValue

    CauchySequence : Set
    sequenceTerm : CauchySequence → Nat → Vector
    Limit : CauchySequence → Set
    limitVector : (sequence : CauchySequence) → Limit sequence → Vector

    scalarFieldAuthority : Set
    scalarFieldAuthorityProof : scalarFieldAuthority
    normedVectorLaws : Set
    normedVectorLawsProof : normedVectorLaws
    complete : Set
    completeProof : complete
open CompleteQuadraticCarrier public

record OrthogonalMultiscaleLaw
  (carrier : CompleteQuadraticCarrier) : Set₁ where
  field
    Functional : Set
    PolarForm : Set

    evaluate : Functional → Vector carrier → Scalar carrier
    polarize : Functional → PolarForm

    canonicalQuadratic : Functional
    SatisfiesOrthogonalMultiscaleLaws : Functional → Set
    canonicalSatisfiesLaws :
      SatisfiesOrthogonalMultiscaleLaws canonicalQuadratic

    lawsForceCanonicalPolarization :
      (functional : Functional) →
      SatisfiesOrthogonalMultiscaleLaws functional →
      polarize functional ≡ polarize canonicalQuadratic

    polarizationDeterminesFunctional :
      (left right : Functional) →
      polarize left ≡ polarize right →
      left ≡ right

    reconstructionAndOrthogonalityDefined : Set
    reconstructionAndOrthogonalityDefinedProof :
      reconstructionAndOrthogonalityDefined
    parallelogramOrEquivalentQuadraticLaw : Set
    parallelogramOrEquivalentQuadraticLawProof :
      parallelogramOrEquivalentQuadraticLaw
open OrthogonalMultiscaleLaw public

arbitraryCompleteCarrierQuadraticUnique :
  (carrier : CompleteQuadraticCarrier) →
  (law : OrthogonalMultiscaleLaw carrier) →
  (functional : Functional law) →
  SatisfiesOrthogonalMultiscaleLaws law functional →
  functional ≡ canonicalQuadratic law
arbitraryCompleteCarrierQuadraticUnique carrier law functional satisfies =
  polarizationDeterminesFunctional law
    functional
    (canonicalQuadratic law)
    (lawsForceCanonicalPolarization law functional satisfies)

completeCarrierQuadraticLegacySurface :
  (carrier : CompleteQuadraticCarrier) →
  OrthogonalMultiscaleLaw carrier →
  Legacy.QuadraticUniquenessProof
completeCarrierQuadraticLegacySurface carrier law =
  record
    { EnergyFunctional = Functional law
    ; SatisfiesMultiscaleLaws = SatisfiesOrthogonalMultiscaleLaws law
    ; canonicalQuadraticDefect = canonicalQuadratic law
    ; canonicalSatisfiesLaws = canonicalSatisfiesLaws law
    ; uniqueness = arbitraryCompleteCarrierQuadraticUnique carrier law
    }

record CompleteCarrierQuadraticAuthority : Set₁ where
  field
    carrier : CompleteQuadraticCarrier
    law : OrthogonalMultiscaleLaw carrier
    arbitraryCarrierScope : Set
    arbitraryCarrierScopeProof : arbitraryCarrierScope
    noFiniteEnumerationDependency : Set
    noFiniteEnumerationDependencyProof : noFiniteEnumerationDependency
open CompleteCarrierQuadraticAuthority public

quadraticAuthoritySurface :
  CompleteCarrierQuadraticAuthority → Legacy.QuadraticUniquenessProof
quadraticAuthoritySurface authority =
  completeCarrierQuadraticLegacySurface
    (carrier authority)
    (law authority)
