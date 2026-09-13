module DASHI.Physics.Gravity.Penrose1965NullGeodesicIncompletenessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Laws.SpacetimeMechanicsLaws as Mechanics
import DASHI.Promotion.GRBoundaryClarification as GRBoundary

------------------------------------------------------------------------
-- Penrose 1965 theorem-boundary owner.
--
-- This module records the source, hypotheses, conclusion kind, and the
-- interpretation firewalls needed by downstream DASHI consumers.  It does
-- not re-prove the continuum Lorentzian theorem inside Agda.  In particular,
-- "singularity" is not represented as a point of the spacetime manifold and
-- is not equated with divergence of a curvature scalar.
------------------------------------------------------------------------

Penrose1965SourceReceipt : Source.AttributedSource
Penrose1965SourceReceipt =
  Source.mkDOISource
    "Roger Penrose"
    "Gravitational Collapse and Space-Time Singularities"
    "Physical Review Letters 14(3), 57-59"
    "1965"
    "10.1103/PhysRevLett.14.57"
    "https://doi.org/10.1103/PhysRevLett.14.57"
    Source.academicArticleSource
    "primary theorem source for the trapped-surface singularity theorem boundary; citation records provenance but does not import the proof"
    Source.publicAttribution

record CitationNonPromotionReceipt : Set where
  field
    citationImportsNoProof :
      Source.citationImportsProof Penrose1965SourceReceipt ≡ false
    citationCreatesNoAuthority :
      Source.citationCreatesAuthority Penrose1965SourceReceipt ≡ false

open CitationNonPromotionReceipt public

citationImportsNeitherProofNorAuthority : CitationNonPromotionReceipt
citationImportsNeitherProofNorAuthority = record
  { citationImportsNoProof = refl
  ; citationCreatesNoAuthority = refl
  }

data PenroseHypothesisKind : Set where
  nonCompactCauchyHypersurfaceHypothesis : PenroseHypothesisKind
  closedTrappedSurfaceHypothesis : PenroseHypothesisKind
  nullConvergenceHypothesis : PenroseHypothesisKind

data PenroseConclusionKind : Set where
  nullGeodesicIncompletenessConclusion : PenroseConclusionKind

record Penrose1965TheoremBoundary : Set where
  field
    cauchySurfaceHypothesis : PenroseHypothesisKind
    trappedSurfaceHypothesis : PenroseHypothesisKind
    convergenceHypothesis : PenroseHypothesisKind
    nullConvergenceCondition : String
    theoremConclusion : PenroseConclusionKind
    theoremConclusionMeaning : String
    continuumAuthorityRequired : Bool
    continuumAuthorityRequiredIsTrue : continuumAuthorityRequired ≡ true
    theoremInternallyReproved : Bool
    theoremInternallyReprovedIsFalse : theoremInternallyReproved ≡ false

open Penrose1965TheoremBoundary public

canonicalPenrose1965TheoremBoundary : Penrose1965TheoremBoundary
canonicalPenrose1965TheoremBoundary = record
  { cauchySurfaceHypothesis = nonCompactCauchyHypersurfaceHypothesis
  ; trappedSurfaceHypothesis = closedTrappedSurfaceHypothesis
  ; convergenceHypothesis = nullConvergenceHypothesis
  ; nullConvergenceCondition =
      "Ric(k,k) >= 0 for null tangent k, equivalently the null-convergence/focusing condition used by the theorem under the declared GR assumptions"
  ; theoremConclusion = nullGeodesicIncompletenessConclusion
  ; theoremConclusionMeaning =
      "under the theorem hypotheses, at least one null geodesic is inextendible after finite affine parameter; this is geodesic incompleteness, not a theorem that a singular point belongs to the manifold"
  ; continuumAuthorityRequired = true
  ; continuumAuthorityRequiredIsTrue = refl
  ; theoremInternallyReproved = false
  ; theoremInternallyReprovedIsFalse = refl
  }

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

record PenroseInterpretationBoundary : Set where
  field
    geodesicIncompletenessIsNotSingularPointInSpacetime : Bool
    geodesicIncompletenessIsNotSingularPointInSpacetimeIsTrue :
      geodesicIncompletenessIsNotSingularPointInSpacetime ≡ true

    incompletenessDoesNotRequireCurvatureScalarDivergence : Bool
    incompletenessDoesNotRequireCurvatureScalarDivergenceIsTrue :
      incompletenessDoesNotRequireCurvatureScalarDivergence ≡ true

    theoremDoesNotRequireSphericalSymmetry : Bool
    theoremDoesNotRequireSphericalSymmetryIsTrue :
      theoremDoesNotRequireSphericalSymmetry ≡ true

    theoremBoundaryDoesNotProveQuantumGravity : Bool
    theoremBoundaryDoesNotProveQuantumGravityIsTrue :
      theoremBoundaryDoesNotProveQuantumGravity ≡ true

    theoremBoundaryDoesNotSelectAUniqueGRFailureMechanism : Bool
    theoremBoundaryDoesNotSelectAUniqueGRFailureMechanismIsTrue :
      theoremBoundaryDoesNotSelectAUniqueGRFailureMechanism ≡ true

open PenroseInterpretationBoundary public

canonicalPenroseInterpretationBoundary : PenroseInterpretationBoundary
canonicalPenroseInterpretationBoundary = record
  { geodesicIncompletenessIsNotSingularPointInSpacetime = true
  ; geodesicIncompletenessIsNotSingularPointInSpacetimeIsTrue = refl
  ; incompletenessDoesNotRequireCurvatureScalarDivergence = true
  ; incompletenessDoesNotRequireCurvatureScalarDivergenceIsTrue = refl
  ; theoremDoesNotRequireSphericalSymmetry = true
  ; theoremDoesNotRequireSphericalSymmetryIsTrue = refl
  ; theoremBoundaryDoesNotProveQuantumGravity = true
  ; theoremBoundaryDoesNotProveQuantumGravityIsTrue = refl
  ; theoremBoundaryDoesNotSelectAUniqueGRFailureMechanism = true
  ; theoremBoundaryDoesNotSelectAUniqueGRFailureMechanismIsTrue = refl
  }

------------------------------------------------------------------------
-- Explicit reuse of existing repo-native GR/mechanics surfaces.
------------------------------------------------------------------------

existingSpacetimeDynamicsSurface : Set₁
existingSpacetimeDynamicsSurface = Mechanics.DifferentialGeometricDynamics

existingGRPromotionBoundarySurface : Set₁
existingGRPromotionBoundarySurface = GRBoundary.GRBoundaryClarificationIndex

penroseOwnerPromotesContinuumGR : Bool
penroseOwnerPromotesContinuumGR = false

penroseOwnerPromotesContinuumGRIsFalse :
  penroseOwnerPromotesContinuumGR ≡ false
penroseOwnerPromotesContinuumGRIsFalse = refl
