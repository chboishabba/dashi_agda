module DASHI.Core.SelectiveAuthorityCertificateExact where

------------------------------------------------------------------------
-- SELECTIVE AUTHORITY != NUMERICAL CERTIFICATION
--
-- This module isolates the Gate-0 pattern exposed concretely by SeaMeInIt and
-- reusable in Animalexic/LES: computation may produce a certified candidate,
-- but a separate policy decides whether it is promoted, held/abstained, or
-- rejected.  Abstention may preserve an independently valid anchor.
--
-- Literature calibration:
--
-- J. Hendrickx et al.,
-- "Machine learning with a reject option: a survey", Machine Learning (2024).
-- DOI: 10.1007/s10994-024-06534-x.
--
-- Richard H. Byrd, Peihuang Lu, Jorge Nocedal, Ciyou Zhu,
-- "Algorithm 778: L-BFGS-B: Fortran Subroutines for Large-Scale Bound-
-- Constrained Optimization", ACM TOMS 23(4), 1997.
-- DOI: 10.1145/279232.279236.
--
-- These references motivate selective/reject decisions and projected/KKT-style
-- numerical certificates.  They do not prove a domain authority policy.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed

------------------------------------------------------------------------
-- A numerical certificate describes a computation.  It intentionally carries
-- no promotion constructor.
------------------------------------------------------------------------

record NumericalCandidateCertificate (Candidate : Set) : Set₁ where
  constructor numericalCandidateCertificate
  field
    candidate : Candidate
    solver : String
    residual : Nat
    tolerance : Nat
    residualWithinTolerance : Set
    activeConstraintSummary : List String
    evidenceReferences : List String

open NumericalCandidateCertificate public

------------------------------------------------------------------------
-- Selection result preserves the distinction between an authorised candidate,
-- fallback anchor, and complete rejection.
------------------------------------------------------------------------

data CanonicalSelection (Candidate Anchor : Set) : Set where
  selectedCandidate : Candidate → CanonicalSelection Candidate Anchor
  selectedAnchor : Anchor → CanonicalSelection Candidate Anchor
  selectedNone : CanonicalSelection Candidate Anchor

record SelectiveAuthority
    (Input Candidate Anchor : Set) : Set₁ where
  constructor selectiveAuthority
  field
    anchor : Input → Anchor
    authorize : Input → Candidate → Governed.AuthorityDecision
    policyReference : String

open SelectiveAuthority public

selectCanonical :
  ∀ {Input Candidate Anchor} →
  SelectiveAuthority Input Candidate Anchor →
  Input → Candidate → CanonicalSelection Candidate Anchor
selectCanonical authority input candidate with authorize authority input candidate
... | Governed.promote = selectedCandidate candidate
... | Governed.abstain = selectedAnchor (anchor authority input)
... | Governed.reject = selectedNone

promoteSelectsCandidate :
  ∀ {Input Candidate Anchor}
    (authority : SelectiveAuthority Input Candidate Anchor)
    (input : Input) (candidate : Candidate) →
  authorize authority input candidate ≡ Governed.promote →
  selectCanonical authority input candidate ≡ selectedCandidate candidate
promoteSelectsCandidate authority input candidate decision
  rewrite decision = refl

abstainSelectsAnchor :
  ∀ {Input Candidate Anchor}
    (authority : SelectiveAuthority Input Candidate Anchor)
    (input : Input) (candidate : Candidate) →
  authorize authority input candidate ≡ Governed.abstain →
  selectCanonical authority input candidate
  ≡ selectedAnchor (anchor authority input)
abstainSelectsAnchor authority input candidate decision
  rewrite decision = refl

rejectSelectsNone :
  ∀ {Input Candidate Anchor}
    (authority : SelectiveAuthority Input Candidate Anchor)
    (input : Input) (candidate : Candidate) →
  authorize authority input candidate ≡ Governed.reject →
  selectCanonical authority input candidate ≡ selectedNone
rejectSelectsNone authority input candidate decision
  rewrite decision = refl

------------------------------------------------------------------------
-- The separation itself is theorem-shaped: a numerical certificate can be
-- consumed by a policy, but there is no constructor that turns it into a
-- promotion witness without the independent authority decision.
------------------------------------------------------------------------

record AuthorisedCandidate
    {Input Candidate Anchor : Set}
    (authority : SelectiveAuthority Input Candidate Anchor)
    (input : Input)
    (certificate : NumericalCandidateCertificate Candidate) : Set where
  constructor authorisedCandidate
  field
    promoted :
      authorize authority input (candidate certificate) ≡ Governed.promote

open AuthorisedCandidate public

certifiedAndAuthorisedSelectsCandidate :
  ∀ {Input Candidate Anchor}
    {authority : SelectiveAuthority Input Candidate Anchor}
    {input : Input}
    {certificate : NumericalCandidateCertificate Candidate} →
  AuthorisedCandidate authority input certificate →
  selectCanonical authority input (candidate certificate)
  ≡ selectedCandidate (candidate certificate)
certifiedAndAuthorisedSelectsCandidate witness =
  promoteSelectsCandidate _ _ _ (promoted witness)

record CertificateAuthorityBoundary : Set where
  constructor certificateAuthorityBoundary
  field
    numericalConvergenceIsNotAuthority : Bool
    abstentionIsNotRejection : Bool
    abstentionMayPreserveIndependentAnchor : Bool
    rejectOptionPolicyMustBeDomainScoped : Bool
    solverResidualDoesNotValidateObservationModel : Bool

canonicalCertificateAuthorityBoundary : CertificateAuthorityBoundary
canonicalCertificateAuthorityBoundary =
  certificateAuthorityBoundary true true true true true
