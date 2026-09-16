module DASHI.Physics.Closure.NSABPortabilityBidiStatusExact where

------------------------------------------------------------------------
-- A/B BIDIRECTIONAL PORTABILITY AUDIT
--
-- A = unforced whole-space R^3.
-- B = unforced periodic T^3.
--
-- This owner is deliberately non-promoting.  It does NOT prove B -> A or
-- A -> B.  It keeps A active as a portability consumer while B remains the
-- current proof-discovery lane.  Every B theorem family is to be factored into
--
--   domain-independent analytic core
--   + torus/lattice/cutoff realization
--   + explicit whole-space transport obligations.
--
-- The purpose is bidirectional control:
--
--   B -> A: ask which paid B ingredients survive after quotienting torus-only
--           structure;
--   A -> B: ask which whole-space formulations reveal that a current B lemma
--           is accidentally over-specialized to the lattice.
--
-- Neither direction imports theorem authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

data PortabilityClass : Set where
  domainIndependentCandidate
  torusSpecificRealization
  mixedNeedsFactorization
  unresolvedWholeSpaceTransport : PortabilityClass

record ABPortabilityCoordinate : Set where
  constructor ab-portability-coordinate
  field
    owner : String
    bRole : String
    portabilityClass : PortabilityClass
    aQuestion : String
    sameObjectTransportObserved : Bool

open ABPortabilityCoordinate public

coordinates : List ABPortabilityCoordinate
coordinates =
  ab-portability-coordinate
    "R104 signed Abel/layer-cake algebra"
    "finite signed production decomposition"
    domainIndependentCandidate
    "Reformulate on a continuous radial/scale measure without finite torus enumeration."
    false
  ∷ ab-portability-coordinate
    "R98 packet-boundary cancellation"
    "exact internal/external packet cancellation before majorization"
    mixedNeedsFactorization
    "Separate selector/cancellation algebra from finite Fourier packet enumeration."
    false
  ∷ ab-portability-coordinate
    "#957 S2b2 low/collar/remote split"
    "quantitative phase-production geometry"
    torusSpecificRealization
    "Replace shellIndex/cutoff-mode packet geometry by an R^3 Littlewood-Paley or radial-frequency realization."
    false
  ∷ ab-portability-coordinate
    "R291/R573 signed Hermitian linearization"
    "signed vector/scalar cancellation ordering"
    domainIndependentCandidate
    "Check transport to the whole-space Fourier integral carrier before any norm majorization."
    false
  ∷ ab-portability-coordinate
    "R568/R572/R503 commutator compiler"
    "terminal periodic commutator route"
    mixedNeedsFactorization
    "Factor finite-lattice/output-fibre bookkeeping from the underlying commutator spacetime estimate."
    false
  ∷ []

bToAImplicationAllowed : Bool
bToAImplicationAllowed = false

aToBImplicationAllowed : Bool
aToBImplicationAllowed = false

bPhaseAnalyticCoreCandidateTracked : Bool
bPhaseAnalyticCoreCandidateTracked = true

bCommAnalyticCoreCandidateTracked : Bool
bCommAnalyticCoreCandidateTracked = true

torusSpecificRealizationSeparated : Bool
torusSpecificRealizationSeparated = true

wholeSpaceTransportObserved : Bool
wholeSpaceTransportObserved = false

aPortabilityAuditActive : Bool
aPortabilityAuditActive = true

bToAImplicationAllowedIsFalse : bToAImplicationAllowed ≡ false
bToAImplicationAllowedIsFalse = refl

aToBImplicationAllowedIsFalse : aToBImplicationAllowed ≡ false
aToBImplicationAllowedIsFalse = refl

bPhaseAnalyticCoreCandidateTrackedIsTrue :
  bPhaseAnalyticCoreCandidateTracked ≡ true
bPhaseAnalyticCoreCandidateTrackedIsTrue = refl

bCommAnalyticCoreCandidateTrackedIsTrue :
  bCommAnalyticCoreCandidateTracked ≡ true
bCommAnalyticCoreCandidateTrackedIsTrue = refl

torusSpecificRealizationSeparatedIsTrue :
  torusSpecificRealizationSeparated ≡ true
torusSpecificRealizationSeparatedIsTrue = refl

wholeSpaceTransportObservedIsFalse :
  wholeSpaceTransportObserved ≡ false
wholeSpaceTransportObservedIsFalse = refl

aPortabilityAuditActiveIsTrue : aPortabilityAuditActive ≡ true
aPortabilityAuditActiveIsTrue = refl
