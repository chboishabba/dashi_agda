module DASHI.Physics.YangMills.BalabanCMP119AnchoredNormalizedExpectationSourceExact where

------------------------------------------------------------------------
-- ROUND82: CMP119 ALREADY EXPANDS NORMALIZED LOCAL EXPECTATIONS
--          BY ANCHORED CONNECTED POLYMERS
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- SOURCE LOCATOR / MATHEMATICAL CONTENT
--
-- In Sect. 3, around equations (3.44)--(3.47), Bałaban treats expectation
-- values by expanding BOTH numerator and normalization denominator.  The
-- numerator contains a distinguished localization domain Z_0 carrying the
-- inserted bond/point.  The remaining denominator polymers exponentiate; after
-- subtraction of the denominator exponent and a Mayer re-expansion, the
-- normalized expectation is represented as a sum over domains X containing
-- that distinguished insertion.
--
-- The source then states that these anchored terms satisfy the same exponential
-- localization estimate as the boundary terms in (2.42), with the appropriate
-- small prefactor (O(p_1(g_k)) in the displayed application).  This is exactly
-- the connected/denominator-cancellation mechanism needed by the continuum
-- increment route.  It is stronger than merely knowing that the action density
-- itself has exponentially localized E/R/B terms.
--
-- This file gives that published result its own theorem boundary.  It does NOT
-- claim that an arbitrary repository observable is automatically one of the
-- source insertions.  The remaining same-object job is to place the ordinary
-- Schwinger and compact-support characteristic insertions inside the source
-- local analytic insertion class.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP119AnchoredNormalizedExpectationSource : Set₁ where
  field
    Scale Domain Anchor : Set

    -- Source localization coordinate d_j(X).
    sourceTreeDistance : Scale → Domain → ℚ

    -- A normalized expectation after the denominator has been exponentiated
    -- and cancelled as in (3.44)--(3.47).
    NormalizedExpectation : Scale → Anchor → Set
    AnchoredTerm : Scale → Anchor → Domain → Set

    containsAnchor : Anchor → Domain → Set

    -- Absolute-value / strong analytic seminorm used by the source estimate.
    magnitude : ∀ {scale anchor domain} →
      AnchoredTerm scale anchor domain → ℚ

    amplitude : Scale → ℚ
    sourceExponentialEnvelope : Scale → Domain → ℚ

    -- Equation-(3.47)-shaped representation: only domains carrying the
    -- distinguished insertion occur after normalization.
    representedByAnchoredTerms : ∀ scale anchor →
      NormalizedExpectation scale anchor → Set

    representationUsesOnlyAnchoredDomains : ∀ scale anchor domain →
      AnchoredTerm scale anchor domain → containsAnchor anchor domain

    -- Source bound: the normalized anchored response inherits the exponential
    -- localization envelope (the concrete CMP119 application replaces B_0 by
    -- O(p_1(g_k))).
    anchoredTermBelowSourceEnvelope : ∀ scale anchor domain →
      (term : AnchoredTerm scale anchor domain) →
      magnitude term ≤ amplitude scale * sourceExponentialEnvelope scale domain

open CMP119AnchoredNormalizedExpectationSource public

record CMP119LocalInsertionDictionary
    (source : CMP119AnchoredNormalizedExpectationSource) : Set₁ where
  field
    RepositoryInsertion : Set
    repositoryAnchor : RepositoryInsertion → Anchor source

    IsSourceLocalAnalyticInsertion : RepositoryInsertion → Set

    repositoryNormalizedExpectation :
      (scale : Scale source) → RepositoryInsertion →
      NormalizedExpectation source scale
        (repositoryAnchor)

    repositoryInsertionIsRepresented :
      ∀ scale insertion →
      IsSourceLocalAnalyticInsertion insertion →
      representedByAnchoredTerms source scale (repositoryAnchor insertion)
        (repositoryNormalizedExpectation scale insertion)

open CMP119LocalInsertionDictionary public

-- The published theorem itself is accepted at its literal source boundary.
cmp119AnchoredNormalizedExpectationSourceLevel : ProofLevel
cmp119AnchoredNormalizedExpectationSourceLevel = standardImported

-- What remains new is NOT a second cluster expansion.  It is the same-object
-- dictionary showing that the repository's physical insertions are members of
-- the source local analytic insertion class.
cmp119RepositoryLocalInsertionDictionaryLevel : ProofLevel
cmp119RepositoryLocalInsertionDictionaryLevel = conditional
