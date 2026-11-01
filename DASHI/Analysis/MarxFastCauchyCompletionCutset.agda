module DASHI.Analysis.MarxFastCauchyCompletionCutset where

open import Agda.Primitive using (Set₁)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.FastCauchyReals
open import DASHI.Analysis.FastCauchyQuotient
open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxConstructiveRealAdapter
open import DASHI.Analysis.MarxConstructiveRealRingNormalisation

------------------------------------------------------------------------
-- Exact dependency cutset from the repository's existing fast-Cauchy layer to
-- a nonterminal Marx differential carrier.
--
-- No second real-number construction is introduced here.  The selected
-- quotient backend, quotient arithmetic, algebra laws, and completeness data
-- are precisely the existing FastCauchyQuotient interfaces.  The only new
-- inhabitant required after those is the ring-normalisation/nondegeneracy
-- package isolated by MarxConstructiveRealRingNormalisation.

record FastCauchyMarxCompletionData : Set₁ where
  field
    rationalMetric : RationalMetricAuthority
    operations : FastCauchyOperations rationalMetric

    quotientBackend :
      SetQuotientBackend
        (FastCauchyReal rationalMetric)
        (_≈R_ {rationalMetric})

    quotientOperations :
      FastCauchyQuotientOperations
        rationalMetric
        operations
        quotientBackend

    quotientAlgebraLaws :
      FastCauchyQuotientAlgebraLaws
        rationalMetric
        operations
        quotientBackend
        quotientOperations

    quotientCompleteness :
      FastCauchyQuotientCompleteness
        rationalMetric
        operations
        quotientBackend

    ringNormalisation :
      ConstructedRealRingNormalisationLaws
        (fastCauchyConstructedReal
          (fastCauchyQuotientRealization
            quotientOperations
            quotientAlgebraLaws
            quotientCompleteness))

open FastCauchyMarxCompletionData public

selectedFastCauchyRealization :
  (D : FastCauchyMarxCompletionData) →
  FastCauchyQuotientRealization
    (rationalMetric D)
    (operations D)
selectedFastCauchyRealization D =
  fastCauchyQuotientRealization
    (quotientOperations D)
    (quotientAlgebraLaws D)
    (quotientCompleteness D)

selectedFastCauchyConstructedReal :
  FastCauchyMarxCompletionData →
  ConstructedOrderedCompleteReal
selectedFastCauchyConstructedReal D =
  fastCauchyConstructedReal (selectedFastCauchyRealization D)

selectedFastCauchyMarxAlgebra :
  (D : FastCauchyMarxCompletionData) →
  MarxAlgebra
selectedFastCauchyMarxAlgebra D =
  ordinaryConstructiveRealMarxAlgebra (ringNormalisation D)

selectedFastCauchyMarxPackage :
  (D : FastCauchyMarxCompletionData) →
  ConstructiveRealMarxDifferentialPackage
selectedFastCauchyMarxPackage D =
  ordinaryConstructiveRealMarxPackage (ringNormalisation D)

selectedFastCauchyCarrierNonterminal :
  (D : FastCauchyMarxCompletionData) →
  zero (selectedFastCauchyConstructedReal D)
  ≡ one (selectedFastCauchyConstructedReal D) →
  ⊥
selectedFastCauchyCarrierNonterminal D =
  ordinaryMarxCarrierNonterminal (ringNormalisation D)

------------------------------------------------------------------------
-- The representative-respect obligations are not new leaves: they are already
-- fields of FastCauchyOperations and FastCauchyQuotientOperations.  These
-- aliases make that reuse visible in the Marx completion ledger.

selectedAddRespectsEquality :
  (D : FastCauchyMarxCompletionData) →
  ∀ {a a′ b b′} →
  a ≈R a′ →
  b ≈R b′ →
  addR (operations D) a b ≈R addR (operations D) a′ b′
selectedAddRespectsEquality D =
  addRespect (operations D)

selectedSubRespectsEquality :
  (D : FastCauchyMarxCompletionData) →
  ∀ {a a′ b b′} →
  a ≈R a′ →
  b ≈R b′ →
  subR (operations D) a b ≈R subR (operations D) a′ b′
selectedSubRespectsEquality D =
  subRespect (operations D)

selectedMulRespectsEquality :
  (D : FastCauchyMarxCompletionData) →
  ∀ {a a′ b b′} →
  a ≈R a′ →
  b ≈R b′ →
  mulR (operations D) a b ≈R mulR (operations D) a′ b′
selectedMulRespectsEquality D =
  mulRespect (operations D)

selectedNegRespectsEquality :
  (D : FastCauchyMarxCompletionData) →
  ∀ {a a′} →
  a ≈R a′ →
  negR (operations D) a ≈R negR (operations D) a′
selectedNegRespectsEquality D =
  negRespectRepresentative (quotientOperations D)

------------------------------------------------------------------------
-- Honest frontier marker.
--
-- An inhabitant of FastCauchyMarxCompletionData closes the nondegenerate real
-- carrier lane.  The repository still needs a concrete SetQuotientBackend and
-- the quotient-level ring-normalisation/nondegeneracy proofs; this module does
-- not manufacture either from the backend-neutral interface.
