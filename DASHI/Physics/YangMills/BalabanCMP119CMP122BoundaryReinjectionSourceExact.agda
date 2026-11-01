module DASHI.Physics.YangMills.BalabanCMP119CMP122BoundaryReinjectionSourceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- DIRECT LOCATORS
--
-- CMP119 Sect. 2, equations (2.40)--(2.42), pp. 260--262:
--   * B_k is represented as a sum of localized boundary expressions;
--   * every localized term extends analytically to the same multiscale spaces
--     U_j(X, alpha_0, alpha_1);
--   * the extensions are gauge invariant;
--   * they satisfy the exponential localization bound (2.42).
--
-- CMP122, p. 390 immediately after (1.99): the localized R'^(k)(X) terms whose
-- domains meet the large-field region are assigned to the new boundary terms
-- B'^(k)(X).  After (1.100), pp. 390--391, Bałaban states that the newly
-- constructed action satisfies the induction hypothesis, and that the result
-- of the R-operation has the form (2.18) of the preceding paper with all
-- expressions satisfying the Sect.-2 induction hypotheses.
--
-- CONSEQUENCE
--
-- Boundary reinjection is therefore not a new analytic theorem to reprove in
-- DASHI.  Under the hypotheses of Bałaban's complete-density construction, the
-- published R-operation already creates boundary terms in the next admissible
-- analytic/localized class.  The remaining DASHI task is a literal carrier and
-- norm/domain dictionary to the repository BoundaryAdmissible predicate.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP119BoundaryTermClass
    (Scale Polymer BoundaryTerm AnalyticDomain : Set) : Set₁ where
  field
    boundaryTerms : Scale → Polymer → List BoundaryTerm
    domain : Scale → Polymer → AnalyticDomain

    AnalyticOn : BoundaryTerm → AnalyticDomain → Set
    GaugeInvariant : BoundaryTerm → Set
    ExponentiallyLocalized : Scale → Polymer → BoundaryTerm → Set

    analyticOnInductiveDomain : ∀ scale polymer term →
      AnalyticOn term (domain scale polymer)

    gaugeInvariant : ∀ scale polymer term →
      GaugeInvariant term

    exponentiallyLocalized : ∀ scale polymer term →
      ExponentiallyLocalized scale polymer term

open CMP119BoundaryTermClass public

record CMP122BoundaryReinjectionStep
    {Scale Polymer BoundaryTerm AnalyticDomain : Set}
    (sourceClass : CMP119BoundaryTermClass
      Scale Polymer BoundaryTerm AnalyticDomain) : Set₁ where
  field
    nextScale : Scale → Scale
    generated : Scale → Polymer → List BoundaryTerm

    -- The statement proved by the completed R-operation: newly generated
    -- boundary terms lie in the next Sect.-2 boundary class, with its common
    -- analyticity/locality requirements.
    GeneratedTermsAdmissible : Scale → Polymer → List BoundaryTerm → Set
    generatedTermsAdmissible : ∀ scale polymer →
      GeneratedTermsAdmissible scale polymer (generated scale polymer)

open CMP122BoundaryReinjectionStep public

cmp119BoundaryAnalyticityAndDecayLevel : ProofLevel
cmp119BoundaryAnalyticityAndDecayLevel = standardImported

cmp122BoundaryReinjectionPreservationLevel : ProofLevel
cmp122BoundaryReinjectionPreservationLevel = standardImported

-- Literal identification of CMP119 U_j(X,...) / B^(j)(X) with the repository
-- boundary-density carrier and its BoundaryAdmissible predicate remains a
-- representation theorem, not something obtained from the citation alone.
cmp119CMP122BoundaryRepositoryDictionaryLevel : ProofLevel
cmp119CMP122BoundaryRepositoryDictionaryLevel = conditional
