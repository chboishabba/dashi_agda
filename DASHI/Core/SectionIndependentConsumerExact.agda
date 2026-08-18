module DASHI.Core.SectionIndependentConsumerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments", Annals of Mathematical Statistics
-- 24 (1953), 265--272. DOI: 10.1214/aoms/1177729032.
--
-- Samson Abramsky and Achim Jung,
-- "Domain Theory", in Handbook of Logic in Computer Science, Vol. 3, 1994.
-- No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- Separate three notions which are easy to collapse when reopening a quotient:
--
--   * a coarse surface;
--   * an admissible section / reopening convention;
--   * a downstream consumer of the reopened fine state.
--
-- A quotient can be reopenable by many admissible sections without providing a
-- canonical reopening.  The safe criterion for a downstream consumer F is
-- section independence:
--
--   F (s q) = F (t q)
--
-- for every admissible pair of sections s,t and every coarse q.
--
-- If the consumer already factors through the quotient projection, section
-- independence follows immediately.  Conversely, when the declared section
-- family covers every fine point, section independence constructs an explicit
-- quotient factorization.  Thus, under that coverage hypothesis, the exact
-- criterion for safely forgetting section/alignment provenance is precisely
-- factorization through the coarse quotient.
--
-- This is a mathematical information-loss theorem.  It does not turn an
-- arbitrary chosen section into a canonical world state and does not confer
-- semantic or physical authority on the quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A family of admissible reopenings.  No quotient law is assumed yet.
------------------------------------------------------------------------

record ReopeningFamily : Set₁ where
  field
    Coarse Fine Section : Set
    reopen : Section → Coarse → Fine

open ReopeningFamily public

DownstreamSectionIndependent :
  (R : ReopeningFamily) →
  {Y : Set} →
  (Fine R → Y) → Set
DownstreamSectionIndependent R consume =
  (left right : Section R) →
  (q : Coarse R) →
  consume (reopen R left q) ≡ consume (reopen R right q)

record SectionDependenceWitness
    (R : ReopeningFamily)
    {Y : Set}
    (consume : Fine R → Y) : Set where
  field
    leftSection rightSection : Section R
    coarsePoint : Coarse R
    outputsDistinct :
      consume (reopen R leftSection coarsePoint)
      ≡ consume (reopen R rightSection coarsePoint) → ⊥

open SectionDependenceWitness public

sectionDependenceRefutesIndependence :
  (R : ReopeningFamily) →
  {Y : Set} →
  (consume : Fine R → Y) →
  SectionDependenceWitness R consume →
  DownstreamSectionIndependent R consume → ⊥
sectionDependenceRefutesIndependence R consume witness independent =
  outputsDistinct witness
    (independent
      (leftSection witness)
      (rightSection witness)
      (coarsePoint witness))

------------------------------------------------------------------------
-- Add an actual quotient projection and right-inverse law for every declared
-- admissible section.
------------------------------------------------------------------------

record SectionedQuotientFamily : Set₁ where
  field
    reopeningFamily : ReopeningFamily
    project : Fine reopeningFamily → Coarse reopeningFamily
    sectionLaw :
      (section : Section reopeningFamily) →
      (q : Coarse reopeningFamily) →
      project (reopen reopeningFamily section q) ≡ q

open SectionedQuotientFamily public

record ProjectionFactorization
    (Q : SectionedQuotientFamily)
    {Y : Set}
    (consume : Fine (reopeningFamily Q) → Y) : Set where
  field
    coarseConsumer : Coarse (reopeningFamily Q) → Y
    factors :
      (fine : Fine (reopeningFamily Q)) →
      consume fine ≡ coarseConsumer (project Q fine)

open ProjectionFactorization public

factorizationImpliesSectionIndependence :
  (Q : SectionedQuotientFamily) →
  {Y : Set} →
  (consume : Fine (reopeningFamily Q) → Y) →
  ProjectionFactorization Q consume →
  DownstreamSectionIndependent (reopeningFamily Q) consume
factorizationImpliesSectionIndependence Q consume factorized left right q =
  trans
    (factors factorized (reopen (reopeningFamily Q) left q))
    (trans
      (cong
        (coarseConsumer factorized)
        (sectionLaw Q left q))
      (trans
        (sym
          (cong
            (coarseConsumer factorized)
            (sectionLaw Q right q)))
        (sym
          (factors factorized
            (reopen (reopeningFamily Q) right q)))))

------------------------------------------------------------------------
-- Coverage says the declared admissible sections really cover the fine carrier:
-- each fine point is some section's reopening of its own coarse projection.
------------------------------------------------------------------------

record FinePointCovered
    (Q : SectionedQuotientFamily)
    (fine : Fine (reopeningFamily Q)) : Set where
  field
    coveringSection : Section (reopeningFamily Q)
    coveringEquation :
      reopen (reopeningFamily Q) coveringSection (project Q fine) ≡ fine

open FinePointCovered public

SectionFamilyCoversFine : SectionedQuotientFamily → Set
SectionFamilyCoversFine Q =
  (fine : Fine (reopeningFamily Q)) → FinePointCovered Q fine

sectionIndependenceImpliesFactorization :
  (Q : SectionedQuotientFamily) →
  {Y : Set} →
  (consume : Fine (reopeningFamily Q) → Y) →
  (defaultSection : Section (reopeningFamily Q)) →
  SectionFamilyCoversFine Q →
  DownstreamSectionIndependent (reopeningFamily Q) consume →
  ProjectionFactorization Q consume
sectionIndependenceImpliesFactorization
    Q consume defaultSection coverage independent = record
  { coarseConsumer = λ q →
      consume (reopen (reopeningFamily Q) defaultSection q)
  ; factors = λ fine →
      let covered = coverage fine
      in trans
        (cong consume (sym (coveringEquation covered)))
        (independent
          (coveringSection covered)
          defaultSection
          (project Q fine))
  }

------------------------------------------------------------------------
-- Boundary / interpretation.
------------------------------------------------------------------------

record SectionIndependentConsumerBoundary : Set where
  field
    reopenableImpliesCanonicalReopening : Bool
    factorizedConsumerIsSectionIndependent : Bool
    coveredSectionIndependentConsumerFactorsThroughQuotient : Bool
    sectionDependenceRequiresProvenanceRetention : Bool
    quotientFactorizationConfersWorldAuthority : Bool

canonicalSectionIndependentConsumerBoundary :
  SectionIndependentConsumerBoundary
canonicalSectionIndependentConsumerBoundary = record
  { reopenableImpliesCanonicalReopening = false
  ; factorizedConsumerIsSectionIndependent = true
  ; coveredSectionIndependentConsumerFactorsThroughQuotient = true
  ; sectionDependenceRequiresProvenanceRetention = true
  ; quotientFactorizationConfersWorldAuthority = false
  }
