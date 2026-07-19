module DASHI.Biology.PrionAmyloidTemplating where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Structural carrier
------------------------------------------------------------------------

-- Amyloid is represented as a conformational state, not as an organism.
data Conformation : Set where
  native  : Conformation
  amyloid : Conformation

-- Contact is a local structural update.  An amyloid seed can template a
-- compatible native substrate; native material cannot do the converse.
template : Conformation → Conformation → Conformation
template native  substrate = substrate
template amyloid native    = amyloid
template amyloid amyloid   = amyloid

nativeDoesNotTemplate : (c : Conformation) → template native c ≡ c
nativeDoesNotTemplate c = refl

amyloidConvertsNative : template amyloid native ≡ amyloid
amyloidConvertsNative = refl

amyloidPersists : template amyloid amyloid ≡ amyloid
amyloidPersists = refl

templateIdempotent : (seed substrate : Conformation) →
  template seed (template seed substrate) ≡ template seed substrate
templateIdempotent native  substrate = refl
templateIdempotent amyloid native    = refl
templateIdempotent amyloid amyloid   = refl

------------------------------------------------------------------------
-- Amyloid evidence versus prion evidence
------------------------------------------------------------------------

-- Cross-beta order and fibril assembly are the defining structural evidence
-- carried by this minimal amyloid interface.  No infectivity follows from it.
record AmyloidEvidence (Protein : Set) : Set₁ where
  field
    conformation       : Protein → Conformation
    crossBetaOrdered   : Protein → Set
    fibrilCompetent    : Protein → Set

-- A templating system identifies which molecular contacts are compatible and
-- proves the conversion law only for those contacts.
record TemplatingSystem (Protein : Set) : Set₁ where
  field
    amyloidEvidence : AmyloidEvidence Protein
    Compatible      : Protein → Protein → Set
    contact          : Protein → Protein → Protein

    compatibleAmyloidTemplates :
      (seed substrate : Protein) →
      Compatible seed substrate →
      AmyloidEvidence.conformation amyloidEvidence seed ≡ amyloid →
      AmyloidEvidence.conformation amyloidEvidence substrate ≡ native →
      AmyloidEvidence.conformation amyloidEvidence (contact seed substrate)
        ≡ amyloid

-- Prionhood is strictly stronger than amyloid structure: the templated state
-- must cross a biological boundary and remain templating-competent afterward.
record PrionSystem (Protein Host : Set) : Set₁ where
  field
    templating       : TemplatingSystem Protein
    residentHost     : Protein → Host
    transfer         : Host → Host → Protein → Protein
    Transmissible    : Protein → Set

    crossesHostBoundary :
      (source target : Host) (seed : Protein) →
      Transmissible seed →
      residentHost (transfer source target seed) ≡ target

    transferPreservesAmyloid :
      (source target : Host) (seed : Protein) →
      Transmissible seed →
      AmyloidEvidence.conformation
        (TemplatingSystem.amyloidEvidence templating) seed ≡ amyloid →
      AmyloidEvidence.conformation
        (TemplatingSystem.amyloidEvidence templating)
        (transfer source target seed) ≡ amyloid

------------------------------------------------------------------------
-- Pathology is an additional dynamical layer
------------------------------------------------------------------------

-- Structural propagation alone does not entail disease, much less immediate
-- lethality from one molecule.  A pathology model must supply a burden,
-- accumulation dynamics, a lethal region, and the bridge between them.
record PathologyModel (Protein Tissue Burden : Set) : Set₁ where
  field
    burden       : Tissue → Burden
    expose       : Protein → Tissue → Tissue
    _≤burden_    : Burden → Burden → Set
    Lethal       : Burden → Set

    exposureMonotone : (seed : Protein) (tissue : Tissue) →
      burden tissue ≤burden burden (expose seed tissue)

-- This optional witness states explicitly that one exposure is non-lethal in
-- a particular model.  It is not derivable from amyloid or prionhood alone.
record SingleExposureNonLethal
  {Protein Tissue Burden : Set}
  (P : PathologyModel Protein Tissue Burden) : Set₁ where
  field
    nonLethalAfterOne : (seed : Protein) (tissue : Tissue) →
      PathologyModel.Lethal P
        (PathologyModel.burden P (PathologyModel.expose P seed tissue)) → ⊥

------------------------------------------------------------------------
-- Exact conceptual boundary
------------------------------------------------------------------------

record AmyloidPrionBoundary : Set₁ where
  field
    Protein Host Tissue Burden : Set
    amyloidStructure : AmyloidEvidence Protein
    prionDynamics    : PrionSystem Protein Host
    pathology        : PathologyModel Protein Tissue Burden

-- The types enforce the intended non-collapse:
--   amyloid structure  ≠ templating proof
--   templating proof   ≠ host-to-host transmissibility
--   transmissibility  ≠ pathology
--   pathology          ≠ immediate lethality from one exposure
