module DASHI.Physics.YangMills.BalabanClayGate4CMP109ProjectedEndpointBlocksExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Dec; yes; no; Not; _∈_; elements; complete; first; second;
    PositiveBond; periodicTorus4DecidableEquality)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicEndpointBlockPredicateExact as Endpoint

------------------------------------------------------------------------
-- Canonical endpoint blocks induced by a literal coarse-site projection.
--
-- Primary provenance:
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The physical paper fixes the block geometry.  DASHI's repository-specific
-- finite construction is as follows: a fine positive bond belongs to the block
-- of a coarse site exactly when the coarse-site projection of its initial site
-- is that coarse site.  Source and target endpoint blocks are then obtained by
-- filtering the complete fine-bond enumeration.  No hand-written block list and
-- no independent decidability assumption remain.
------------------------------------------------------------------------

record PeriodicCMP109SiteProjection
    (fineN coarseN : Nat) : Set₁ where
  field
    coarseOfFineSite :
      Periodic.PeriodicBlock fineN → Periodic.PeriodicBlock coarseN

open PeriodicCMP109SiteProjection public

FineBondProjectsToCoarseSite :
  ∀ {fineN coarseN} →
  PeriodicCMP109SiteProjection fineN coarseN →
  Periodic.PeriodicBlock coarseN →
  PositiveBond (suc fineN) → Set
FineBondProjectsToCoarseSite projection coarseSite fineBond =
  coarseOfFineSite projection (first fineBond) ≡ coarseSite

fineBondProjectsToCoarseSiteDecidable :
  ∀ {fineN coarseN}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    coarseSite fineBond →
  Dec (FineBondProjectsToCoarseSite projection coarseSite fineBond)
fineBondProjectsToCoarseSiteDecidable {coarseN = coarseN}
    projection coarseSite fineBond
  with periodicTorus4DecidableEquality (suc coarseN)
    (coarseOfFineSite projection (first fineBond)) coarseSite
... | yes equality = yes equality
... | no inequality = no inequality

projectedFineBondBlock :
  ∀ {fineN coarseN} →
  PeriodicCMP109SiteProjection fineN coarseN →
  Periodic.PeriodicBlock coarseN →
  List (PositiveBond (suc fineN))
projectedFineBondBlock {fineN = fineN} projection coarseSite =
  Support.filterDec
    (FineBondProjectsToCoarseSite projection coarseSite)
    (fineBondProjectsToCoarseSiteDecidable projection coarseSite)
    (elements (Support.positiveBondFinite (suc fineN)))

projectedFineBondBlockSound :
  ∀ {fineN coarseN}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    coarseSite fineBond →
  fineBond ∈ projectedFineBondBlock projection coarseSite →
  FineBondProjectsToCoarseSite projection coarseSite fineBond
projectedFineBondBlockSound projection coarseSite fineBond =
  Support.filterDecSound
    (fineBondProjectsToCoarseSiteDecidable projection coarseSite)

projectedFineBondBlockComplete :
  ∀ {fineN coarseN}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    coarseSite fineBond →
  FineBondProjectsToCoarseSite projection coarseSite fineBond →
  fineBond ∈ projectedFineBondBlock projection coarseSite
projectedFineBondBlockComplete {fineN = fineN}
    projection coarseSite fineBond proof =
  Support.filterDecComplete
    (fineBondProjectsToCoarseSiteDecidable projection coarseSite)
    (complete (Support.positiveBondFinite (suc fineN)) fineBond)
    proof

sourceEndpoint :
  ∀ {coarseN} →
  PositiveBond (suc coarseN) → Periodic.PeriodicBlock coarseN
sourceEndpoint = first

targetEndpoint :
  ∀ {coarseN} →
  PositiveBond (suc coarseN) → Periodic.PeriodicBlock coarseN
targetEndpoint coarseBond =
  Bond.positiveStep (first coarseBond) (second coarseBond)

projectedSourceEndpointBlock :
  ∀ {fineN coarseN} →
  PeriodicCMP109SiteProjection fineN coarseN →
  PositiveBond (suc coarseN) →
  List (PositiveBond (suc fineN))
projectedSourceEndpointBlock projection coarseBond =
  projectedFineBondBlock projection (sourceEndpoint coarseBond)

projectedTargetEndpointBlock :
  ∀ {fineN coarseN} →
  PeriodicCMP109SiteProjection fineN coarseN →
  PositiveBond (suc coarseN) →
  List (PositiveBond (suc fineN))
projectedTargetEndpointBlock projection coarseBond =
  projectedFineBondBlock projection (targetEndpoint coarseBond)

projectedEndpointBlockLists :
  ∀ {fineN coarseN} →
  PeriodicCMP109SiteProjection fineN coarseN →
  Endpoint.PeriodicEndpointBlockLists (suc fineN) (suc coarseN)
projectedEndpointBlockLists projection = record
  { Endpoint.PeriodicEndpointBlockLists.sourceEndpointBlock =
      projectedSourceEndpointBlock projection
  ; Endpoint.PeriodicEndpointBlockLists.targetEndpointBlock =
      projectedTargetEndpointBlock projection
  }

sourceEndpointMembershipIffProjection :
  ∀ {fineN coarseN}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    coarseBond fineBond →
  Support.Iff
    (Endpoint.FineBondInSourceEndpointBlock
      (projectedEndpointBlockLists projection) coarseBond fineBond)
    (FineBondProjectsToCoarseSite projection
      (sourceEndpoint coarseBond) fineBond)
sourceEndpointMembershipIffProjection projection coarseBond fineBond =
  Support.iff
    (projectedFineBondBlockSound projection
      (sourceEndpoint coarseBond) fineBond)
    (projectedFineBondBlockComplete projection
      (sourceEndpoint coarseBond) fineBond)

targetEndpointMembershipIffProjection :
  ∀ {fineN coarseN}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    coarseBond fineBond →
  Support.Iff
    (Endpoint.FineBondInTargetEndpointBlock
      (projectedEndpointBlockLists projection) coarseBond fineBond)
    (FineBondProjectsToCoarseSite projection
      (targetEndpoint coarseBond) fineBond)
targetEndpointMembershipIffProjection projection coarseBond fineBond =
  Support.iff
    (projectedFineBondBlockSound projection
      (targetEndpoint coarseBond) fineBond)
    (projectedFineBondBlockComplete projection
      (targetEndpoint coarseBond) fineBond)

projectedEndpointSupportMeaning :
  ∀ {fineN coarseN}
    (projection : PeriodicCMP109SiteProjection fineN coarseN) →
  Support.PeriodicQkSupportMeaning (suc fineN) (suc coarseN)
projectedEndpointSupportMeaning projection =
  Endpoint.endpointBlockSupportMeaning
    (projectedEndpointBlockLists projection)

record EndpointSupportedFrechetDerivative
    {fineN coarseN : Nat}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    (Entry : Set) : Set₁ where
  field
    derivativeEntry :
      PositiveBond (suc coarseN) → PositiveBond (suc fineN) → Entry
    zeroEntry : Entry

    derivativeVanishesOutsideEndpointBlocks : ∀ coarseBond fineBond →
      Not
        (Endpoint.EndpointBlockUnionSupport
          (projectedEndpointBlockLists projection)
          coarseBond fineBond) →
      derivativeEntry coarseBond fineBond ≡ zeroEntry

open EndpointSupportedFrechetDerivative public

record CMP109DerivativeSupportIdentification
    {fineN coarseN : Nat}
    (projection : PeriodicCMP109SiteProjection fineN coarseN)
    (Entry : Set) : Set₁ where
  field
    derivative : EndpointSupportedFrechetDerivative projection Entry

    PhysicalDerivative :
      (PositiveBond (suc coarseN) → PositiveBond (suc fineN) → Entry) → Set

    physicalDerivative :
      PhysicalDerivative (derivativeEntry derivative)

open CMP109DerivativeSupportIdentification public

projectedEndpointBlockConstructionLevel : ProofLevel
projectedEndpointBlockConstructionLevel = computed

projectedEndpointMembershipDecisionLevel : ProofLevel
projectedEndpointMembershipDecisionLevel = machineChecked

projectedEndpointMembershipSoundCompleteLevel : ProofLevel
projectedEndpointMembershipSoundCompleteLevel = machineChecked

projectedEndpointSupportCarrierLevel : ProofLevel
projectedEndpointSupportCarrierLevel = machineChecked

physicalCMP109SiteProjectionInputsLevel : ProofLevel
physicalCMP109SiteProjectionInputsLevel = conditional

physicalCMP109DerivativeOutsideSupportZeroInputsLevel : ProofLevel
physicalCMP109DerivativeOutsideSupportZeroInputsLevel = conditional
