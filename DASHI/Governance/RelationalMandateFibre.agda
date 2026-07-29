module DASHI.Governance.RelationalMandateFibre where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FibreRestrictionCore as FibreCore
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Culture.CulturalTriadOperatorBoundary as Culture
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

------------------------------------------------------------------------
-- Coarse relational mandate fibre.
--
-- The notation "1 = subject + other + relation = 3" is read here as a
-- coarse-graining statement, not as arithmetic equality.  One observed
-- relational unit is the projection of a three-role fine carrier:
--
--   coarse unit
--      ^ fibre
--   principal / delegate / mandate relation.
--
-- This cross-pollinates the existing CulturalTriadOperatorBoundary with the
-- recursive hypervoxel rank/depth grammar.  It does not identify political
-- representation with spatial geometry, nor does it promote political or
-- legal authority.
------------------------------------------------------------------------

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

data MandateFineRole : Set where
  principalFineRole : MandateFineRole
  delegateFineRole : MandateFineRole
  mandateRelationFineRole : MandateFineRole

canonicalMandateFineRoles : List MandateFineRole
canonicalMandateFineRoles =
  principalFineRole
  ∷ delegateFineRole
  ∷ mandateRelationFineRole
  ∷ []

canonicalMandateFineRoleCountIsThree :
  listCount canonicalMandateFineRoles ≡ 3
canonicalMandateFineRoleCountIsThree = refl

canonicalCulturalTriadRoles : List Culture.TriadCarrierRole
canonicalCulturalTriadRoles =
  Culture.subjectCarrierRole
  ∷ Culture.otherCarrierRole
  ∷ Culture.relationCarrierRole
  ∷ []

canonicalCulturalTriadRoleCountIsThree :
  listCount canonicalCulturalTriadRoles ≡ 3
canonicalCulturalTriadRoleCountIsThree = refl

record TriadicMandateDetail : Set where
  constructor triadicMandateDetail
  field
    principal : String
    delegate : String
    mandateRelation : String

open TriadicMandateDetail public

data CoarseMandateUnit : Set where
  coarseMandateUnit : CoarseMandateUnit

coarseMandateProjection :
  TriadicMandateDetail →
  CoarseMandateUnit
coarseMandateProjection detail =
  coarseMandateUnit

MandateFibre : CoarseMandateUnit → Set
MandateFibre surface =
  Σ TriadicMandateDetail
    (λ detail → coarseMandateProjection detail ≡ surface)

canonicalTriadicMandateDetail : TriadicMandateDetail
canonicalTriadicMandateDetail =
  triadicMandateDetail
    "constituency/principal"
    "recallable delegate/agent"
    "scope-limited public mandate relation"

canonicalMandateFibre : MandateFibre coarseMandateUnit
canonicalMandateFibre =
  canonicalTriadicMandateDetail , refl

data MandateEvidence : Set where
  mandateEvidence : String → MandateEvidence

mandateFibreRestrictionCore : FibreCore.FibreRestrictionCore
mandateFibreRestrictionCore =
  FibreCore.fibreRestrictionCore
    TriadicMandateDetail
    CoarseMandateUnit
    MandateEvidence
    coarseMandateProjection
    MandateFibre
    (λ evidence surface → MandateFibre surface)
    true
    false

mandateFibreDoesNotRecoverCarrier :
  FibreCore.doesNotRecoverCarrier mandateFibreRestrictionCore ≡ true
mandateFibreDoesNotRecoverCarrier = refl

mandateFibreDoesNotPromoteTruth :
  FibreCore.promotesTruth mandateFibreRestrictionCore ≡ false
mandateFibreDoesNotPromoteTruth = refl

------------------------------------------------------------------------
-- Hypervoxel cross-pollination.
--
-- Rank one at depth one has three fine sites.  The governance adapter uses
-- only that coarse/fine shape: it does not claim that people, institutions or
-- mandates are literal voxels.
------------------------------------------------------------------------

rankOneDepthOneHasThreeSites :
  Hyper.siteCount 1 1 ≡ 3
rankOneDepthOneHasThreeSites =
  Hyper.rank1Depth1Sites

record CoarseTriadHypervoxelBridge : Set where
  constructor coarseTriadHypervoxelBridge
  field
    coarseUnitCount : Nat
    fineRoleCount : Nat
    coarseUnitCountIsOne : coarseUnitCount ≡ 1
    fineRoleCountIsThree : fineRoleCount ≡ 3
    rankOneSiteCountMatchesFineRoles :
      Hyper.siteCount 1 1 ≡ fineRoleCount
    coarseProjectionPresent : Bool
    arithmeticOneEqualsThreeClaimed : Bool
    spatialOntologyClaimed : Bool
    politicalAuthorityPromoted : Bool

open CoarseTriadHypervoxelBridge public

canonicalCoarseTriadHypervoxelBridge :
  CoarseTriadHypervoxelBridge
canonicalCoarseTriadHypervoxelBridge =
  coarseTriadHypervoxelBridge
    1
    3
    refl
    refl
    refl
    true
    false
    false
    false

coarseTriadSummary : String
coarseTriadSummary =
  "One coarse relational fibre projects a three-role principal/delegate/mandate carrier; 1=3 is not asserted as arithmetic, ontology, legal authority or political legitimacy."

canonicalRelationalMandateFibreReceipt :
  GenericReceipt.GenericReceipt
canonicalRelationalMandateFibreReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "coarse triadic mandate fibre"
    "DASHI.Governance.RelationalMandateFibre"
    "canonicalCoarseTriadHypervoxelBridge"
    "separates one coarse relational observation from its three fine principal/delegate/mandate roles and connects that shape to the existing rank-one ternary hypervoxel count"
    "no empirical, legal or political authority follows from the coarse/fine analogy"
    "agda -i . DASHI/Governance/RelationalMandateFibre.agda"
