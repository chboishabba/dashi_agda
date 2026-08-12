module DASHI.Physics.YangMills.BalabanCMP109L13AllCoarseAnchorsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- The source-faithful minimal CMP109 carrier has a one-site coarse torus.
-- Therefore the distinction between a gauge section anchored at one chosen
-- coarse root and a section anchored at *every* embedded coarse site vanishes
-- exactly at this local Gate-I scale.  We prove the equivalence rather than
-- assuming it: every coarse site is propositionally equal to the repository
-- coarse origin.
--
-- This closes the root-vs-all-coarse-sites geometric seam for the L=13 local
-- variational problem.  It does not claim the corresponding theorem on an
-- arbitrary multi-block coarse torus; that belongs to the global RG induction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

infixr 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

record CoarseGaugeAnchorData (Gauge Group : Set) : Set₁ where
  field
    identity : Group
    coarseGauge : Gauge → Minimal.RepositoryCoarseSite → Group

open CoarseGaugeAnchorData public

AnchoredAtOrigin :
  ∀ {Gauge Group} → CoarseGaugeAnchorData Gauge Group → Gauge → Set
AnchoredAtOrigin dataSet gauge =
  coarseGauge dataSet gauge Minimal.repositoryCoarseOrigin ≡ identity dataSet

AnchoredAtEveryCoarseSite :
  ∀ {Gauge Group} → CoarseGaugeAnchorData Gauge Group → Gauge → Set
AnchoredAtEveryCoarseSite dataSet gauge =
  ∀ coarse → coarseGauge dataSet gauge coarse ≡ identity dataSet

originAnchorImpliesAllCoarseAnchors :
  ∀ {Gauge Group}
    (dataSet : CoarseGaugeAnchorData Gauge Group)
    gauge →
  AnchoredAtOrigin dataSet gauge →
  AnchoredAtEveryCoarseSite dataSet gauge
originAnchorImpliesAllCoarseAnchors dataSet gauge originAnchor coarse =
  subst
    (λ selected → coarseGauge dataSet gauge selected ≡ identity dataSet)
    (sym (Minimal.repositoryCoarseUnique coarse))
    originAnchor

allCoarseAnchorsImpliesOriginAnchor :
  ∀ {Gauge Group}
    (dataSet : CoarseGaugeAnchorData Gauge Group)
    gauge →
  AnchoredAtEveryCoarseSite dataSet gauge →
  AnchoredAtOrigin dataSet gauge
allCoarseAnchorsImpliesOriginAnchor dataSet gauge allAnchors =
  allAnchors Minimal.repositoryCoarseOrigin

record LogicalEquivalence (A B : Set) : Set₁ where
  field
    forward : A → B
    backward : B → A

open LogicalEquivalence public

originAnchorIffAllCoarseAnchors :
  ∀ {Gauge Group}
    (dataSet : CoarseGaugeAnchorData Gauge Group)
    gauge →
  LogicalEquivalence
    (AnchoredAtOrigin dataSet gauge)
    (AnchoredAtEveryCoarseSite dataSet gauge)
originAnchorIffAllCoarseAnchors dataSet gauge = record
  { forward = originAnchorImpliesAllCoarseAnchors dataSet gauge
  ; backward = allCoarseAnchorsImpliesOriginAnchor dataSet gauge
  }

------------------------------------------------------------------------
-- Both endpoints of every minimal coarse bond are anchored automatically.
------------------------------------------------------------------------

BothEndpointsAnchored :
  ∀ {Gauge Group} →
  CoarseGaugeAnchorData Gauge Group → Gauge →
  Minimal.RepositoryCoarseBond → Set
BothEndpointsAnchored dataSet gauge coarseBond =
  (coarseGauge dataSet gauge (Carrier.first coarseBond) ≡ identity dataSet)
  ×
  (coarseGauge dataSet gauge (Carrier.second coarseBond) ≡ identity dataSet)

originAnchorImpliesEveryBondEndpointsAnchored :
  ∀ {Gauge Group}
    (dataSet : CoarseGaugeAnchorData Gauge Group)
    gauge →
  AnchoredAtOrigin dataSet gauge →
  ∀ coarseBond → BothEndpointsAnchored dataSet gauge coarseBond
originAnchorImpliesEveryBondEndpointsAnchored dataSet gauge originAnchor coarseBond =
  let
    allAnchors = originAnchorImpliesAllCoarseAnchors dataSet gauge originAnchor
  in
  allAnchors (Carrier.first coarseBond)
  , allAnchors (Carrier.second coarseBond)

cmp109L13OriginAllCoarseAnchorEquivalenceLevel : ProofLevel
cmp109L13OriginAllCoarseAnchorEquivalenceLevel = machineChecked

cmp109L13EveryCoarseBondEndpointAnchoredLevel : ProofLevel
cmp109L13EveryCoarseBondEndpointAnchoredLevel = machineChecked

-- The arbitrary-volume counterpart is intentionally not promoted here: a
-- multi-site coarse lattice needs an actual global section construction.
ym4GlobalCoarseAnchoredGaugeSectionLevel : ProofLevel
ym4GlobalCoarseAnchoredGaugeSectionLevel = conditional
