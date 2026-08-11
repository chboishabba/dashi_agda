module DASHI.Physics.YangMills.BalabanSingleBlockRootedGaugeAverageCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Close the algebraic part of the configuration-space seam for a one-coarse-
-- block average.  The existing rooted path section constructs a genuine fine
-- gauge function g_U with g_U(root)=1.  Whenever the concrete nonlinear block
-- average restricts fine gauge transformations by evaluation at that same
-- root, the rooted section is therefore automatically coarse anchored.  The
-- exact block-average covariance theorem then gives
--
--       Q(U^{g_U}) = Q(U)
--
-- for every block label, with no additional gauge averaging argument.
--
-- This module deliberately isolates the only still-physical identification:
-- the concrete selected nonlinear Bałaban average must prove that its
-- restrictGauge map is root evaluation.  It does not assume that preservation
-- of Q forces root identity; the separate stabilizer theorem proves the exact
-- converse is only membership in Stab(Q(U)).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicLatticeGaugeCovariance as Gauge
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.CompactLieBlockAverage as Average
import DASHI.Physics.YangMills.BalabanBlockAnchoredGaugeAverageCompatibilityExact as Anchored

record RootRestrictionData
    {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra) : Set₁ where
  field
    restrictGaugeIsRootEvaluation : ∀ fineGauge →
      Average.restrictGauge bundle fineGauge
      ≡ fineGauge (Rooted.RootedPathSystem.root paths)

open RootRestrictionData public

rootCoarseIdentityData :
  ∀ {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra) →
  (∀ coarseField →
    Average.coarseGaugeAction bundle (Gauge.GroupStructure.unit group) coarseField
    ≡ coarseField) →
  Anchored.CoarseGaugeIdentityData bundle
rootCoarseIdentityData group paths bundle unitActs = record
  { Anchored.CoarseGaugeIdentityData.coarseIdentity = Gauge.GroupStructure.unit group
  ; Anchored.CoarseGaugeIdentityData.coarseIdentityActsTrivially = unitActs
  }

rootedGaugeFunctionCoarseAnchored :
  ∀ {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra)
    (restriction : RootRestrictionData group paths bundle)
    (unitActs : ∀ coarseField →
      Average.coarseGaugeAction bundle (Gauge.GroupStructure.unit group) coarseField
      ≡ coarseField)
    gaugeField →
  Anchored.CoarseAnchoredGauge bundle
    (rootCoarseIdentityData group paths bundle unitActs)
    (Rooted.rootedGaugeFunction group paths gaugeField)
rootedGaugeFunctionCoarseAnchored
    group paths bundle restriction unitActs gaugeField =
  trans
    (restrictGaugeIsRootEvaluation restriction
      (Rooted.rootedGaugeFunction group paths gaugeField))
    (Rooted.rootedGaugeFunctionBased group paths gaugeField)

record RootedSingleBlockAverageData
    {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra) : Set₁ where
  field
    rootRestriction : RootRestrictionData group paths bundle
    unitActsTrivially : ∀ coarseField →
      Average.coarseGaugeAction bundle (Gauge.GroupStructure.unit group) coarseField
      ≡ coarseField

open RootedSingleBlockAverageData public

rootedGaugeRepresentativePreservesBlockAverage :
  ∀ {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra)
    (data : RootedSingleBlockAverageData group paths bundle)
    block gaugeField →
  Average.blockAverage bundle block
    (Rooted.rootedGaugeRepresentative group paths gaugeField)
  ≡ Average.blockAverage bundle block gaugeField
rootedGaugeRepresentativePreservesBlockAverage
    group paths bundle data block gaugeField =
  let
    identityData = rootCoarseIdentityData
      group paths bundle (unitActsTrivially data)

    anchored : Anchored.CoarseAnchoredGauge bundle identityData
      (Rooted.rootedGaugeFunction group paths gaugeField)
    anchored = rootedGaugeFunctionCoarseAnchored
      group paths bundle (rootRestriction data)
      (unitActsTrivially data) gaugeField
  in
  Anchored.blockAverageFixedByCoarseIdentityGauge
    bundle identityData block
    (Rooted.rootedGaugeFunction group paths gaugeField)
    gaugeField anchored

rootedSingleBlockAverageCompatibilityLevel : ProofLevel
rootedSingleBlockAverageCompatibilityLevel = conditional
