module DASHI.Physics.YangMills.BalabanClayGate4CMP109SupportOverlapCompletionExact where

open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (PositiveBond)

import DASHI.Physics.YangMills.BalabanClayGate4CMP109ProjectedEndpointBlocksExact as Endpoint
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkUniformSupportBoundsExact as Uniform

------------------------------------------------------------------------
-- Exact CMP 109 support and overlap counts on the periodic carrier.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The projected endpoint predicate already has a complete finite row and dual
-- column enumeration.  This module names the literal exact counts and their
-- canonical maxima N_row and N_col on the same support carrier, eliminating a
-- second overlap-count convention.
------------------------------------------------------------------------

record CMP109SupportOverlapCounts
    (fineN coarseN : Nat) : Set₁ where
  field
    projection : Endpoint.PeriodicCMP109SiteProjection fineN coarseN

  supportMeaning : Support.PeriodicQkSupportMeaning (suc fineN) (suc coarseN)
  supportMeaning = Endpoint.projectedEndpointSupportMeaning projection

  supportCarrier : Support.FiniteKernelSupportRelation
    (PositiveBond (suc coarseN)) (PositiveBond (suc fineN))
  supportCarrier = Support.periodicSupportCarrier supportMeaning

  exactRowOverlap : PositiveBond (suc coarseN) → Nat
  exactRowOverlap = Support.exactRowCount supportCarrier

  exactColumnOverlap : PositiveBond (suc fineN) → Nat
  exactColumnOverlap = Support.exactColumnCount supportCarrier

  Nrow : Nat
  Nrow = Uniform.uniformRowBound supportCarrier

  Ncol : Nat
  Ncol = Uniform.uniformColumnBound supportCarrier

open CMP109SupportOverlapCounts public

exactRowOverlapBelowNrow :
  ∀ {fineN coarseN}
    (counts : CMP109SupportOverlapCounts fineN coarseN)
    coarseBond →
  Uniform._≤ᴺ_
    (exactRowOverlap counts coarseBond)
    (Nrow counts)
exactRowOverlapBelowNrow counts coarseBond =
  Uniform.rowCountBelowUniformBound
    (supportCarrier counts) coarseBond

exactColumnOverlapBelowNcol :
  ∀ {fineN coarseN}
    (counts : CMP109SupportOverlapCounts fineN coarseN)
    fineBond →
  Uniform._≤ᴺ_
    (exactColumnOverlap counts fineBond)
    (Ncol counts)
exactColumnOverlapBelowNcol counts fineBond =
  Uniform.columnCountBelowUniformBound
    (supportCarrier counts) fineBond

cmp109ExactRowOverlapDefinitionLevel : ProofLevel
cmp109ExactRowOverlapDefinitionLevel = computed

cmp109ExactColumnOverlapDefinitionLevel : ProofLevel
cmp109ExactColumnOverlapDefinitionLevel = computed

cmp109UniformNrowConstructionLevel : ProofLevel
cmp109UniformNrowConstructionLevel = computed

cmp109UniformNcolConstructionLevel : ProofLevel
cmp109UniformNcolConstructionLevel = computed

cmp109OverlapUniversalBoundsLevel : ProofLevel
cmp109OverlapUniversalBoundsLevel = machineChecked

physicalCMP109ProjectionSelectionInputsLevel : ProofLevel
physicalCMP109ProjectionSelectionInputsLevel = conditional
