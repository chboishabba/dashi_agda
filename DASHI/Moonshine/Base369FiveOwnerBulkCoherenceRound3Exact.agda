{-# OPTIONS --safe #-}
module DASHI.Moonshine.Base369FiveOwnerBulkCoherenceRound3Exact where

-- Round 3 / Slot 3. Reuse the source-pinned proof owners.
-- These are exact equalities of Natural-number dimensions.
-- They do NOT identify the actual Monster module, VOA, or its action.
-- Original mathematical context: Heisenberg/Weyl, E8, Monster moonshine;
-- original repo proof ownership remains with the imported modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369AppraisalHeisenbergMonomialActionBidiExact as Monomial
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Moonshine.Base369DecimalCompletionMonsterBulkBidiExact as Bulk
import DASHI.Moonshine.Base369ExceptionalAlbertFiftyThreeResidualBidiExact as Albert
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as Monster

-- Invariant 1: the geometric product and its genuine Heisenberg chart agree.
slot03GeometryHeisenbergCount :
  Carrier.factorisedFabricStateCount ≡ Geometry.hyperfabricStateCount
slot03GeometryHeisenbergCount = Carrier.factorisedCountAgreesWithGeometry

-- Invariant 2: the 729-dimensional finite basis is the one already owned.
slot03HeisenbergFibre729 : Carrier.heisenbergFibreStateCount ≡ 729
slot03HeisenbergFibre729 = Carrier.heisenbergFibreStateCountIs729

-- Invariant 3: 10 completed coarse channels times the geometric fabric.
slot03Bulk196830 : Bulk.base369TenChannelBulk ≡ 196830
slot03Bulk196830 = Bulk.base369TenChannelBulkIs196830

-- Bridge A: two independently constructed bulk accounting expressions.
slot03TenByNineBulkAgreesWithBase369 :
  Ninety.threePhaseTenByNineBulkDimension ≡ Bulk.base369TenChannelBulk
slot03TenByNineBulkAgreesWithBase369 =
  trans Ninety.threePhaseTenByNineBulkIs196830
        (sym Bulk.base369TenChannelBulkIs196830)

-- Bridge B: the same finite bulk agrees with the existing harmonic owner.
slot03TenByNineBulkAgreesWithHarmonic :
  Ninety.threePhaseTenByNineBulkDimension ≡ Harmonic.elementaryHarmonicDimension
slot03TenByNineBulkAgreesWithHarmonic =
  trans slot03TenByNineBulkAgreesWithBase369
        Bulk.base369BulkAgreesWithHarmonicElementaryDimension

-- Bridge C: and with the existing Monster bulk number, NOT its actual action.
slot03TenByNineBulkAgreesWithMonsterNumber :
  Ninety.threePhaseTenByNineBulkDimension ≡ Monster.monsterBulk
slot03TenByNineBulkAgreesWithMonsterNumber =
  trans slot03TenByNineBulkAgreesWithBase369
        Bulk.base369BulkAgreesWithMonsterBulk

-- Bridge D: exact recovery of the known dimension +53, without implying
-- that the Albert residual is an equivariant Monster representation.
slot03MonsterNumberFromTenByNine :
  Ninety.threePhaseTenByNineBulkDimension + Monster.reducedSixByNine
    ≡ Bulk.monsterDimensionFromBase369Bulk
slot03MonsterNumberFromTenByNine =
  cong (λ n → n + Monster.reducedSixByNine)
       slot03TenByNineBulkAgreesWithBase369

-- Bridge E: preserve the 54-dimensional weight-two completion independently.
slot03WeightTwoNumberFromTenByNine :
  Ninety.threePhaseTenByNineBulkDimension + Monster.fullSixByNine
    ≡ Bulk.moonshineWeightTwoFromBase369Bulk
slot03WeightTwoNumberFromTenByNine =
  cong (λ n → n + Monster.fullSixByNine)
       slot03TenByNineBulkAgreesWithBase369

-- Existing actual action / 53-residual recognition is deliberately NOT
-- inferred from these equality proofs.
