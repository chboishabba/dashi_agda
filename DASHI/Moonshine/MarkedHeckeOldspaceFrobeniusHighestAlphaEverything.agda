module DASHI.Moonshine.MarkedHeckeOldspaceFrobeniusHighestAlphaEverything where

------------------------------------------------------------------------
-- Highest-alpha convergence root after PR #585's oldspace / isotypic tranche.
--
-- Two global producers remain:
--
--   (A) p=11 level-44 same-object comparison
--       analytic V1/V2/V4 good-prime oldspace
--          <-> marked quaternion/deck permutation module;
--
--   (B) supersingular geometric Frobenius realization for general p.
--
-- The downstream algebra around both is now closed.  In particular the generic
-- Frobenius consequence theorem is exercised on the actual p11/p37/p43 source
-- carriers rather than left as a conditional interface only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MarkedHeckeDeckCollisionEverything as Marked
import DASHI.Moonshine.P11Level44OldspaceSameObjectCutsetExact as OldCutset
import DASHI.Moonshine.GeometricSupersingularFrobeniusSelectorConsequenceExact as Frobenius
import DASHI.Moonshine.P11P37P43GeometricFrobeniusSelectorInstantiationsExact as Controls

oldspaceNoFurtherPrimeProbe :
  OldCutset.morePrimeProbesRequiredBeforeComparison
    OldCutset.canonicalP11Level44OldspaceSameObjectCutsetBoundary ≡ false
oldspaceNoFurtherPrimeProbe = refl

oldspaceSameObjectMapStillProducer :
  OldCutset.actualEichlerJacquetLanglandsComparisonConstructed
    OldCutset.canonicalP11Level44OldspaceSameObjectCutsetBoundary ≡ false
oldspaceSameObjectMapStillProducer = refl

frobeniusSelectorAlgebraClosedAfterRealization :
  Frobenius.downstreamSelectorAlgebraStillMissingAfterRealization
    Frobenius.canonicalGeometricSupersingularFrobeniusSelectorBoundary ≡ false
frobeniusSelectorAlgebraClosedAfterRealization = refl

p11SourceGeometryIsFullyFixed :
  Frobenius.GeometricallyFullyFixed Controls.P11.p11FrobeniusCarrier
p11SourceGeometryIsFullyFixed = Controls.p11GeometricallyFullyFixed

p37SourceGeometryNotFullyFixed :
  Frobenius.GeometricallyFullyFixed Controls.P37.p37FrobeniusCarrier → ⊥
p37SourceGeometryNotFullyFixed = Controls.p37NotGeometricallyFullyFixed

p43SourceGeometryNotFullyFixed :
  Frobenius.GeometricallyFullyFixed Controls.P43.p43FrobeniusCarrier → ⊥
p43SourceGeometryNotFullyFixed = Controls.p43NotGeometricallyFullyFixed

frobeniusAllPrimeRealizationStillProducer :
  Frobenius.allPrimeGeometricRealizationConstructedHere
    Frobenius.canonicalGeometricSupersingularFrobeniusSelectorBoundary ≡ false
frobeniusAllPrimeRealizationStillProducer = refl
