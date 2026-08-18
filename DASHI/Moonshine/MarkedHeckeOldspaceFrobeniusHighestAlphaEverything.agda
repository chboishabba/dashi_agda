module DASHI.Moonshine.MarkedHeckeOldspaceFrobeniusHighestAlphaEverything where

------------------------------------------------------------------------
-- Highest-alpha convergence root after PR #585's oldspace / isotypic tranche.
--
-- This root intentionally consumes theorem surfaces from the two now-sharp
-- global cutsets rather than adding another observer or receipt layer:
--
--   (A) p=11 level-44 same-object cutset
--       analytic V1/V2/V4 good-prime oldspace
--          <-> marked quaternion/deck permutation module;
--
--   (B) supersingular Frobenius selector cutset
--       construct actual Frobenius normal-form realization for general p;
--       all-fixed <=> g(X0+(p))=0 and finite-control Ogg consequences then
--       follow from the generic theorem already proved.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MarkedHeckeDeckCollisionEverything as Marked
import DASHI.Moonshine.P11Level44OldspaceSameObjectCutsetExact as OldCutset
import DASHI.Moonshine.GeometricSupersingularFrobeniusSelectorConsequenceExact as Frobenius

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

frobeniusAllPrimeRealizationStillProducer :
  Frobenius.allPrimeGeometricRealizationConstructedHere
    Frobenius.canonicalGeometricSupersingularFrobeniusSelectorBoundary ≡ false
frobeniusAllPrimeRealizationStillProducer = refl
