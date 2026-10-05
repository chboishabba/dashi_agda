{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261005TExact where

------------------------------------------------------------------------
-- OVERLAY T / 2026-10-05: SOURCE-CONSTRUCTION FRONTIER AFTER S3a CORRECTION.
--
-- Overlay S still charged an equality between the selected F^2 marked source
-- and the R129 stress-lane marked source.  That is not required and is the
-- wrong same-object boundary: stress and F^2 are distinct insertions/operators.
-- They need the SAME completed Composite carrier, not the SAME marked-source
-- data record.
--
-- The Local-C rechart now consumes a separately constructed physical marked
-- curvature/F^2 family on the exact carrier.  The Haar lane is also tightened:
-- choose each quadrature weight to be the exact source/Haar cell mass.  Then
-- mass discrepancy is identically zero and only the shrinking-cell oscillation
-- theorem remains geometric.
--
-- Preferred frontier:
--
--   T1  construct the actual CMP109/116 one-parameter Background path and its
--       B4-equivariant compact/source geometry on the literal Background;
--
--   T2  instantiate/prove the renormalized Hilbert/Weyl Ward identity on the
--       exact pinned Local-C stress/F^2 pair;
--
--   T3  construct the physical marked F^2 source family on the exact completed
--       Composite carrier (NO equality to the stress marked source);
--
--   T4  construct literal product-Haar cells/nodes with exact Haar cell masses
--       and prove the selected integrand's cell oscillation budget vanishes.
--
-- T2 is the one standard imported analytic authority.  T1/T3/T4 are concrete
-- source constructions.  All covariance/rechart/common-limit/sign transport
-- below them is compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyP1PreferredPathDefinedPresentCutExact as P1
import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3DistinctF2MarkedSourceSameCarrierExact as P3
import DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExact as P3Limit
import DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureExact as ExactMass

remainingNovelSourceConstructionCount : Nat
remainingNovelSourceConstructionCount = 3

remainingStandardImportedAuthorityCount : Nat
remainingStandardImportedAuthorityCount = 1

------------------------------------------------------------------------
-- T1: actual CMP109/116 source/background path geometry.
------------------------------------------------------------------------

actualCMP109116BackgroundPathConstructionRequired : Bool
actualCMP109116BackgroundPathConstructionRequired =
  P1.remainingQ1LeafIsActualB4EquivariantSourcePath

primitiveSignedCovarianceRequired : Bool
primitiveSignedCovarianceRequired = false

------------------------------------------------------------------------
-- T2: renormalized Hilbert/Weyl Ward identity on exact Local-C pair.
------------------------------------------------------------------------

renormalizedHilbertWeylWardAuthorityRequired : Bool
renormalizedHilbertWeylWardAuthorityRequired =
  P2.remainingR2WorkIsInstantiationOfStandardWardAuthority

freeTraceCalibrationRequired : Bool
freeTraceCalibrationRequired = false

------------------------------------------------------------------------
-- T3: physical marked F^2 source, distinct from stress source.
------------------------------------------------------------------------

stressMarkedSourceEqualsF2MarkedSourceRequired : Bool
stressMarkedSourceEqualsF2MarkedSourceRequired =
  P3.oldS3aStressSourceEqualityIsRequired

physicalMarkedF2SourceConstructionRequired : Bool
physicalMarkedF2SourceConstructionRequired =
  P3.remainingF2WorkIsConstructPhysicalMarkedF2Source

sameCarrierIsSufficientForLocalCRechart : Bool
sameCarrierIsSufficientForLocalCRechart =
  P3.r129StressMarkedSourceEqualityNotRequiredForLocalCRechart

------------------------------------------------------------------------
-- T4: literal product Haar geometry.
------------------------------------------------------------------------

productHaarQuadratureGeometryRequired : Bool
productHaarQuadratureGeometryRequired = true

cellOscillationEstimateStillPhysical : Bool
cellOscillationEstimateStillPhysical = true

massDiscrepancyEstimateStillPhysical : Bool
massDiscrepancyEstimateStillPhysical =
  ExactMass.independentMassDiscrepancyEstimateRequired

exactHaarCellMassEliminatesDiscrepancy : Bool
exactHaarCellMassEliminatesDiscrepancy =
  ExactMass.exactCellMassEliminatesMassDiscrepancy

commonLimitAfterHaarGeometryIsCompilerOwned : Bool
commonLimitAfterHaarGeometryIsCompilerOwned =
  P3Limit.compiledCommonLimitNeedsNoPointwiseSourceWeld

------------------------------------------------------------------------
-- Retired lanes / trust accounting.
------------------------------------------------------------------------

oldS3aStressSourceIdentityRetired : Bool
oldS3aStressSourceIdentityRetired = true

finiteDGammaR109TailRouteRequired : Bool
finiteDGammaR109TailRouteRequired = false

eq223VacuumGapRouteRequired : Bool
eq223VacuumGapRouteRequired = false

remainingAdapterDebt : Nat
remainingAdapterDebt = 0

noSyntheticPhysicalIdentificationAdded : Bool
noSyntheticPhysicalIdentificationAdded = true
