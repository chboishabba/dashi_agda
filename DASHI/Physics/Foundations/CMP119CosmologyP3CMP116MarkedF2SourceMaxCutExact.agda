{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3CMP116MarkedF2SourceMaxCutExact where

------------------------------------------------------------------------
-- S3a SOURCE MAX-CUT AGAINST THE ACTUAL CMP116 AUTHORITY.
--
-- CMP116 Sect. 1, (1.23)--(1.36), already supplies differentiated analytic
-- localization with surviving positive tree-distance decay.  The proof-bearing
-- source ABI and the (1.26)--(1.29) rate-split authority already exist in-repo.
-- Geometric shell summation and weighted Cauchy/Hilbert transport are also
-- downstream compilers.
--
-- Therefore the remaining selected-F2 source payment is NOT a new decay theorem
-- and NOT an abstract Hilbert-continuity theorem.  It is the SAME-OBJECT
-- application theorem:
--
--   selected differentiated F2 mark
--      = the published CMP116 marked/source coordinate,
--
-- with the published analytic radii/constants positive and uniform over the
-- selected cutoff/volume/scale family, plus the selected gauge/local semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as Shell
import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedF2HilbertMaxCutExact as Hilbert

cmp116DifferentiatedLocalizationIsImportedAuthority : ProofLevel
cmp116DifferentiatedLocalizationIsImportedAuthority =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

cmp116Equation126129RateSplitIsImportedAuthority : ProofLevel
cmp116Equation126129RateSplitIsImportedAuthority =
  Source.cmp116Equation126129RateSplitAuthorityLevel

geometricShellSummationIsCompilerOwned : ProofLevel
geometricShellSummationIsCompilerOwned =
  Shell.markedSourceGeometricShellSummationLevel

freshDifferentiatedDecayTheoremRequired : Bool
freshDifferentiatedDecayTheoremRequired = false

freshHilbertInequalityRequired : Bool
freshHilbertInequalityRequired =
  Hilbert.abstractIndependentHilbertInequalityRequired

selectedF2MarkedCoordinateAndUniformRadiusWeldRequired : Bool
selectedF2MarkedCoordinateAndUniformRadiusWeldRequired = true

selectedF2GaugeLocalSemanticsRequired : Bool
selectedF2GaugeLocalSemanticsRequired = true
