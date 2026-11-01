module DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryReconstructionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdmissibleReconstructionEquivalenceExact as R
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChiralMolecularSeparatingPairExact as C
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinDNA3DAdapterExact as B

------------------------------------------------------------------------
-- RED/GREEN validation root for the symmetry-resolved molecular tranche.
-- This must fail while the three owners above are absent.  After they exist,
-- checking this module requires the exact reconstruction equivalence, the
-- chirality separating-pair obstruction, and the protein/DNA adapters.
------------------------------------------------------------------------

reconstructionRegression :
  R.AdmissibleReconstructionBoundary.richStateEquivalentToAdmissibleSurfaceResidualSigma
    R.canonicalAdmissibleReconstructionBoundary
  ≡ true
reconstructionRegression = refl

chiralityRegression :
  C.ChiralSeparatingPairBoundary.sameCoarseChart
    C.canonicalChiralSeparatingPairBoundary
  ≡ true
  × C.ChiralSeparatingPairBoundary.chiralityResidualSeparates
    C.canonicalChiralSeparatingPairBoundary
  ≡ true
  × C.ChiralSeparatingPairBoundary.chiralitySensitiveObservableFactorsThroughCoarseChart
    C.canonicalChiralSeparatingPairBoundary
  ≡ false
chiralityRegression = refl , (refl , refl)

proteinDNARegression :
  B.ProteinDNA3DAdapterBoundary.dnaUsesExactCoordinateBijection
    B.canonicalProteinDNA3DAdapterBoundary
  ≡ true
  × B.ProteinDNA3DAdapterBoundary.dnaPhysicalGeometryUsesRigidMotionComposition
    B.canonicalProteinDNA3DAdapterBoundary
  ≡ true
  × B.ProteinDNA3DAdapterBoundary.proteinSequenceDefinitionallyDeterminesUniqueConformation
    B.canonicalProteinDNA3DAdapterBoundary
  ≡ false
proteinDNARegression = refl , (refl , refl)
