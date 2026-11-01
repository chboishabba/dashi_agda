{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalPhysicalTransferGapObligationExact where

open import Agda.Builtin.Bool using (Bool; false)

import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- The generic clustering/OS4 -> PositiveTransferGap compiler is already owned
-- non-Round by `BalabanClayT5ClusteringToTransferGapExact`.  The historical
-- `positiveTransferGap` frontier therefore contracts to the selected-object
-- physical premises needed to invoke that compiler, not another copy of it.
------------------------------------------------------------------------

record SelectedPhysicalTransferGapObligation
    {Measure Schwinger Observable Energy Bound : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger)
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    selectedOS4Interpretation : Gap.OS4SpectralInterpretation closure spectrum
    selectedContinuumClustering :
      Limit.Clustered closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))

open SelectedPhysicalTransferGapObligation public

positiveTransferGapFromSelectedPhysicalObligation :
  ∀ {Measure Schwinger Observable Energy Bound}
    {closure : Limit.FiniteToContinuumOSClosure Measure Schwinger}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  SelectedPhysicalTransferGapObligation closure spectrum →
  Gap.PositiveTransferGap spectrum
positiveTransferGapFromSelectedPhysicalObligation obligation =
  Gap.positiveTransferGapFromOS4
    (selectedOS4Interpretation obligation)
    (selectedContinuumClustering obligation)

selectedPhysicalTransferGapPaidByExtraction : Bool
selectedPhysicalTransferGapPaidByExtraction = false
