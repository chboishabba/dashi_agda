module DASHI.Physics.Chemistry.AmmoniaSCIReleasedArtifactValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaSCIReleasedArtifactExact as A

matrixDimension64 :
  A.ReleasedSelectedCIArtifact.matrixDimension A.nh3SelectedCI64Artifact ≡ 64
matrixDimension64 = refl

matrixBlobRecorded :
  A.ReleasedSelectedCIArtifact.gitBlobSHA A.nh3SelectedCI64Artifact ≡
  "07541705a0305e75dab1de5bc1b8324d66fee778"
matrixBlobRecorded = refl

selectedEnergyReceiptRecorded :
  A.ReleasedSelectedCIArtifact.selectedGroundEnergyNanoHartreeMagnitude
    A.nh3SelectedCI64Artifact ≡ 55517555010
selectedEnergyReceiptRecorded = refl

releasedFCIEnergyReceiptRecorded :
  A.ReleasedFCIRunMetadata.groundEnergyNanoHartreeMagnitude
    A.nh3ReleasedFCIRunMetadata ≡ 55519414318
releasedFCIEnergyReceiptRecorded = refl

paperAndArtifactNotCollapsed :
  A.ReleasedArtifactBoundary.paperBenchmarkAndArtifactAreSameNumericalObject
    A.canonicalReleasedArtifactBoundary ≡ false
paperAndArtifactNotCollapsed = refl

literalMatrixBytesNotVendored :
  A.ReleasedArtifactBoundary.matrixBytesVendoredIntoDASHI
    A.canonicalReleasedArtifactBoundary ≡ false
literalMatrixBytesNotVendored = refl

matrixNotIndependentlyRediagonalized :
  A.ReleasedArtifactBoundary.matrixIndependentlyRediagonalizedByDASHI
    A.canonicalReleasedArtifactBoundary ≡ false
matrixNotIndependentlyRediagonalized = refl
