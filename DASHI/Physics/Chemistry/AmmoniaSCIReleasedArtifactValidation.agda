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
  A.ReleasedSelectedCIArtifact.selectedGroundEnergyMicroHartreeMagnitude
    A.nh3SelectedCI64Artifact ≡ 55517555
selectedEnergyReceiptRecorded = refl

paperAndArtifactNotCollapsed :
  A.ReleasedArtifactBoundary.paperBenchmarkAndArtifactAreSameNumericalObject
    A.canonicalReleasedArtifactBoundary ≡ false
paperAndArtifactNotCollapsed = refl

literalMatrixBytesNotVendored :
  A.ReleasedArtifactBoundary.matrixBytesVendoredIntoDASHI
    A.canonicalReleasedArtifactBoundary ≡ false
literalMatrixBytesNotVendored = refl
