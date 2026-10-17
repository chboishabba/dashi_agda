module DASHI.Moonshine.OggSSPClimbingGymBishopPhaseCellValidation where

open import DASHI.Core.Prelude

import Real as BishopReal

import DASHI.Moonshine.OggSSPClimbingGymBishopPhaseCellExact as PhaseCell
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

certifiedPhaseCompilesAtEveryWall :
  (form : Gym.WallForm) →
  (phase : BishopReal.ℝ) →
  PhaseCell.CertifiedWallPhaseCell form phase →
  PhaseCell.WallRadixAddress form
certifiedPhaseCompilesAtEveryWall = PhaseCell.certifiedWallPhaseAddress

compilerNeedsNoTotalFloor :
  PhaseCell.totalRealFloorRequired
    PhaseCell.canonicalBishopPhaseCellBoundary
  ≡ false
compilerNeedsNoTotalFloor = refl

analyticPhaseCertificateStillRequired :
  PhaseCell.actualZeroPhaseCellCertificatesConstructed
    PhaseCell.canonicalBishopPhaseCellBoundary
  ≡ false
analyticPhaseCertificateStillRequired = refl
