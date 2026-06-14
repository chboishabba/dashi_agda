module DASHI.Physics.Closure.PerelmanBTAnalogueImportSmoke where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.BTBallVolumeArithmetic as Ball
import DASHI.Physics.Closure.BTCanonicalNeckAnalogue as Neck
import DASHI.Physics.Closure.BTGaussianReducedVolumeSurface as Gaussian
import DASHI.Physics.Closure.GeometryAnalogueClassification as Geometry
import DASHI.Physics.Closure.JSJAnaloguePieceClassification as JSJ
import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObstruction as Surgery

record PerelmanBTAnalogueImportSmoke : Set where
  field
    ballVolumeArithmeticWitness :
      Ball.T3xT2xT7Sphere111Is96 ≡ Ball.T3xT2xT7Sphere111Is96

    canonicalNeckWitness :
      Neck.p2PathCylinderConstructed ≡ Neck.p2PathCylinderConstructed

    gaussianReducedVolumeWitness :
      Gaussian.canonicalSurfaceRowsRecorded
      ≡
      Gaussian.canonicalSurfaceRowsRecorded

    geometryAnalogueWitness :
      Geometry.classificationBTProductTreeNonArch
      ≡
      Geometry.classificationBTProductTreeNonArch

    jsjAnaloguePieceWitness :
      JSJ.canonicalReceiptKeepsPromotionFlagsEmpty
      ≡
      JSJ.canonicalReceiptKeepsPromotionFlagsEmpty

    surgeryCanonicalNeighborhoodWitness :
      Surgery.oneMinusObstructionCandidate
      ≡
      Surgery.oneMinusObstructionCandidate

open PerelmanBTAnalogueImportSmoke public

perelmanBTAnalogueImportSmoke :
  PerelmanBTAnalogueImportSmoke
perelmanBTAnalogueImportSmoke =
  record
    { ballVolumeArithmeticWitness =
        refl
    ; canonicalNeckWitness =
        refl
    ; gaussianReducedVolumeWitness =
        refl
    ; geometryAnalogueWitness =
        refl
    ; jsjAnaloguePieceWitness =
        refl
    ; surgeryCanonicalNeighborhoodWitness =
        refl
    }
