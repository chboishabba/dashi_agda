module DASHI.Physics.Closure.BTGaussianDiagonalInputRows where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BTProductDiagonalGrowthArithmetic as Growth
import DASHI.Physics.Closure.BTGaussianReducedVolumeSurface as Surface

------------------------------------------------------------------------
-- Exact diagonal input rows for the BT Gaussian reduced-volume surface.
--
-- The exactSphere and exactBall columns are exact product-tree diagonal
-- counts from BTProductDiagonalGrowthArithmetic.  The envelope and
-- shellWeightSurrogate columns are the 8 * 42^r Nat surrogate consumed
-- by BTGaussianReducedVolumeSurface.  This file records only finite
-- r=0..3 input rows and definitional arithmetic witnesses; it does not
-- assert convergence, monotonicity, or any inequality between exact and
-- surrogate columns.

data NumericColumnKind : Set where
  exactProductDiagonal :
    NumericColumnKind

  gaussianSurfaceSurrogate :
    NumericColumnKind

exactProductDiagonalText :
  String
exactProductDiagonalText =
  "exact product diagonal count"

gaussianSurfaceSurrogateText :
  String
gaussianSurfaceSurrogateText =
  "Gaussian reduced-volume surface surrogate"

record BTGaussianDiagonalInputRow : Set where
  field
    radius :
      Nat

    radiusSquared :
      Nat

    radiusSquaredIsComputed :
      radiusSquared ≡ Surface.squareNat radius

    radiusSquaredKind :
      NumericColumnKind

    radiusSquaredKindIsExact :
      radiusSquaredKind ≡ exactProductDiagonal

    radiusSquaredText :
      String

    exactSphere :
      Nat

    exactSphereIsComputed :
      exactSphere ≡ Growth.diagonalProductSphereCount radius

    exactSphereKind :
      NumericColumnKind

    exactSphereKindIsExact :
      exactSphereKind ≡ exactProductDiagonal

    exactSphereText :
      String

    exactBall :
      Nat

    exactBallIsComputed :
      exactBall ≡ Growth.diagonalProductBallCount radius

    exactBallKind :
      NumericColumnKind

    exactBallKindIsExact :
      exactBallKind ≡ exactProductDiagonal

    exactBallText :
      String

    envelope :
      Nat

    envelopeIsComputed :
      envelope ≡ Growth.diagonalEnvelope radius

    envelopeKind :
      NumericColumnKind

    envelopeKindIsSurrogate :
      envelopeKind ≡ gaussianSurfaceSurrogate

    envelopeText :
      String

    shellWeightSurrogate :
      Nat

    shellWeightSurrogateIsComputed :
      shellWeightSurrogate ≡ Surface.shellWeightSurrogate radius

    shellWeightSurrogateKind :
      NumericColumnKind

    shellWeightSurrogateKindIsSurrogate :
      shellWeightSurrogateKind ≡ gaussianSurfaceSurrogate

    shellWeightSurrogateText :
      String

open BTGaussianDiagonalInputRow public

diagonalInputRow0 :
  BTGaussianDiagonalInputRow
diagonalInputRow0 =
  record
    { radius =
        0
    ; radiusSquared =
        0
    ; radiusSquaredIsComputed =
        refl
    ; radiusSquaredKind =
        exactProductDiagonal
    ; radiusSquaredKindIsExact =
        refl
    ; radiusSquaredText =
        exactProductDiagonalText
    ; exactSphere =
        1
    ; exactSphereIsComputed =
        refl
    ; exactSphereKind =
        exactProductDiagonal
    ; exactSphereKindIsExact =
        refl
    ; exactSphereText =
        exactProductDiagonalText
    ; exactBall =
        1
    ; exactBallIsComputed =
        refl
    ; exactBallKind =
        exactProductDiagonal
    ; exactBallKindIsExact =
        refl
    ; exactBallText =
        exactProductDiagonalText
    ; envelope =
        8
    ; envelopeIsComputed =
        refl
    ; envelopeKind =
        gaussianSurfaceSurrogate
    ; envelopeKindIsSurrogate =
        refl
    ; envelopeText =
        gaussianSurfaceSurrogateText
    ; shellWeightSurrogate =
        8
    ; shellWeightSurrogateIsComputed =
        refl
    ; shellWeightSurrogateKind =
        gaussianSurfaceSurrogate
    ; shellWeightSurrogateKindIsSurrogate =
        refl
    ; shellWeightSurrogateText =
        gaussianSurfaceSurrogateText
    }

diagonalInputRow1 :
  BTGaussianDiagonalInputRow
diagonalInputRow1 =
  record
    { radius =
        1
    ; radiusSquared =
        1
    ; radiusSquaredIsComputed =
        refl
    ; radiusSquaredKind =
        exactProductDiagonal
    ; radiusSquaredKindIsExact =
        refl
    ; radiusSquaredText =
        exactProductDiagonalText
    ; exactSphere =
        96
    ; exactSphereIsComputed =
        refl
    ; exactSphereKind =
        exactProductDiagonal
    ; exactSphereKindIsExact =
        refl
    ; exactSphereText =
        exactProductDiagonalText
    ; exactBall =
        180
    ; exactBallIsComputed =
        refl
    ; exactBallKind =
        exactProductDiagonal
    ; exactBallKindIsExact =
        refl
    ; exactBallText =
        exactProductDiagonalText
    ; envelope =
        336
    ; envelopeIsComputed =
        refl
    ; envelopeKind =
        gaussianSurfaceSurrogate
    ; envelopeKindIsSurrogate =
        refl
    ; envelopeText =
        gaussianSurfaceSurrogateText
    ; shellWeightSurrogate =
        336
    ; shellWeightSurrogateIsComputed =
        refl
    ; shellWeightSurrogateKind =
        gaussianSurfaceSurrogate
    ; shellWeightSurrogateKindIsSurrogate =
        refl
    ; shellWeightSurrogateText =
        gaussianSurfaceSurrogateText
    }

diagonalInputRow2 :
  BTGaussianDiagonalInputRow
diagonalInputRow2 =
  record
    { radius =
        2
    ; radiusSquared =
        4
    ; radiusSquaredIsComputed =
        refl
    ; radiusSquaredKind =
        exactProductDiagonal
    ; radiusSquaredKindIsExact =
        refl
    ; radiusSquaredText =
        exactProductDiagonalText
    ; exactSphere =
        4032
    ; exactSphereIsComputed =
        refl
    ; exactSphereKind =
        exactProductDiagonal
    ; exactSphereKindIsExact =
        refl
    ; exactSphereText =
        exactProductDiagonalText
    ; exactBall =
        11050
    ; exactBallIsComputed =
        refl
    ; exactBallKind =
        exactProductDiagonal
    ; exactBallKindIsExact =
        refl
    ; exactBallText =
        exactProductDiagonalText
    ; envelope =
        14112
    ; envelopeIsComputed =
        refl
    ; envelopeKind =
        gaussianSurfaceSurrogate
    ; envelopeKindIsSurrogate =
        refl
    ; envelopeText =
        gaussianSurfaceSurrogateText
    ; shellWeightSurrogate =
        14112
    ; shellWeightSurrogateIsComputed =
        refl
    ; shellWeightSurrogateKind =
        gaussianSurfaceSurrogate
    ; shellWeightSurrogateKindIsSurrogate =
        refl
    ; shellWeightSurrogateText =
        gaussianSurfaceSurrogateText
    }

diagonalInputRow3 :
  BTGaussianDiagonalInputRow
diagonalInputRow3 =
  record
    { radius =
        3
    ; radiusSquared =
        9
    ; radiusSquaredIsComputed =
        refl
    ; radiusSquaredKind =
        exactProductDiagonal
    ; radiusSquaredKindIsExact =
        refl
    ; radiusSquaredText =
        exactProductDiagonalText
    ; exactSphere =
        169344
    ; exactSphereIsComputed =
        refl
    ; exactSphereKind =
        exactProductDiagonal
    ; exactSphereKindIsExact =
        refl
    ; exactSphereText =
        exactProductDiagonalText
    ; exactBall =
        532862
    ; exactBallIsComputed =
        refl
    ; exactBallKind =
        exactProductDiagonal
    ; exactBallKindIsExact =
        refl
    ; exactBallText =
        exactProductDiagonalText
    ; envelope =
        592704
    ; envelopeIsComputed =
        refl
    ; envelopeKind =
        gaussianSurfaceSurrogate
    ; envelopeKindIsSurrogate =
        refl
    ; envelopeText =
        gaussianSurfaceSurrogateText
    ; shellWeightSurrogate =
        592704
    ; shellWeightSurrogateIsComputed =
        refl
    ; shellWeightSurrogateKind =
        gaussianSurfaceSurrogate
    ; shellWeightSurrogateKindIsSurrogate =
        refl
    ; shellWeightSurrogateText =
        gaussianSurfaceSurrogateText
    }

canonicalBTGaussianDiagonalInputRows :
  List BTGaussianDiagonalInputRow
canonicalBTGaussianDiagonalInputRows =
  diagonalInputRow0
  ∷ diagonalInputRow1
  ∷ diagonalInputRow2
  ∷ diagonalInputRow3
  ∷ []

row0EnvelopeMatchesShellWeightSurrogate :
  envelope diagonalInputRow0 ≡ shellWeightSurrogate diagonalInputRow0
row0EnvelopeMatchesShellWeightSurrogate =
  refl

row1EnvelopeMatchesShellWeightSurrogate :
  envelope diagonalInputRow1 ≡ shellWeightSurrogate diagonalInputRow1
row1EnvelopeMatchesShellWeightSurrogate =
  refl

row2EnvelopeMatchesShellWeightSurrogate :
  envelope diagonalInputRow2 ≡ shellWeightSurrogate diagonalInputRow2
row2EnvelopeMatchesShellWeightSurrogate =
  refl

row3EnvelopeMatchesShellWeightSurrogate :
  envelope diagonalInputRow3 ≡ shellWeightSurrogate diagonalInputRow3
row3EnvelopeMatchesShellWeightSurrogate =
  refl
