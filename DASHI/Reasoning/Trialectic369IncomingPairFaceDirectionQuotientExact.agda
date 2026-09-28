module DASHI.Reasoning.Trialectic369IncomingPairFaceDirectionQuotientExact where

------------------------------------------------------------------------
-- INCOMING T2 INVERSION QUOTIENT = FACE CENTRE + FOUR UNORIENTED DIRECTIONS
--
-- DASHI CONTRIBUTION
--
-- The participant-centered incoming observer pair is a nonary T^2 sheet.
-- Existing Base369 face geometry already decomposes that sheet as:
--
--   centre
--   +
--   (four antipodal directions x endpoint orientation).
--
-- Simultaneous trit inversion fixes the centre and swaps endpoint orientation,
-- while preserving the unoriented direction.  Therefore the five orbit
-- quotient is exactly:
--
--   centre + four unoriented face directions.
--
-- This supplies an independent GEOMETRIC authority for the T^2 / +/- quotient.
-- It does not identify the inversion with analytic Fricke transport or with an
-- external arithmetic involution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369FaceSheetPunctureIncidenceIdentityExact as Face
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- 1. NineSheet <-> literal face-sheet coordinates.
------------------------------------------------------------------------

kernelTritToSSP :
  Triadic.KernelTrit ->
  SSP.SSPTrit
kernelTritToSSP =
  Reduction.kernelToSSPTrit

sspToKernelTrit :
  SSP.SSPTrit ->
  Triadic.KernelTrit
sspToKernelTrit =
  Reduction.sspToKernelTrit

pairToFaceSheet :
  SSP.SSPTrit × SSP.SSPTrit ->
  Face.FaceSheet9
pairToFaceSheet (SSP.sspZero , SSP.sspZero) =
  Face.faceCentre
pairToFaceSheet (SSP.sspNegOne , SSP.sspNegOne) =
  Face.facePuncture Face.negNeg
pairToFaceSheet (SSP.sspNegOne , SSP.sspZero) =
  Face.facePuncture Face.negZero
pairToFaceSheet (SSP.sspNegOne , SSP.sspPosOne) =
  Face.facePuncture Face.negPos
pairToFaceSheet (SSP.sspZero , SSP.sspNegOne) =
  Face.facePuncture Face.zeroNeg
pairToFaceSheet (SSP.sspZero , SSP.sspPosOne) =
  Face.facePuncture Face.zeroPos
pairToFaceSheet (SSP.sspPosOne , SSP.sspNegOne) =
  Face.facePuncture Face.posNeg
pairToFaceSheet (SSP.sspPosOne , SSP.sspZero) =
  Face.facePuncture Face.posZero
pairToFaceSheet (SSP.sspPosOne , SSP.sspPosOne) =
  Face.facePuncture Face.posPos

faceSheetToPair :
  Face.FaceSheet9 ->
  SSP.SSPTrit × SSP.SSPTrit
faceSheetToPair =
  Face.faceSheetFreePair

facePairRoundTrip :
  (sheet : Face.FaceSheet9) ->
  pairToFaceSheet (faceSheetToPair sheet)
  ≡ sheet
facePairRoundTrip Face.faceCentre = refl
facePairRoundTrip (Face.facePuncture Face.negNeg) = refl
facePairRoundTrip (Face.facePuncture Face.negZero) = refl
facePairRoundTrip (Face.facePuncture Face.negPos) = refl
facePairRoundTrip (Face.facePuncture Face.zeroNeg) = refl
facePairRoundTrip (Face.facePuncture Face.zeroPos) = refl
facePairRoundTrip (Face.facePuncture Face.posNeg) = refl
facePairRoundTrip (Face.facePuncture Face.posZero) = refl
facePairRoundTrip (Face.facePuncture Face.posPos) = refl

pairFaceRoundTrip :
  (pair : SSP.SSPTrit × SSP.SSPTrit) ->
  faceSheetToPair (pairToFaceSheet pair)
  ≡ pair
pairFaceRoundTrip (SSP.sspNegOne , SSP.sspNegOne) = refl
pairFaceRoundTrip (SSP.sspNegOne , SSP.sspZero) = refl
pairFaceRoundTrip (SSP.sspNegOne , SSP.sspPosOne) = refl
pairFaceRoundTrip (SSP.sspZero , SSP.sspNegOne) = refl
pairFaceRoundTrip (SSP.sspZero , SSP.sspZero) = refl
pairFaceRoundTrip (SSP.sspZero , SSP.sspPosOne) = refl
pairFaceRoundTrip (SSP.sspPosOne , SSP.sspNegOne) = refl
pairFaceRoundTrip (SSP.sspPosOne , SSP.sspZero) = refl
pairFaceRoundTrip (SSP.sspPosOne , SSP.sspPosOne) = refl

nineSheetToFaceSheet :
  Triadic.NineSheet ->
  Face.FaceSheet9
nineSheetToFaceSheet (left , right) =
  pairToFaceSheet
    (kernelTritToSSP left , kernelTritToSSP right)

faceSheetToNineSheet :
  Face.FaceSheet9 ->
  Triadic.NineSheet
faceSheetToNineSheet sheet with faceSheetToPair sheet
... | left , right =
  sspToKernelTrit left , sspToKernelTrit right

------------------------------------------------------------------------
-- 2. Geometric five-way quotient.
------------------------------------------------------------------------

data FaceOrbit5 : Set where
  centreOrbit : FaceOrbit5
  horizontalOrbit : FaceOrbit5
  verticalOrbit : FaceOrbit5
  positiveDiagonalOrbit : FaceOrbit5
  negativeDiagonalOrbit : FaceOrbit5

faceDirectionOrbit :
  Face.FaceDirection4 ->
  FaceOrbit5
faceDirectionOrbit Face.horizontalDirection = horizontalOrbit
faceDirectionOrbit Face.verticalDirection = verticalOrbit
faceDirectionOrbit Face.positiveDiagonalDirection = positiveDiagonalOrbit
faceDirectionOrbit Face.negativeDiagonalDirection = negativeDiagonalOrbit

faceSheetOrbit :
  Face.FaceSheet9 ->
  FaceOrbit5
faceSheetOrbit Face.faceCentre = centreOrbit
faceSheetOrbit (Face.facePuncture puncture) =
  faceDirectionOrbit
    (Data.Product.proj₁
      (Face.punctureToDirectionOrientation puncture))

nineSheetFaceOrbit :
  Triadic.NineSheet ->
  FaceOrbit5
nineSheetFaceOrbit sheet =
  faceSheetOrbit (nineSheetToFaceSheet sheet)

canonicalFaceOrbitRepresentative :
  FaceOrbit5 ->
  Triadic.NineSheet
canonicalFaceOrbitRepresentative centreOrbit =
  sspToKernelTrit SSP.sspZero
  , sspToKernelTrit SSP.sspZero
canonicalFaceOrbitRepresentative horizontalOrbit =
  sspToKernelTrit SSP.sspPosOne
  , sspToKernelTrit SSP.sspZero
canonicalFaceOrbitRepresentative verticalOrbit =
  sspToKernelTrit SSP.sspZero
  , sspToKernelTrit SSP.sspPosOne
canonicalFaceOrbitRepresentative positiveDiagonalOrbit =
  sspToKernelTrit SSP.sspPosOne
  , sspToKernelTrit SSP.sspPosOne
canonicalFaceOrbitRepresentative negativeDiagonalOrbit =
  sspToKernelTrit SSP.sspPosOne
  , sspToKernelTrit SSP.sspNegOne

faceOrbitRepresentativeRoundTrip :
  (orbit : FaceOrbit5) ->
  nineSheetFaceOrbit
    (canonicalFaceOrbitRepresentative orbit)
  ≡ orbit
faceOrbitRepresentativeRoundTrip centreOrbit = refl
faceOrbitRepresentativeRoundTrip horizontalOrbit = refl
faceOrbitRepresentativeRoundTrip verticalOrbit = refl
faceOrbitRepresentativeRoundTrip positiveDiagonalOrbit = refl
faceOrbitRepresentativeRoundTrip negativeDiagonalOrbit = refl

------------------------------------------------------------------------
-- 3. Simultaneous inversion preserves the geometric orbit.
------------------------------------------------------------------------

faceOrbitInversionInvariant :
  (sheet : Triadic.NineSheet) ->
  nineSheetFaceOrbit (Triadic.negateNine sheet)
  ≡ nineSheetFaceOrbit sheet
faceOrbitInversionInvariant (Triadic.kNeg , Triadic.kNeg) = refl
faceOrbitInversionInvariant (Triadic.kNeg , Triadic.kZero) = refl
faceOrbitInversionInvariant (Triadic.kNeg , Triadic.kPos) = refl
faceOrbitInversionInvariant (Triadic.kZero , Triadic.kNeg) = refl
faceOrbitInversionInvariant (Triadic.kZero , Triadic.kZero) = refl
faceOrbitInversionInvariant (Triadic.kZero , Triadic.kPos) = refl
faceOrbitInversionInvariant (Triadic.kPos , Triadic.kNeg) = refl
faceOrbitInversionInvariant (Triadic.kPos , Triadic.kZero) = refl
faceOrbitInversionInvariant (Triadic.kPos , Triadic.kPos) = refl

------------------------------------------------------------------------
-- 4. Exact agreement with the existing FiveOrbit/NineOrbit quotient.
------------------------------------------------------------------------

faceOrbitToNineOrbit :
  FaceOrbit5 ->
  Triadic.NineOrbit
faceOrbitToNineOrbit centreOrbit = Triadic.zeroOrbit
faceOrbitToNineOrbit horizontalOrbit = Triadic.firstAxisOrbit
faceOrbitToNineOrbit verticalOrbit = Triadic.secondAxisOrbit
faceOrbitToNineOrbit positiveDiagonalOrbit = Triadic.equalSignOrbit
faceOrbitToNineOrbit negativeDiagonalOrbit = Triadic.oppositeSignOrbit

nineOrbitToFaceOrbit :
  Triadic.NineOrbit ->
  FaceOrbit5
nineOrbitToFaceOrbit Triadic.zeroOrbit = centreOrbit
nineOrbitToFaceOrbit Triadic.firstAxisOrbit = horizontalOrbit
nineOrbitToFaceOrbit Triadic.secondAxisOrbit = verticalOrbit
nineOrbitToFaceOrbit Triadic.equalSignOrbit = positiveDiagonalOrbit
nineOrbitToFaceOrbit Triadic.oppositeSignOrbit = negativeDiagonalOrbit

faceNineOrbitRoundTrip :
  (orbit : FaceOrbit5) ->
  nineOrbitToFaceOrbit (faceOrbitToNineOrbit orbit)
  ≡ orbit
faceNineOrbitRoundTrip centreOrbit = refl
faceNineOrbitRoundTrip horizontalOrbit = refl
faceNineOrbitRoundTrip verticalOrbit = refl
faceNineOrbitRoundTrip positiveDiagonalOrbit = refl
faceNineOrbitRoundTrip negativeDiagonalOrbit = refl

nineFaceOrbitRoundTrip :
  (orbit : Triadic.NineOrbit) ->
  faceOrbitToNineOrbit (nineOrbitToFaceOrbit orbit)
  ≡ orbit
nineFaceOrbitRoundTrip Triadic.zeroOrbit = refl
nineFaceOrbitRoundTrip Triadic.firstAxisOrbit = refl
nineFaceOrbitRoundTrip Triadic.secondAxisOrbit = refl
nineFaceOrbitRoundTrip Triadic.equalSignOrbit = refl
nineFaceOrbitRoundTrip Triadic.oppositeSignOrbit = refl

genericQuotientAgreesWithFaceDirectionQuotient :
  (sheet : Triadic.NineSheet) ->
  Triadic.quotientNine sheet
  ≡ faceOrbitToNineOrbit (nineSheetFaceOrbit sheet)
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kNeg , Triadic.kNeg) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kNeg , Triadic.kZero) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kNeg , Triadic.kPos) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kZero , Triadic.kNeg) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kZero , Triadic.kZero) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kZero , Triadic.kPos) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kPos , Triadic.kNeg) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kPos , Triadic.kZero) = refl
genericQuotientAgreesWithFaceDirectionQuotient
  (Triadic.kPos , Triadic.kPos) = refl

------------------------------------------------------------------------
-- 5. Authority firewall.
------------------------------------------------------------------------

data GeometricAntipodalQuotientIsAnalyticFricke : Set where
data GeometricAntipodalQuotientIsArithmeticOggInvolution : Set where

geometricQuotientNotPromotedToAnalyticFricke :
  GeometricAntipodalQuotientIsAnalyticFricke -> ⊥
geometricQuotientNotPromotedToAnalyticFricke ()

geometricQuotientNotPromotedToArithmeticOggInvolution :
  GeometricAntipodalQuotientIsArithmeticOggInvolution -> ⊥
geometricQuotientNotPromotedToArithmeticOggInvolution ()

record Trialectic369IncomingPairFaceDirectionQuotientBoundary : Set where
  constructor trialectic-369-incoming-pair-face-direction-quotient-boundary
  field
    incomingNineSheetToFaceSheetBidiShapeOwned : Bool
    faceSheetCentrePlusEightOwned : Bool
    puncturedEightDirectionOrientationDecompositionReused : Bool
    inversionPreservesUnorientedDirection : Bool
    faceCentrePlusFourDirectionsQuotientPaid : Bool
    agreesWithExistingNineOrbitQuotient : Bool
    geometricAuthorityForIncomingQuotientPaid : Bool
    analyticFrickeIdentificationPaid : Bool
    arithmeticOggInvolutionIdentificationPaid : Bool

canonicalTrialectic369IncomingPairFaceDirectionQuotientBoundary :
  Trialectic369IncomingPairFaceDirectionQuotientBoundary
canonicalTrialectic369IncomingPairFaceDirectionQuotientBoundary =
  trialectic-369-incoming-pair-face-direction-quotient-boundary
    true true true true true true true
    false false
