module DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact where

------------------------------------------------------------------------
-- LOSSLESS QUOTIENT + DEPENDENT RESIDUAL CODEC
--
-- BalancedTernaryAntipodalOrbitExact constructs the 27 -> 14 strict-antipodal
-- quotient.  This module supplies the missing exact reconstruction theorem.
-- The centre class has no orientation degree of freedom; every noncentral class
-- has one direct/counter orientation.  The residual type therefore depends on
-- the quotient stratum.
--
-- This is the exact finite pattern used throughout DASHI's coarse/fine and
-- p-adic residual towers:
--
--   fine state  ~=  Sigma coarseClass (Residual coarseClass).
--
-- No information is lost by the codec.  Information is lost only if the
-- residual is discarded.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube

data Orientation2 : Set where
  direct counter : Orientation2

OrientationResidual27 : Orbit.AntipodalClass27 → Set
OrientationResidual27 Orbit.centre27 = ⊤
OrientationResidual27 (Orbit.firstPositive27 b c) = Orientation2
OrientationResidual27 (Orbit.secondPositive27 c) = Orientation2
OrientationResidual27 Orbit.thirdPositive27 = Orientation2

record AntipodalCode27 : Set where
  constructor antipodalCode27
  field
    coarseClass : Orbit.AntipodalClass27
    orientationResidual : OrientationResidual27 coarseClass

open AntipodalCode27 public

rebuildCode27 :
  (code : AntipodalCode27) →
  antipodalCode27 (coarseClass code) (orientationResidual code) ≡ code
rebuildCode27 (antipodalCode27 coarse residual) = refl

encode27 : Orbit.TritTriple → AntipodalCode27
encode27 (Branch.triple SSP.sspPosOne b c) =
  antipodalCode27 (Orbit.firstPositive27 b c) direct
encode27 (Branch.triple SSP.sspNegOne b c) =
  antipodalCode27
    (Orbit.firstPositive27 (Orbit.strictAntipode b) (Orbit.strictAntipode c))
    counter
encode27 (Branch.triple SSP.sspZero SSP.sspPosOne c) =
  antipodalCode27 (Orbit.secondPositive27 c) direct
encode27 (Branch.triple SSP.sspZero SSP.sspNegOne c) =
  antipodalCode27 (Orbit.secondPositive27 (Orbit.strictAntipode c)) counter
encode27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) =
  antipodalCode27 Orbit.thirdPositive27 direct
encode27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) =
  antipodalCode27 Orbit.thirdPositive27 counter
encode27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) =
  antipodalCode27 Orbit.centre27 tt

decode27 : AntipodalCode27 → Orbit.TritTriple
decode27 (antipodalCode27 Orbit.centre27 tt) =
  Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
decode27 (antipodalCode27 (Orbit.firstPositive27 b c) direct) =
  Branch.triple SSP.sspPosOne b c
decode27 (antipodalCode27 (Orbit.firstPositive27 b c) counter) =
  Branch.triple SSP.sspNegOne (Orbit.strictAntipode b) (Orbit.strictAntipode c)
decode27 (antipodalCode27 (Orbit.secondPositive27 c) direct) =
  Branch.triple SSP.sspZero SSP.sspPosOne c
decode27 (antipodalCode27 (Orbit.secondPositive27 c) counter) =
  Branch.triple SSP.sspZero SSP.sspNegOne (Orbit.strictAntipode c)
decode27 (antipodalCode27 Orbit.thirdPositive27 direct) =
  Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne
decode27 (antipodalCode27 Orbit.thirdPositive27 counter) =
  Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne

decodeAfterEncode27 : (triple : Orbit.TritTriple) → decode27 (encode27 triple) ≡ triple
decodeAfterEncode27 (Branch.triple SSP.sspPosOne b c) = refl
decodeAfterEncode27 (Branch.triple SSP.sspNegOne b c)
  rewrite Orbit.strictAntipodeInvolutive b | Orbit.strictAntipodeInvolutive c = refl
decodeAfterEncode27 (Branch.triple SSP.sspZero SSP.sspPosOne c) = refl
decodeAfterEncode27 (Branch.triple SSP.sspZero SSP.sspNegOne c)
  rewrite Orbit.strictAntipodeInvolutive c = refl
decodeAfterEncode27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
decodeAfterEncode27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
decodeAfterEncode27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = refl

encodeAfterDecode27 : (code : AntipodalCode27) → encode27 (decode27 code) ≡ code
encodeAfterDecode27 (antipodalCode27 Orbit.centre27 tt) = refl
encodeAfterDecode27 (antipodalCode27 (Orbit.firstPositive27 b c) direct) = refl
encodeAfterDecode27 (antipodalCode27 (Orbit.firstPositive27 b c) counter)
  rewrite Orbit.strictAntipodeInvolutive b | Orbit.strictAntipodeInvolutive c = refl
encodeAfterDecode27 (antipodalCode27 (Orbit.secondPositive27 c) direct) = refl
encodeAfterDecode27 (antipodalCode27 (Orbit.secondPositive27 c) counter)
  rewrite Orbit.strictAntipodeInvolutive c = refl
encodeAfterDecode27 (antipodalCode27 Orbit.thirdPositive27 direct) = refl
encodeAfterDecode27 (antipodalCode27 Orbit.thirdPositive27 counter) = refl

coarseOfEncodeIsClassifier :
  (triple : Orbit.TritTriple) →
  coarseClass (encode27 triple) ≡ Orbit.classifyAntipodal27 triple
coarseOfEncodeIsClassifier (Branch.triple SSP.sspPosOne b c) = refl
coarseOfEncodeIsClassifier (Branch.triple SSP.sspNegOne b c) = refl
coarseOfEncodeIsClassifier (Branch.triple SSP.sspZero SSP.sspPosOne c) = refl
coarseOfEncodeIsClassifier (Branch.triple SSP.sspZero SSP.sspNegOne c) = refl
coarseOfEncodeIsClassifier (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
coarseOfEncodeIsClassifier (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
coarseOfEncodeIsClassifier (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = refl

interactionTriple : Cube.InteractionCube → Orbit.TritTriple
interactionTriple (Cube.interactionCube a b c) = Branch.triple a b c

interactionFromTriple : Orbit.TritTriple → Cube.InteractionCube
interactionFromTriple (Branch.triple a b c) = Cube.interactionCube a b c

interactionTripleFromTriple :
  (triple : Orbit.TritTriple) →
  interactionTriple (interactionFromTriple triple) ≡ triple
interactionTripleFromTriple (Branch.triple a b c) = refl

appraisalTriple : Cube.ParticipantAppraisal → Orbit.TritTriple
appraisalTriple (Cube.participantAppraisal a b c) = Branch.triple a b c

appraisalFromTriple : Orbit.TritTriple → Cube.ParticipantAppraisal
appraisalFromTriple (Branch.triple a b c) = Cube.participantAppraisal a b c

appraisalTripleFromTriple :
  (triple : Orbit.TritTriple) →
  appraisalTriple (appraisalFromTriple triple) ≡ triple
appraisalTripleFromTriple (Branch.triple a b c) = refl

record ThreeBlockResidualCode : Set where
  constructor threeBlockResidualCode
  field
    interactionCode : AntipodalCode27
    appraisalACode : AntipodalCode27
    appraisalBCode : AntipodalCode27

open ThreeBlockResidualCode public

encodeRound : Cube.OneRoundInteractionState → ThreeBlockResidualCode
encodeRound
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA appraisalB)) =
  threeBlockResidualCode
    (encode27 (interactionTriple interaction))
    (encode27 (appraisalTriple appraisalA))
    (encode27 (appraisalTriple appraisalB))

decodeRound : ThreeBlockResidualCode → Cube.OneRoundInteractionState
decodeRound (threeBlockResidualCode interaction appraisalA appraisalB) =
  Cube.oneRoundInteractionState
    (interactionFromTriple (decode27 interaction))
    (Cube.appraisalFibre
      (appraisalFromTriple (decode27 appraisalA))
      (appraisalFromTriple (decode27 appraisalB)))

decodeAfterEncodeRound :
  (state : Cube.OneRoundInteractionState) → decodeRound (encodeRound state) ≡ state
decodeAfterEncodeRound
  (Cube.oneRoundInteractionState
    (Cube.interactionCube i1 i2 i3)
    (Cube.appraisalFibre
      (Cube.participantAppraisal a1 a2 a3)
      (Cube.participantAppraisal b1 b2 b3)))
  rewrite decodeAfterEncode27 (Branch.triple i1 i2 i3)
        | decodeAfterEncode27 (Branch.triple a1 a2 a3)
        | decodeAfterEncode27 (Branch.triple b1 b2 b3) = refl

encodeAfterDecodeRound :
  (code : ThreeBlockResidualCode) → encodeRound (decodeRound code) ≡ code
encodeAfterDecodeRound (threeBlockResidualCode interaction appraisalA appraisalB)
  rewrite interactionTripleFromTriple (decode27 interaction)
        | appraisalTripleFromTriple (decode27 appraisalA)
        | appraisalTripleFromTriple (decode27 appraisalB)
        | encodeAfterDecode27 interaction
        | encodeAfterDecode27 appraisalA
        | encodeAfterDecode27 appraisalB = refl

record AntipodalResidualCodecBoundary : Set where
  constructor antipodalResidualCodecBoundary
  field
    quotientAloneReconstructsFineState : Bool
    quotientPlusDependentResidualRoundTrips : Bool
    centreCarriesSpuriousOrientationBit : Bool
    threeBlockCodecRoundTripsExactly : Bool

canonicalAntipodalResidualCodecBoundary : AntipodalResidualCodecBoundary
canonicalAntipodalResidualCodecBoundary =
  antipodalResidualCodecBoundary false true false true
