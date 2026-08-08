module DASHI.Biology.StageSymmetrySSP15SpectrumExact where

open import DASHI.Core.Prelude

import DASHI.Biology.StageSymmetrySSP15BridgeExact as Base
import DASHI.Foundations.BalancedTernaryAmplitudeClosureExact as Amp
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Sources and bounded source roles:
--
-- Andrew P. Ogg, Automorphismes de courbes modulaires,
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8,
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono, The Jack Daniels Problem,
-- Journal of Number Theory 161 (2016), 230-239,
-- DOI 10.1016/j.jnt.2015.06.001.
--
-- J. H. Conway and S. P. Norton, Monstrous Moonshine,
-- Bulletin of the London Mathematical Society 11 (1979), 308-339,
-- DOI 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds, Monstrous Moonshine and Monstrous Lie
-- Superalgebras, Inventiones Mathematicae 109 (1992), 405-444,
-- DOI 10.1007/BF01232032.
--
-- These sources ground the Monster/supersingular-prime and moonshine
-- scaffolding.  They do not supply the DASHI frame, Tarot, MDL, residual, or
-- valuation semantics defined below.
------------------------------------------------------------------------

data OrbitType : Set where
  fullTriadOrbit pairOpenOrbit distinguishedLineOrbit : OrbitType

data LaneVisibility : Set where
  laneVisible laneLatent : LaneVisibility

data LaneTransport : Set where
  transportAdmissible transportBlocked transportUnresolved : LaneTransport

data LaneOrientation : Set where
  directOrientation inverseOrientation unresolvedOrientation : LaneOrientation

data EvidenceStatus : Set where
  evidenceAffirmed evidenceOpen evidenceCountered : EvidenceStatus

record RichSymmetryLaneReading : Set where
  constructor richSymmetryLaneReading
  field
    primeLane : Base.OggPrimeLane
    projectedPattern : BT.TriadPattern
    amplitude : Amp.Amplitude7
    amplitudeExact : Amp.triadAmplitude projectedPattern ≡ amplitude
    orbitType : OrbitType
    stabiliser : BT.StabiliserType
    stabiliserExact : BT.patternStabiliser projectedPattern ≡ stabiliser
    status : EvidenceStatus
    visibility : LaneVisibility
    transport : LaneTransport
    valuationDepth : Nat
    residualCode : Nat
    orientation : LaneOrientation

open RichSymmetryLaneReading public

RichSSP15Signature : Set
RichSSP15Signature = Base.OggPrimeLane → RichSymmetryLaneReading

------------------------------------------------------------------------
-- The same local Stage-3 closure can have different multiscale signatures.
-- A locally coherent frame is therefore not identified with its SSP profile.
------------------------------------------------------------------------

localOnlyStageThreeSignature : RichSSP15Signature
localOnlyStageThreeSignature Lane.p71 =
  richSymmetryLaneReading
    Lane.p71 BT.allPositive Amp.ampPos3 refl
    fullTriadOrbit BT.fullStabiliserS3 refl
    evidenceOpen laneLatent transportUnresolved
    1 1 unresolvedOrientation
localOnlyStageThreeSignature p =
  richSymmetryLaneReading
    p BT.allPositive Amp.ampPos3 refl
    fullTriadOrbit BT.fullStabiliserS3 refl
    evidenceAffirmed laneVisible transportAdmissible
    2 0 directOrientation

crossScaleStageThreeSignature : RichSSP15Signature
crossScaleStageThreeSignature p =
  richSymmetryLaneReading
    p BT.allPositive Amp.ampPos3 refl
    fullTriadOrbit BT.fullStabiliserS3 refl
    evidenceAffirmed laneVisible transportAdmissible
    3 0 directOrientation

sameLocalPatternAtP71 :
  projectedPattern (localOnlyStageThreeSignature Lane.p71)
  ≡ projectedPattern (crossScaleStageThreeSignature Lane.p71)
sameLocalPatternAtP71 = refl

signaturesDifferAtP71 :
  status (localOnlyStageThreeSignature Lane.p71)
  ≡ status (crossScaleStageThreeSignature Lane.p71)
  → ⊥
signaturesDifferAtP71 ()

------------------------------------------------------------------------
-- Stage 5 retains the S3/S2 constituent mismatch at every lane.  The rich
-- signature adds amplitude, orbit, visibility, transport, depth, residual,
-- and orientation to the earlier minimal lane receipt.
------------------------------------------------------------------------

stageFiveRichSignature : RichSSP15Signature
stageFiveRichSignature p =
  richSymmetryLaneReading
    p BT.twoPositiveOneOpen Amp.ampPos2 refl
    pairOpenOrbit BT.pairStabiliserS2 refl
    evidenceOpen laneVisible transportUnresolved
    2 2 unresolvedOrientation

stageFiveP3RetainsPairSymmetry :
  stabiliser (stageFiveRichSignature Lane.p3) ≡ BT.pairStabiliserS2
stageFiveP3RetainsPairSymmetry = refl

stageFiveP3RetainsResidualTwo :
  residualCode (stageFiveRichSignature Lane.p3) ≡ 2
stageFiveP3RetainsResidualTwo = refl

------------------------------------------------------------------------
-- Ogg/Monster authority boundary.  Prime lanes and Monster conjugacy-class
-- lanes are different indices.  In particular, the statement that every
-- Monster element of prime order p has the same Gamma_0(p)^+ Hauptmodul is not
-- promoted: a class-sensitive Fricke/Hauptmodul witness is required.
------------------------------------------------------------------------

record OggSpectrumAuthorityBoundary : Set where
  constructor oggSpectrumAuthorityBoundary
  field
    existingFifteenPrimeCarrierReused : Bool
    existingFifteenPrimeCarrierReusedIsTrue :
      existingFifteenPrimeCarrierReused ≡ true
    richSymmetryResolutionSpectrumConstructed : Bool
    richSymmetryResolutionSpectrumConstructedIsTrue :
      richSymmetryResolutionSpectrumConstructed ≡ true
    sspSignatureIdentifiedWithFrame : Bool
    sspSignatureIdentifiedWithFrameIsFalse :
      sspSignatureIdentifiedWithFrame ≡ false
    everyOrderPMonsterClassHasSameGamma0PlusHauptmodul : Bool
    everyOrderPMonsterClassHasSameGamma0PlusHauptmodulIsFalse :
      everyOrderPMonsterClassHasSameGamma0PlusHauptmodul ≡ false
    classSensitiveFrickeWitnessConstructedHere : Bool
    classSensitiveFrickeWitnessConstructedHereIsFalse :
      classSensitiveFrickeWitnessConstructedHere ≡ false
    divinationSemanticsEstablishedByMoonshineSources : Bool
    divinationSemanticsEstablishedByMoonshineSourcesIsFalse :
      divinationSemanticsEstablishedByMoonshineSources ≡ false
    monsterIntertwinerConstructed : Bool
    monsterIntertwinerConstructedIsFalse :
      monsterIntertwinerConstructed ≡ false

canonicalOggSpectrumAuthorityBoundary : OggSpectrumAuthorityBoundary
canonicalOggSpectrumAuthorityBoundary =
  oggSpectrumAuthorityBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
