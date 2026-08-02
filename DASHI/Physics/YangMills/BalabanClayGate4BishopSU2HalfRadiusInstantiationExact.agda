module DASHI.Physics.YangMills.BalabanClayGate4BishopSU2HalfRadiusInstantiationExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact as HalfRadius
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusFromSignedTailsExact as Signed

------------------------------------------------------------------------
-- Literal Bishop-real instantiation of the SU(2) half-radius scalar lane.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- The repository's elementary bridge defines sine and cosine as limits of
-- absolutely convergent Bishop-real power series. This record prevents the
-- physical SU(2) envelope from being inhabited with unrelated abstract
-- functions: its scalar sine and cosine must be exactly those series values.
-- The remaining analytic work is the signed first-omitted-tail certificate on
-- the selected half ball.
------------------------------------------------------------------------

record BishopSU2HalfRadiusInputs
    (seriesData : Elementary.BishopElementaryPowerSeriesData) : Set₁ where
  field
    core : Signed.SU2HalfRadiusScalarCore Bishop.Bishopℝ

    sineIsBishopSeries :
      HalfRadius.sine (Signed.coreScalar core)
      ≡ Elementary.bishopSin seriesData

    cosineIsBishopSeries :
      HalfRadius.cosine (Signed.coreScalar core)
      ≡ Elementary.bishopCos seriesData

    configuredTails :
      Elementary.BishopConfiguredElementaryTailProofs seriesData

    configuredRadiusIsHalf :
      Bishop.BishopEquivalent
        (Elementary.configuredRadius configuredTails)
        (Signed.coreHalf core)

    signedTailInputs : Signed.SU2HalfRadiusSignedTailInputs core

open BishopSU2HalfRadiusInputs public

bishopSU2HalfRadiusEnvelope :
  ∀ {seriesData : Elementary.BishopElementaryPowerSeriesData} →
  BishopSU2HalfRadiusInputs seriesData →
  HalfRadius.SU2HalfRadiusScalarEnvelope Bishop.Bishopℝ
bishopSU2HalfRadiusEnvelope inputs =
  Signed.halfRadiusEnvelopeFromSignedTails
    (signedTailInputs inputs)

bishopSineUsedByEnvelope :
  ∀ {seriesData : Elementary.BishopElementaryPowerSeriesData}
    (inputs : BishopSU2HalfRadiusInputs seriesData) →
  HalfRadius.sine
    (HalfRadius.scalar (bishopSU2HalfRadiusEnvelope inputs))
  ≡ Elementary.bishopSin seriesData
bishopSineUsedByEnvelope inputs = sineIsBishopSeries inputs

bishopCosineUsedByEnvelope :
  ∀ {seriesData : Elementary.BishopElementaryPowerSeriesData}
    (inputs : BishopSU2HalfRadiusInputs seriesData) →
  HalfRadius.cosine
    (HalfRadius.scalar (bishopSU2HalfRadiusEnvelope inputs))
  ≡ Elementary.bishopCos seriesData
bishopCosineUsedByEnvelope inputs = cosineIsBishopSeries inputs

bishopSU2PowerSeriesFunctionIdentificationLevel : ProofLevel
bishopSU2PowerSeriesFunctionIdentificationLevel = machineChecked

bishopSU2HalfRadiusEnvelopeAssemblyLevel : ProofLevel
bishopSU2HalfRadiusEnvelopeAssemblyLevel = machineChecked

physicalBishopHalfRadiusSignedTailCertificateInputsLevel : ProofLevel
physicalBishopHalfRadiusSignedTailCertificateInputsLevel = conditional
