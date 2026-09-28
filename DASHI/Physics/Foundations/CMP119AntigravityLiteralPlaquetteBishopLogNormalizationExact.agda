{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBishopLogNormalizationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- LITERAL-PLAQUETTE / BISHOP LOG NORMALIZATION
--
-- There are two coefficient carriers in the repository:
--
--   * the older rational localized-plaquette producer writes
--
--       beta_Z = b0 * logBlocking_rational ;
--
--   * the richer T4 literal vacuum-polarization machinery keeps the physical
--     continuum normalization explicit:
--
--       beta_Z = b0 * pi^{-2} * log L .
--
-- Therefore the remaining same-object seam is NOT licensed as
--
--       log L_Bishop = pi^2 * embed(logBlocking_rational)
--
-- by convention alone.  The honest coordinate weld is the normalized one:
--
--       embed(logBlocking_rational)
--         ~= pi^{-2} * log L_Bishop .
--
-- Once that coordinate equation is supplied, the Gaussian coefficient weld
-- follows from the already-owned multiplicativity of the Bishop rational
-- embedding.  No new beta-function arithmetic is assumed here.
------------------------------------------------------------------------

record LiteralPlaquetteBishopLogNormalization
    {Scale : Set}
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale) : Set₁ where
  field
    bishopLogBlocking : Scale → Bishop.ℝ

    casimirIsSU2 :
      Plaquette.casimirAdjoint oneLoop ≡ SU2.su2Casimir

    normalizedLogCoordinate :
      ∀ scale →
      Bishop._≃_
        (UV.embed (Plaquette.logBlocking oneLoop scale))
        (Bishop._*_
          Pi.inversePiSquared
          (bishopLogBlocking scale))

open LiteralPlaquetteBishopLogNormalization public

embeddedGaussianAtNativeCasimir :
  ∀ {Scale}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale}
    (normalization : LiteralPlaquetteBishopLogNormalization oneLoop)
    scale →
  Bishop._≃_
    (UV.embed
      (Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop scale))
    (Bishop._*_
      (Bishop._*_
        (Embed.embed
          (Beta.pureYMInverseCouplingCoefficient
            (Plaquette.casimirAdjoint oneLoop)))
        Pi.inversePiSquared)
      (bishopLogBlocking normalization scale))
embeddedGaussianAtNativeCasimir {oneLoop = oneLoop} normalization scale =
  BishopP.≃-trans
    (Embed.embedMul
      (Beta.pureYMInverseCouplingCoefficient
        (Plaquette.casimirAdjoint oneLoop))
      (Plaquette.logBlocking oneLoop scale))
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (normalizedLogCoordinate normalization scale))
      (BishopP.≃-symm
        (BishopP.*-assoc
          (Embed.embed
            (Beta.pureYMInverseCouplingCoefficient
              (Plaquette.casimirAdjoint oneLoop)))
          Pi.inversePiSquared
          (bishopLogBlocking normalization scale))))

embeddedGaussianIsCanonicalBishopSU2 :
  ∀ {Scale}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Scale}
    (normalization : LiteralPlaquetteBishopLogNormalization oneLoop)
    scale →
  Bishop._≃_
    (UV.embed
      (Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop scale))
    (Bishop._*_
      (Bishop._*_
        (Embed.embed
          (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
        Pi.inversePiSquared)
      (bishopLogBlocking normalization scale))
embeddedGaussianIsCanonicalBishopSU2
    {oneLoop = oneLoop} normalization scale =
  subst
    (λ selectedCasimir →
      Bishop._≃_
        (UV.embed
          (Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop scale))
        (Bishop._*_
          (Bishop._*_
            (Embed.embed
              (Beta.pureYMInverseCouplingCoefficient selectedCasimir))
            Pi.inversePiSquared)
          (bishopLogBlocking normalization scale)))
    (casimirIsSU2 normalization)
    (embeddedGaussianAtNativeCasimir normalization scale)

------------------------------------------------------------------------
-- P3 GAUSSIAN COORDINATE CONSEQUENCE
--
-- The preferred split P3/literal weld already identifies the P3 Gaussian
-- increment with the embedded literal beta_Z.  Combining that machine-checked
-- weld with the normalized-log theorem above removes a second same-object
-- obligation: once normalizedLogCoordinate is paid, the P3 Gaussian term is
-- automatically in the canonical Bishop SU(2) convention.
------------------------------------------------------------------------

p3GaussianUsesCanonicalBishopSU2 :
  ∀ {dataSet : Plaquette.PhysicalRunningCouplingData Nat}
    {recursion : P3.RunningCouplingRecursion Nat Bishop.ℝ}
    (splitView :
      P3Literal.P3RepresentsLiteralPlaquetteSplitUVView dataSet recursion)
    (normalization :
      LiteralPlaquetteBishopLogNormalization (Plaquette.oneLoop dataSet))
    depth →
  Bishop._≃_
    (P3.betaLogBlocking recursion (suc depth))
    (Bishop._*_
      (Bishop._*_
        (Embed.embed
          (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
        Pi.inversePiSquared)
      (bishopLogBlocking normalization (suc depth)))
p3GaussianUsesCanonicalBishopSU2
    {dataSet = dataSet} splitView normalization depth =
  BishopP.≃-trans
    (P3Literal.betaLogBlockingSameLiteralGaussian splitView depth)
    (embeddedGaussianIsCanonicalBishopSU2 normalization (suc depth))

------------------------------------------------------------------------
-- STRUCTURAL NO-GO: THE OLD RATIONAL LOG COORDINATE IS FREE
--
-- OneLoopVacuumPolarizationData does not attach logBlocking to a geometric
-- blocking factor, a continuum logarithm, or pi.  For any rational-valued
-- coordinate we can inhabit the record definitionally.  Therefore no theorem
-- of the form
--
--   embed(logBlocking) ~= pi^{-2} * physicalLog
--
-- can be recovered from that record alone.  It must come from the richer T4
-- literal integral / source normalization.
------------------------------------------------------------------------

freeRationalOneLoopVacuumPolarizationData :
  ∀ {Scale}
    (casimir : ℚ)
    (chosenLog : Scale → ℚ) →
  Plaquette.OneLoopVacuumPolarizationData Scale
freeRationalOneLoopVacuumPolarizationData casimir chosenLog = record
  { Plaquette.OneLoopVacuumPolarizationData.casimirAdjoint =
      casimir
  ; Plaquette.OneLoopVacuumPolarizationData.logBlocking =
      chosenLog
  ; Plaquette.OneLoopVacuumPolarizationData.gaugeModeContribution =
      λ _ → 0ℚ
  ; Plaquette.OneLoopVacuumPolarizationData.ghostContribution =
      λ _ → 0ℚ
  ; Plaquette.OneLoopVacuumPolarizationData.transverseContribution =
      λ _ → 0ℚ
  ; Plaquette.OneLoopVacuumPolarizationData.connectedCumulantCoefficient =
      λ scale →
        Beta.pureYMInverseCouplingCoefficient casimir * chosenLog scale
  ; Plaquette.OneLoopVacuumPolarizationData.gaugeModeContributionExact =
      λ _ → Agda.Builtin.Equality.refl
  ; Plaquette.OneLoopVacuumPolarizationData.ghostContributionExact =
      λ _ → Agda.Builtin.Equality.refl
  ; Plaquette.OneLoopVacuumPolarizationData.gaugeGhostCancellationExact =
      λ _ → ℚRing.solve []
  ; Plaquette.OneLoopVacuumPolarizationData.adjointColorTraceEqualsCasimir =
      Agda.Builtin.Equality.refl
  ; Plaquette.OneLoopVacuumPolarizationData.latticeMomentumSecondDerivativeExact =
      λ _ → Agda.Builtin.Equality.refl
  ; Plaquette.OneLoopVacuumPolarizationData.dashenGrossLatticeContinuumCalibrationExact =
      λ _ → Agda.Builtin.Equality.refl
  }

oldRationalOneLoopRecordFixesPhysicalPiNormalization :
  Agda.Builtin.Bool.Bool
oldRationalOneLoopRecordFixesPhysicalPiNormalization =
  Agda.Builtin.Bool.false

------------------------------------------------------------------------
-- FRONTIER RECUT
--
-- The pi^{-2} factor is already explicit in the physical T4 convention.
-- The surviving source theorem is only the same-object identification of the
-- old rational log coordinate with that normalized physical coordinate.
------------------------------------------------------------------------

freePiSquaredRescalingOfPhysicalLogRequired :
  Agda.Builtin.Bool.Bool
freePiSquaredRescalingOfPhysicalLogRequired =
  Agda.Builtin.Bool.false

normalizedLiteralLogCoordinateStillRequired :
  Agda.Builtin.Bool.Bool
normalizedLiteralLogCoordinateStillRequired =
  Agda.Builtin.Bool.true

literalPlaquetteBishopLogNormalizationCompilerLevel : ProofLevel
literalPlaquetteBishopLogNormalizationCompilerLevel = machineChecked

literalPlaquetteBishopLogSameObjectLevel : ProofLevel
literalPlaquetteBishopLogSameObjectLevel = conditional
