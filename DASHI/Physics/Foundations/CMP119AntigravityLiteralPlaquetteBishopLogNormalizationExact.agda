{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBishopLogNormalizationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
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
