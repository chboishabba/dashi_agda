module DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Dashen and David J. Gross,
-- "Relationship between Lattice and Continuum Definitions of the Gauge-Theory
-- Coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Identify beta_Z and beta_int with the SAME localized plaquette coefficient
-- appearing in the repository's literal one-step running-coupling recursion.
-- The Gaussian term is exactly the vacuum-polarization plaquette projector;
-- the interaction term is exactly the total localized quartic remainder.
-- A signed quartic enclosure plus one common small-coupling compatibility
-- inequality yields the finite beta estimate used by the history theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact as Estimate

literalBetaZ :
  ∀ {Scale} → Plaquette.PhysicalRunningCouplingData Scale → Scale → ℚ
literalBetaZ dataSet scale =
  Plaquette.vacuumPolarizationPlaquetteCoefficient
    (Plaquette.oneLoop dataSet) scale

literalBetaInt :
  ∀ {Scale} → Plaquette.PhysicalRunningCouplingData Scale → Scale → ℚ
literalBetaInt dataSet scale =
  Plaquette.totalRemainder (Plaquette.remainder dataSet) scale

literalBetaStep :
  ∀ {Scale} → Plaquette.PhysicalRunningCouplingData Scale → Scale → ℚ
literalBetaStep dataSet scale = literalBetaZ dataSet scale + literalBetaInt dataSet scale

literalRunningCouplingStepIsBetaSplit :
  ∀ {Scale} (dataSet : Plaquette.PhysicalRunningCouplingData Scale) scale →
  Plaquette.nextInverseCouplingSq dataSet scale
  ≡ Plaquette.inverseCouplingSq dataSet scale + literalBetaStep dataSet scale
literalRunningCouplingStepIsBetaSplit dataSet scale =
  trans
    (Plaquette.physicalRunningCouplingRecursion dataSet scale)
    (ℚRing.solve-∀
      (Plaquette.inverseCouplingSq dataSet scale)
      (literalBetaZ dataSet scale)
      (literalBetaInt dataSet scale))

record LiteralFiniteBetaCertificate
    {Scale : Set}
    (dataSet : Plaquette.PhysicalRunningCouplingData Scale)
    (scale : Scale) : Set where
  field
    coupling : ℚ
    zLower : ℚ

    couplingNonnegative : 0ℚ ≤ coupling
    zLowerNonnegative : 0ℚ ≤ zLower

    gaussianLower : zLower ≤ literalBetaZ dataSet scale

    interactionConstant : ℚ
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant

    signedQuarticRemainder :
      ∣ literalBetaInt dataSet scale ∣
      ≤ interactionConstant * Estimate.fourthPower coupling

    quarticFitsHalfGaussianGap :
      interactionConstant * Estimate.fourthPower coupling
      ≤ Estimate.half * zLower

open LiteralFiniteBetaCertificate public

literalCertificateAsFiniteEstimate :
  ∀ {Scale} {dataSet : Plaquette.PhysicalRunningCouplingData Scale} {scale}
    (certificate : LiteralFiniteBetaCertificate dataSet scale) →
  Estimate.FiniteLatticeBetaEstimate
literalCertificateAsFiniteEstimate {dataSet = dataSet} {scale = scale} certificate = record
  { Estimate.FiniteLatticeBetaEstimate.beta = literalBetaStep dataSet scale
  ; Estimate.FiniteLatticeBetaEstimate.betaZ = literalBetaZ dataSet scale
  ; Estimate.FiniteLatticeBetaEstimate.betaInt = literalBetaInt dataSet scale
  ; Estimate.FiniteLatticeBetaEstimate.coupling = coupling certificate
  ; Estimate.FiniteLatticeBetaEstimate.interactionConstant =
      interactionConstant certificate
  ; Estimate.FiniteLatticeBetaEstimate.zLower = zLower certificate
  ; Estimate.FiniteLatticeBetaEstimate.betaSplitExact = ℚRing.solve []
  ; Estimate.FiniteLatticeBetaEstimate.couplingNonnegative =
      couplingNonnegative certificate
  ; Estimate.FiniteLatticeBetaEstimate.interactionConstantNonnegative =
      interactionConstantNonnegative certificate
  ; Estimate.FiniteLatticeBetaEstimate.zLowerNonnegative =
      zLowerNonnegative certificate
  ; Estimate.FiniteLatticeBetaEstimate.gaussianLower = gaussianLower certificate
  ; Estimate.FiniteLatticeBetaEstimate.interactionQuartic =
      signedQuarticRemainder certificate
  ; Estimate.FiniteLatticeBetaEstimate.quarticFitsHalfGaussianGap =
      quarticFitsHalfGaussianGap certificate
  }

literalFiniteBetaLowerHalfGap :
  ∀ {Scale} {dataSet : Plaquette.PhysicalRunningCouplingData Scale} {scale}
    (certificate : LiteralFiniteBetaCertificate dataSet scale) →
  Estimate.half * zLower certificate ≤ literalBetaStep dataSet scale
literalFiniteBetaLowerHalfGap certificate =
  Estimate.finiteLatticeBetaLowerHalfGap
    (literalCertificateAsFiniteEstimate certificate)

literalFiniteBetaNonnegative :
  ∀ {Scale} {dataSet : Plaquette.PhysicalRunningCouplingData Scale} {scale}
    (certificate : LiteralFiniteBetaCertificate dataSet scale) →
  0ℚ ≤ literalBetaStep dataSet scale
literalFiniteBetaNonnegative certificate =
  Estimate.finiteLatticeBetaNonnegative
    (literalCertificateAsFiniteEstimate certificate)

ym4LiteralPlaquetteBetaSplitLevel : ProofLevel
ym4LiteralPlaquetteBetaSplitLevel = machineChecked

ym4LiteralPlaquetteFiniteBetaEstimateLevel : ProofLevel
ym4LiteralPlaquetteFiniteBetaEstimateLevel = machineChecked
