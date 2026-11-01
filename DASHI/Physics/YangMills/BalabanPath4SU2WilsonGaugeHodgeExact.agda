module DASHI.Physics.YangMills.BalabanPath4SU2WilsonGaugeHodgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (trans; cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact

------------------------------------------------------------------------
-- Exact dependency cut for the configured physical Hodge identity.
--
-- The previous surface owned one opaque equality.  This module separates the
-- three mathematically distinct statements that must be checked against the
-- literal Wilson action and the literal periodic operators:
--
--   (1) Wilson second variation = curl norm squared;
--   (2) gauge-fixing quadratic form = codifferential norm squared;
--   (3) curl norm squared + codifferential norm squared = full difference
--       energy.
--
-- The final equality below is derived solely by transitivity and congruence.
-- No inequality, coefficient suppression, or orientation multiplicity is
-- hidden in the assembly theorem.
------------------------------------------------------------------------

record ConfiguredWilsonGaugeHodgeProducer
    (Gauge Coarse : Set)
    (quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ)
    : Set₁ where
  field
    CurlField : Set
    CodifferentialField : Set

    literalDiscreteCurl : PhysicalSU2Tangent4 → CurlField
    literalCodifferential : PhysicalSU2Tangent4 → CodifferentialField

    curlNormSq : CurlField → ℚ
    codifferentialNormSq : CodifferentialField → ℚ

    -- Includes the four-link plaquette differentiation, SU(2) trace/basis
    -- normalization, positive-pair orientation convention, and coupling
    -- normalization.  Consequently the coefficient on the right is literally
    -- one in the repository's configured reference Hessian convention.
    literalWilsonHessianEqualsCurlEnergy : ∀ tangent →
      wilsonHessianQuadraticForm quadraticData tangent
      ≡ curlNormSq (literalDiscreteCurl tangent)

    -- Identifies the configured divergence with the periodic codifferential,
    -- including its sign and the gauge-fixing coefficient.
    literalGaugeFixingEqualsDivergenceEnergy : ∀ tangent →
      gaugeFixingNormSq quadraticData tangent
      ≡ codifferentialNormSq (literalCodifferential tangent)

    -- The finite periodic Hodge identity.  Its proof owns the periodic
    -- forward/backward summation-by-parts reindexing and the cancellation of
    -- the curl/divergence cross terms.
    discreteCurlDivergenceHodgeIdentity : ∀ tangent →
      curlNormSq (literalDiscreteCurl tangent)
      + codifferentialNormSq (literalCodifferential tangent)
      ≡ physicalReferenceDifferenceEnergy tangent

open ConfiguredWilsonGaugeHodgeProducer public

referenceWilsonGaugeEnergyMatchesDifferenceEnergyExact :
  ∀ {Gauge Coarse}
    {quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ}
    (producer : ConfiguredWilsonGaugeHodgeProducer Gauge Coarse quadraticData)
    tangent →
  wilsonHessianQuadraticForm quadraticData tangent
  + gaugeFixingNormSq quadraticData tangent
  ≡ physicalReferenceDifferenceEnergy tangent
referenceWilsonGaugeEnergyMatchesDifferenceEnergyExact producer tangent =
  trans
    (cong₂ _+_
      (literalWilsonHessianEqualsCurlEnergy producer tangent)
      (literalGaugeFixingEqualsDivergenceEnergy producer tangent))
    (discreteCurlDivergenceHodgeIdentity producer tangent)

------------------------------------------------------------------------
-- Auditable theorem aliases matching the concrete implementation cut.
------------------------------------------------------------------------

wilsonHessianQuadraticFormEqualsCurlNormSq :
  ∀ {Gauge Coarse}
    {quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ}
    (producer : ConfiguredWilsonGaugeHodgeProducer Gauge Coarse quadraticData)
    tangent →
  wilsonHessianQuadraticForm quadraticData tangent
  ≡ curlNormSq producer (literalDiscreteCurl producer tangent)
wilsonHessianQuadraticFormEqualsCurlNormSq =
  literalWilsonHessianEqualsCurlEnergy

gaugeFixingNormSqEqualsDivergenceNormSq :
  ∀ {Gauge Coarse}
    {quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ}
    (producer : ConfiguredWilsonGaugeHodgeProducer Gauge Coarse quadraticData)
    tangent →
  gaugeFixingNormSq quadraticData tangent
  ≡ codifferentialNormSq producer (literalCodifferential producer tangent)
gaugeFixingNormSqEqualsDivergenceNormSq =
  literalGaugeFixingEqualsDivergenceEnergy

literalWilsonLinearisedPlaquetteEqualsDiscreteCurl :
  ∀ {Gauge Coarse}
    {quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ}
    (producer : ConfiguredWilsonGaugeHodgeProducer Gauge Coarse quadraticData)
    tangent →
  wilsonHessianQuadraticForm quadraticData tangent
  ≡ curlNormSq producer (literalDiscreteCurl producer tangent)
literalWilsonLinearisedPlaquetteEqualsDiscreteCurl =
  literalWilsonHessianEqualsCurlEnergy

literalGaugeDivergenceEqualsCodifferential :
  ∀ {Gauge Coarse}
    {quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ}
    (producer : ConfiguredWilsonGaugeHodgeProducer Gauge Coarse quadraticData)
    tangent →
  gaugeFixingNormSq quadraticData tangent
  ≡ codifferentialNormSq producer (literalCodifferential producer tangent)
literalGaugeDivergenceEqualsCodifferential =
  literalGaugeFixingEqualsDivergenceEnergy

configuredWilsonGaugeHodgeAssemblyLevel : ProofLevel
configuredWilsonGaugeHodgeAssemblyLevel = machineChecked

literalWilsonPlaquetteSecondVariationLevel : ProofLevel
literalWilsonPlaquetteSecondVariationLevel = conditional

periodicCurlDivergenceIdentityLevel : ProofLevel
periodicCurlDivergenceIdentityLevel = conditional
