{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact where

------------------------------------------------------------------------
-- ROUND108: RE-EVALUATE FROZEN ROW C AFTER SAME-DENSITY BC2
--
-- Once BC1/BC2 bind the actual effective density and Heat/Doob expectation,
-- source-local Hessian/covariance summation is downstream.  The remaining Row-C
-- spatial content must be genuinely stochastic/global, not another CMP116
-- locality estimate.  We expose two evidence-bearing objects:
--
--   1. the absolute covariant derivative generator on the SAME Heat/Doob
--      calculus is identified pointwise with one weighted finite influence
--      majorant;
--   2. connected covariance obeys an actual uniform geometric envelope
--      A r^distance, 0 <= r < 1.
--
-- The frozen completion contract was hardened in Round108 so these are witnesses,
-- not proposition names stored as bare `Set` fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayFrozenFourCompletionContractExact as Frozen
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as HeatLSI
import DASHI.Physics.YangMills.CompactLieHeatDoobRicciReserveDebtExact as Reserve
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanHeatDoobFromSameDensityExpectationRound108Exact as SameHeat
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record SameDensityWeightedCovariantInfluence
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier)
    (heat : SameHeat.SameDensityHeatExpectation carrier)
    (Site : Set) : Set₁ where
  field
    physicalDerivativeInfluence : Site → Site → ℚ
    majorant : Weighted.WeightedFiniteInfluenceMajorant Site

    -- SAME dynamic generator: no unrelated comparison matrix may be inserted.
    influenceIsMajorantCarrier : ∀ x y →
      physicalDerivativeInfluence x y
      ≡ Weighted.influence majorant x y

open SameDensityWeightedCovariantInfluence public

record UniformGeometricConnectedClustering (Observable : Set) : Set₁ where
  field
    distance : Observable → Observable → Nat
    connectedCovarianceMagnitude : Observable → Observable → ℚ

    amplitude ratio : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    ratioNonnegative : 0ℚ ≤ ratio
    ratioStrictlyBelowOne : ratio < 1ℚ

    connectedCovarianceBound : ∀ left right →
      connectedCovarianceMagnitude left right
      ≤ amplitude * Power.rationalPower ratio (distance left right)

open UniformGeometricConnectedClustering public

record PostBC2RowCPhysicalCompletion
    (dataSet : HeatLSI.HeatDoobMultiscaleLSIData)
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    sameDensityHeat : SameHeat.SameDensityHeatExpectation carrier

    -- Temporal piece: positive compact-simple Ricci reserve + the SAME-density
    -- cumulative negative Hessian debt already reduced to CMP116 first-gradient
    -- covariance data by the Round102 compiler stack.
    reserveAndHessianDebt : Reserve.RicciReserveHessianDebtData dataSet

    Site : Set
    covariantInfluence :
      SameDensityWeightedCovariantInfluence carrier sameDensityHeat Site

    Observable : Set
    clustering : UniformGeometricConnectedClustering Observable

open PostBC2RowCPhysicalCompletion public

asFrozenRowCCompletion :
  ∀ {dataSet carrier} →
  PostBC2RowCPhysicalCompletion dataSet carrier →
  Frozen.SameDensityCompactLieHeatDoobMassGapCompletion dataSet
asFrozenRowCCompletion data = record
  { Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.SameDensityIdentification =
      SameHeat.SameDensityHeatExpectation _
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.literalSameDensityIdentification =
      sameDensityHeat data
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.reserveAndHessianDebt =
      reserveAndHessianDebt data
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.CovariantInfluencePropagation =
      SameDensityWeightedCovariantInfluence _ (sameDensityHeat data) (Site data)
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.physicalCovariantInfluencePropagation =
      covariantInfluence data
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.ExponentialConnectedClustering =
      UniformGeometricConnectedClustering (Observable data)
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.uniformExponentialConnectedClustering =
      clustering data
  }

round108PostBC2FrozenRowCCompilerLevel : ProofLevel
round108PostBC2FrozenRowCCompilerLevel = machineChecked

-- This is now the honest post-BC2 physical residual.  CMP116 locality itself is
-- not listed again.  The remaining work is: same-density temporal debt
-- instantiation, dynamic weighted influence identification, and the stochastic
-- relaxation/propagation argument producing the displayed geometric covariance
-- envelope.
rowCPostBC2TemporalDebtInstantiationLevel : ProofLevel
rowCPostBC2TemporalDebtInstantiationLevel = conditional

rowCPostBC2DynamicWeightedInfluenceLevel : ProofLevel
rowCPostBC2DynamicWeightedInfluenceLevel = conditional

rowCPostBC2UniformConnectedClusteringLevel : ProofLevel
rowCPostBC2UniformConnectedClusteringLevel = conditional
