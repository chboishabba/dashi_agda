{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact where

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
asFrozenRowCCompletion {carrier = carrier} data = record
  { Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.SameDensityIdentification =
      SameHeat.SameDensityHeatExpectation carrier
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.literalSameDensityIdentification =
      sameDensityHeat data
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.reserveAndHessianDebt =
      reserveAndHessianDebt data
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.CovariantInfluencePropagation =
      SameDensityWeightedCovariantInfluence carrier (sameDensityHeat data) (Site data)
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.physicalCovariantInfluencePropagation =
      covariantInfluence data
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.ExponentialConnectedClustering =
      UniformGeometricConnectedClustering (Observable data)
  ; Frozen.SameDensityCompactLieHeatDoobMassGapCompletion.uniformExponentialConnectedClustering =
      clustering data
  }

round108PostBC2FrozenRowCCompilerLevel : ProofLevel
round108PostBC2FrozenRowCCompilerLevel = machineChecked

rowCPostBC2TemporalDebtInstantiationLevel : ProofLevel
rowCPostBC2TemporalDebtInstantiationLevel = conditional

rowCPostBC2DynamicWeightedInfluenceLevel : ProofLevel
rowCPostBC2DynamicWeightedInfluenceLevel = conditional

rowCPostBC2UniformConnectedClusteringLevel : ProofLevel
rowCPostBC2UniformConnectedClusteringLevel = conditional
