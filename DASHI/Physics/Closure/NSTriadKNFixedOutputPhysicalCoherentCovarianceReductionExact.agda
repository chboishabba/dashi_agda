module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceReductionExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LITERAL PHYSICAL COHERENT-COVARIANCE REDUCTION
--
-- Compose:
--
--   * complete-graph covariance absolute payment;
--   * coherent-work difference = Hermitian work against A_i-A_j;
--   * physical rate-gap normalization
--
--       |r_i-r_j| = nu c^2 |Delta N_ij|.
--
-- The complete physical covariance therefore obeys
--
--   |PairCov|
--     <= nu c^2 *
--        [ 2 sum_{i<j}
--            |Delta N_ij|
--            ( ||M||^2 + ||A_i-A_j||^2 ) ].
--
-- Everything on the RHS is now a literal finite Fourier/state quantity.
-- The only remaining hard B-phase inequality is a cutoff-uniform bound on this
-- explicit lattice-weighted state functional.  There is no abstract rate,
-- scalar-work, covariance, or same-object oracle left.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; Positive; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceAbsolutePaymentExact as Absolute
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateGapExact as RateGap

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

module PhysicalCoherentCovariance
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (mixed : C3.Complex3 F) where

  module Rate = RateGap.PhysicalRateGap physicalSystem viscosityPositive

  scale : ℚ
  scale = Rate.nu * Rate.embeddingScaleSquare

  statePairMass :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    ℚ
  statePairMass left right =
    L2.complex3NormSquared mixed
    + L2.complex3NormSquared
        (C3.complex3Subtract (value left) (value right))

  latticePairMajorant :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    ℚ
  latticePairMajorant left right =
    two *
      (∣ Rate.latticeFrequencyGap left right ∣
        * statePairMass left right)

  latticeMajorantAgainstHead :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence →
    ℚ
  latticeMajorantAgainstHead head [] = 0ℚ
  latticeMajorantAgainstHead head (x ∷ xs) =
    latticePairMajorant head x
    + latticeMajorantAgainstHead head xs

  latticePairEnergy :
    List Physical.PhysicalTriadIncidence → ℚ
  latticePairEnergy [] = 0ℚ
  latticePairEnergy (x ∷ xs) =
    latticeMajorantAgainstHead x xs
    + latticePairEnergy xs

  pairMajorantNormalized :
    (left right : Physical.PhysicalTriadIncidence) →
    Absolute.pairAbsoluteMajorant
      Rate.physicalCellRate value mixed left right
    ≡ scale * latticePairMajorant left right
  pairMajorantNormalized left right =
    let
      rateGapMag =
        Rate.cellRateGapMagnitudeNormalized left right
      gap = ∣ Rate.latticeFrequencyGap left right ∣
      state = statePairMass left right
    in
    trans
      (cong
        (λ rateAbs → two * (rateAbs * state))
        rateGapMag)
      (solve (scale ∷ gap ∷ state ∷ []))
  headMajorantNormalized :
    (head : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    Absolute.majorantAgainstHead
      Rate.physicalCellRate value mixed head items
    ≡ scale * latticeMajorantAgainstHead head items
  headMajorantNormalized head [] =
    sym (ℚP.*-zeroʳ scale)
  headMajorantNormalized head (x ∷ xs) =
    trans
      (cong₂ _+_
        (pairMajorantNormalized head x)
        (headMajorantNormalized head xs))
      (solve
        ( scale
        ∷ latticePairMajorant head x
        ∷ latticeMajorantAgainstHead head xs
        ∷ []))

  fullMajorantNormalized :
    (items : List Physical.PhysicalTriadIncidence) →
    Absolute.pairAbsoluteMajorantSum
      Rate.physicalCellRate value mixed items
    ≡ scale * latticePairEnergy items
  fullMajorantNormalized [] =
    sym (ℚP.*-zeroʳ scale)
  fullMajorantNormalized (x ∷ xs) =
    trans
      (Relation.Binary.PropositionalEquality.cong₂ _+_
        (headMajorantNormalized x xs)
        (fullMajorantNormalized xs))
      (solve
        ( scale
        ∷ latticeMajorantAgainstHead x xs
        ∷ latticePairEnergy xs
        ∷ []))

  physicalCovarianceAbsoluteBound :
    (items : List Physical.PhysicalTriadIncidence) →
    ∣ Pair.pairDifferenceWorkSum
        Rate.physicalCellRate
        (λ i → Work.coherentWork mixed (value i))
        items ∣
    ≤ scale * latticePairEnergy items
  physicalCovarianceAbsoluteBound items =
    subst
      (λ upper →
        ∣ Pair.pairDifferenceWorkSum
            Rate.physicalCellRate
            (λ i → Work.coherentWork mixed (value i))
            items ∣
        ≤ upper)
      (fullMajorantNormalized items)
      (Absolute.pairDifferenceWorkAbsoluteBound
        Rate.physicalCellRate value mixed items)

physicalCoherentCovarianceReducedToLatticePairEnergy : Bool
physicalCoherentCovarianceReducedToLatticePairEnergy = true

abstractRateOracleRemaining : Bool
abstractRateOracleRemaining = false

abstractScalarWorkDifferenceOracleRemaining : Bool
abstractScalarWorkDifferenceOracleRemaining = false

cutoffUniformLatticePairEnergyPaymentClosedHere : Bool
cutoffUniformLatticePairEnergyPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

physicalCoherentCovarianceReducedToLatticePairEnergyIsTrue :
  physicalCoherentCovarianceReducedToLatticePairEnergy ≡ true
physicalCoherentCovarianceReducedToLatticePairEnergyIsTrue = refl

abstractRateOracleRemainingIsFalse :
  abstractRateOracleRemaining ≡ false
abstractRateOracleRemainingIsFalse = refl

abstractScalarWorkDifferenceOracleRemainingIsFalse :
  abstractScalarWorkDifferenceOracleRemaining ≡ false
abstractScalarWorkDifferenceOracleRemainingIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
