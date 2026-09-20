module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBudgetExact where

------------------------------------------------------------------------
-- S2b2d1b2 / PHYSICAL RATE-WEIGHTED COHERENT-COVARIANCE BUDGET
--
-- Combine:
--
--   * exact fixed-output viscous-rate factorization
--
--       2 (r_alpha-r_beta)
--         = nu (|d_alpha|^2-|d_beta|^2),
--
--   * the same-pair coherent Young estimate
--
--       |Delta w|
--         <= 2 (||M||^2 + ||A_alpha-A_beta||^2).
--
-- The factor two is not discarded.  It is absorbed exactly into the physical
-- rate difference, giving the quotient-correct pair budget
--
--   |nu (|d_alpha|^2-|d_beta|^2)|
--     * (||M||^2 + ||A_alpha-A_beta||^2).
--
-- This is a physical theorem on each pair sharing one output.  It introduces
-- no division, maximum, incidence count, shell count, or raw-incidence
-- separation.  In particular it vanishes when the physical radial rate
-- difference vanishes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Bridge
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceQuantitativePairBoundExact as Quant
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate

F : C3.RealField _
F = Rational.rationalRealField

physicalRadialRateDefect :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
physicalRadialRateDefect physicalSystem alpha beta =
  let
    I = Field30.physicalInverseSquare physicalSystem
    nu = Field30.viscosity physicalSystem
    dAlpha = Rate.differenceMode (Physical.p alpha) (Physical.q alpha)
    dBeta = Rate.differenceMode (Physical.p beta) (Physical.q beta)
  in
  nu * (C3.normSquared I dAlpha - C3.normSquared I dBeta)

physicalCoherentPairBudget :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
physicalCoherentPairBudget physicalSystem mixed value alpha beta =
  ∣ physicalRadialRateDefect physicalSystem alpha beta ∣
  * ( L2.complex3NormSquared mixed
    + L2.complex3NormSquared
        (C3.complex3Subtract (value alpha) (value beta)) )

twoNonnegative : 0ℚ ≤ Rate.two
twoNonnegative =
  Rational.addNonnegative (ℚP.0≤∣p∣ 1ℚ) (ℚP.0≤∣p∣ 1ℚ)

absoluteTwice :
  (x : ℚ) →
  ∣ Rate.two * x ∣ ≡ Rate.two * ∣ x ∣
absoluteTwice x =
  trans
    (ℚP.∣p*q∣≡∣p∣*∣q∣ Rate.two x)
    (cong (_* ∣ x ∣) (ℚP.0≤p⇒∣p∣≡p twoNonnegative))

physicalRateYoungPairIsCenteredBudget :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  Quant.rateWeightedYoungPair
    mixed
    (Rate.physicalCellRate physicalSystem)
    value
    alpha beta
  ≡
  physicalCoherentPairBudget physicalSystem mixed value alpha beta
physicalRateYoungPairIsCenteredBudget
    physicalSystem mixed value alpha beta sameOutput =
  let
    rateDiff =
      Rate.physicalCellRate physicalSystem alpha
      - Rate.physicalCellRate physicalSystem beta

    radial =
      physicalRadialRateDefect physicalSystem alpha beta

    X =
      L2.complex3NormSquared mixed
      + L2.complex3NormSquared
          (C3.complex3Subtract (value alpha) (value beta))

    rateExact :
      Rate.two * rateDiff ≡ radial
    rateExact =
      Rate.fixedOutputPhysicalRateDifference
        physicalSystem alpha beta sameOutput

    absExact :
      Rate.two * ∣ rateDiff ∣ ≡ ∣ radial ∣
    absExact =
      trans
        (sym (absoluteTwice rateDiff))
        (cong ∣_∣ rateExact)

    rearrange :
      ∣ rateDiff ∣ * Bridge.two * X
      ≡ Rate.two * ∣ rateDiff ∣ * X
    rearrange = solve (∣ rateDiff ∣ ∷ Rate.two ∷ X ∷ [])
  in
  trans rearrange (cong (_* X) absExact)

physicalSignedPairBelowCenteredBudget :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  ( Rate.physicalCellRate physicalSystem alpha
      - Rate.physicalCellRate physicalSystem beta )
    *
    ( Work.coherentWork mixed (value alpha)
      - Work.coherentWork mixed (value beta) )
  ≤ physicalCoherentPairBudget physicalSystem mixed value alpha beta
physicalSignedPairBelowCenteredBudget
    physicalSystem mixed value alpha beta sameOutput =
  subst
    (λ upper →
      ( Rate.physicalCellRate physicalSystem alpha
          - Rate.physicalCellRate physicalSystem beta )
        *
        ( Work.coherentWork mixed (value alpha)
          - Work.coherentWork mixed (value beta) )
      ≤ upper)
    (physicalRateYoungPairIsCenteredBudget
      physicalSystem mixed value alpha beta sameOutput)
    (ℚP.≤-trans
      (Quant.signedPairTermBelowAbsolute
        (Rate.physicalCellRate physicalSystem)
        (λ item → Work.coherentWork mixed (value item))
        alpha beta)
      (Quant.absoluteCoherentPairBelowYoung
        mixed
        (Rate.physicalCellRate physicalSystem)
        value
        alpha beta))

------------------------------------------------------------------------
-- Exact finite-family lift on one literal output.
------------------------------------------------------------------------

physicalCenteredAgainstHead :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
physicalCenteredAgainstHead physicalSystem mixed value head [] = 0ℚ
physicalCenteredAgainstHead physicalSystem mixed value head (x ∷ xs) =
  physicalCoherentPairBudget physicalSystem mixed value head x
  + physicalCenteredAgainstHead physicalSystem mixed value head xs

physicalCenteredPairSum :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
physicalCenteredPairSum physicalSystem mixed value [] = 0ℚ
physicalCenteredPairSum physicalSystem mixed value (x ∷ xs) =
  physicalCenteredAgainstHead physicalSystem mixed value x xs
  + physicalCenteredPairSum physicalSystem mixed value xs

physicalAgainstHeadBelowCentered :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (output : Z3.FourierMode) →
  (head : Physical.PhysicalTriadIncidence) →
  Physical.k head ≡ output →
  (rest : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau R396.OccursIn rest → Physical.k tau ≡ output) →
  Pair.pairAgainstHead
    (Rate.physicalCellRate physicalSystem)
    (λ item → Work.coherentWork mixed (value item))
    head rest
  ≤ physicalCenteredAgainstHead physicalSystem mixed value head rest
physicalAgainstHeadBelowCentered
    physicalSystem mixed value output head headOutput [] allOutput =
  ℚP.≤-refl
physicalAgainstHeadBelowCentered
    physicalSystem mixed value output head headOutput (x ∷ xs) allOutput =
  ℚP.+-mono-≤
    (physicalSignedPairBelowCenteredBudget
      physicalSystem mixed value head x
      (trans headOutput (sym (allOutput x R396.here))))
    (physicalAgainstHeadBelowCentered
      physicalSystem mixed value output head headOutput xs
      (λ tau member → allOutput tau (R396.there member)))

physicalFixedOutputFamilySignedBound :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (output : Z3.FourierMode) →
  (items : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau R396.OccursIn items → Physical.k tau ≡ output) →
  Pair.pairDifferenceWorkSum
    (Rate.physicalCellRate physicalSystem)
    (λ item → Work.coherentWork mixed (value item))
    items
  ≤ physicalCenteredPairSum physicalSystem mixed value items
physicalFixedOutputFamilySignedBound
    physicalSystem mixed value output [] allOutput =
  ℚP.≤-refl
physicalFixedOutputFamilySignedBound
    physicalSystem mixed value output (head ∷ rest) allOutput =
  ℚP.+-mono-≤
    (physicalAgainstHeadBelowCentered
      physicalSystem mixed value output head
      (allOutput head R396.here)
      rest
      (λ tau member → allOutput tau (R396.there member)))
    (physicalFixedOutputFamilySignedBound
      physicalSystem mixed value output rest
      (λ tau member → allOutput tau (R396.there member)))

occursToCube :
  ∀ {A : Set} {x : A} {xs : List A} →
  x R396.OccursIn xs → x Cube.∈ xs
occursToCube R396.here = Cube.here refl
occursToCube (R396.there member) = Cube.there (occursToCube member)

literalFibreAllHaveOutput :
  (cutoff : Nat) (output : Z3.FourierMode) →
  (tau : Physical.PhysicalTriadIncidence) →
  tau R396.OccursIn Output.physicalOutputFiber cutoff output →
  Physical.k tau ≡ output
literalFibreAllHaveOutput cutoff output tau member =
  Output.physicalOutputFiberSound (occursToCube member)

literalPhysicalOutputFibreSignedBound :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let items = Output.physicalOutputFiber cutoff output
  in
  Pair.pairDifferenceWorkSum
    (Rate.physicalCellRate physicalSystem)
    (λ item → Work.coherentWork mixed (value item))
    items
  ≤ physicalCenteredPairSum physicalSystem mixed value items
literalPhysicalOutputFibreSignedBound
    physicalSystem mixed value cutoff output =
  physicalFixedOutputFamilySignedBound
    physicalSystem mixed value output
    (Output.physicalOutputFiber cutoff output)
    (literalFibreAllHaveOutput cutoff output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

physicalRateDifferenceAbsorbedExactlyIntoRadialDefect : Bool
physicalRateDifferenceAbsorbedExactlyIntoRadialDefect = true

physicalSignedCoherentPairBudgetClosed : Bool
physicalSignedCoherentPairBudgetClosed = true

physicalSignedCoherentPairBudgetIntroducesCardinalityTax : Bool
physicalSignedCoherentPairBudgetIntroducesCardinalityTax = false

physicalFixedOutputFamilyBudgetSummedHere : Bool
physicalFixedOutputFamilyBudgetSummedHere = true

cutoffUniformIntegratedBudgetClosedHere : Bool
cutoffUniformIntegratedBudgetClosedHere = false

clayPromotion : Bool
clayPromotion = false

physicalSignedCoherentPairBudgetClosedIsTrue :
  physicalSignedCoherentPairBudgetClosed ≡ true
physicalSignedCoherentPairBudgetClosedIsTrue = refl

physicalSignedCoherentPairBudgetIntroducesCardinalityTaxIsFalse :
  physicalSignedCoherentPairBudgetIntroducesCardinalityTax ≡ false
physicalSignedCoherentPairBudgetIntroducesCardinalityTaxIsFalse = refl
