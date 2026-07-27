module DASHI.Physics.Closure.NSTriadKNQuarticBKMExpenditure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the breakdown of smooth solutions for the 3-D Euler
-- equations".
-- Venue/year: Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
-- Uses: vorticity-infinity continuation criterion.
-- Relationship: adapts the continuation endpoint to cutoff-uniform periodic
-- Galerkin approximations.
--
-- Authors: Hideo Kozono; Takayoshi Ogawa; Yasushi Taniuchi.
-- Title: "The critical Sobolev inequalities in Besov spaces and regularity
-- criterion to some semi-linear evolution equations".
-- Venue/year: Mathematische Zeitschrift 242 (2002), 251--278.
-- DOI: 10.1007/s002090100332.
-- Uses: the endpoint Besov regularity route.
-- Relationship: motivates the B^0_{infinity,1} fallback only; DASHI's
-- cutoff-uniform differential expenditure remains a new proof obligation.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Venue/year: Journal of Mathematical Fluid Mechanics 21, article 1 (2019).
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv: 1803.05569v4.
-- Uses: frequency- and time-localized alternative continuation route.
-- Relationship: records a possible alternative chart-local endpoint.
-- Note: arXiv:1803.05569 is by Luo, not Chemin--Zhang.
--
-- Authors: Herbert Koch; Daniel Tataru.
-- Title: "Well-posedness for the Navier-Stokes Equations".
-- Venue/year: Advances in Mathematics 157 (2001), 22--35.
-- DOI: 10.1006/aima.2000.1937.
-- Uses: small-data BMO^{-1} alternative.
-- Relationship: documented as a structurally different fallback, not used
-- by the present H^s/Besov expenditure composition.
--
-- Authors: Pascal Auscher; Dorothee Frey.
-- Title: "On the well-posedness of parabolic equations of Navier-Stokes
-- type with BMO^{-1} data".
-- Venue/year: Journal of the Institute of Mathematics of Jussieu 16
-- (2017), 947--985.
-- DOI: 10.1017/S1474748015000158.
-- arXiv: 1412.8407v3.
-- Uses: operator/tent-space formulation without relying on self-adjointness
-- or pointwise kernel bounds for the general model.
-- Relationship: records a last-resort BMO^{-1} architecture; it is not used
-- to discharge the present quartic programme.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_<_)

record QuarticControlToUniformBKMExpenditure
    {c t s r : Level} :
    Set (lsuc (c ⊔ t ⊔ s ⊔ r)) where
  field
    Cutoff : Set c
    Time : Set t
    State : Set s
    Scalar : Set r

    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    squareRoot : Scalar → Scalar
    _≤_ : Scalar → Scalar → Set r
    Finite : Scalar → Set r
    ≤-transitive : ∀ {x y z} → _≤_ x y → _≤_ y z → _≤_ x z

    initialTime finalTime : Time
    solution : Cutoff → Time → State

    weightedShellEnvelope vorticityInfinity
      sobolevEnergy quadraticCorrection quarticValue :
      Cutoff → Time → Scalar

    bernsteinConstant quadraticControlConstant
      quarticControlConstant geometricConstant
      initialDataBound : Scalar

    shellVorticityEnvelope : ∀ N time →
      _≤_
        (vorticityInfinity N time)
        (multiply bernsteinConstant
          (weightedShellEnvelope N time))

    quadraticCorrectionControlsHsUniformly : ∀ N time →
      _≤_
        (sobolevEnergy N time)
        (multiply quadraticControlConstant
          (quadraticCorrection N time))

    quarticCoercivityControlsHsUniformly : ∀ N time →
      _≤_
        (sobolevEnergy N time)
        (multiply quarticControlConstant
          (quarticValue N time))

    twiceSobolevIndex : Nat
    sobolevStrictlyAboveFiveHalves : 5 < twiceSobolevIndex

    HsStrictlyAboveFiveHalvesControlsWeightedShell : ∀ N time →
      _≤_
          (weightedShellEnvelope N time)
        (multiply geometricConstant
          (squareRoot (sobolevEnergy N time)))

    weightedShellGeometricConstantFinite : Finite geometricConstant

    lyapunovDescentGivesUniformHsBound : ∀ N time →
      _≤_ (sobolevEnergy N time) initialDataBound

    compactGammaImpliesWeightedShellSummability : ∀ N time →
      _≤_
        (weightedShellEnvelope N time)
        (multiply geometricConstant initialDataBound)

    uniformWeightedShellPointwiseBound : ∀ N time →
      _≤_
        (weightedShellEnvelope N time)
        (multiply geometricConstant initialDataBound)

    integral : (Time → Scalar) → Time → Time → Scalar
    timeLength : Time → Time → Scalar
    supremumOn : (Time → Scalar) → Time → Time → Scalar

    integralBoundedByLengthTimesSupremum : ∀ f start finish →
      _≤_
        (integral f start finish)
        (multiply
          (timeLength start finish)
          (supremumOn f start finish))

    compactTimeEnvelopeBound : Scalar
    finiteCompactGammaEnvelopeExpenditure : ∀ N →
      _≤_
        (integral
          (weightedShellEnvelope N)
          initialTime finalTime)
        compactTimeEnvelopeBound

    finiteVorticityTimeIntegral : ∀ N →
      _≤_
        (integral
          (vorticityInfinity N)
          initialTime finalTime)
        (multiply bernsteinConstant compactTimeEnvelopeBound)

    BKMContinuation : Cutoff → Set
    uniformGalerkinBKMContinuation : ∀ N →
      BKMContinuation N

    LimitContinuation : Set
    uniformBKMDischargesLimitContinuation :
      LimitContinuation

open QuarticControlToUniformBKMExpenditure public

record CriticalBesovEndpointExpenditure
    {c t r : Level}
    (Cutoff : Set c)
    (Time : Set t)
    (Scalar : Set r) :
    Set (lsuc (c ⊔ t ⊔ r)) where
  field
    criticalBesovEnvelope : Cutoff → Time → Scalar
    criticalBesovFlux : Cutoff → Time → Scalar
    criticalBesovDerivative : Cutoff → Time → Scalar
    _≤_ : Scalar → Scalar → Set r
    expenditureBound : Scalar
    integral : (Time → Scalar) → Time → Time → Scalar
    initialTime finalTime : Time
    criticalBesovEnvelopeDifferentialExpenditure : ∀ N time →
      _≤_
        (criticalBesovDerivative N time)
        (criticalBesovFlux N time)
    criticalBesovFluxSummable : ∀ N →
      _≤_
        (integral (criticalBesovFlux N) initialTime finalTime)
        expenditureBound
    criticalBesovEnvelopeTimeIntegralUniform : ∀ N →
      _≤_
        (integral (criticalBesovEnvelope N) initialTime finalTime)
        expenditureBound

open CriticalBesovEndpointExpenditure public

record FrequencyLocalizedBKMAlternative
    {c t r : Level}
    (Cutoff : Set c)
    (Time : Set t)
    (Scalar : Set r) :
    Set (lsuc (c ⊔ t ⊔ r)) where
  field
    criticalFrequency : Time → Nat
    lowFrequencyVorticity : Cutoff → Time → Scalar
    _≤_ : Scalar → Scalar → Set r
    localizedBound : Scalar
    integral : (Time → Scalar) → Time → Time → Scalar
    initialTime finalTime : Time
    localizedExpenditureUniform : ∀ N →
      _≤_
        (integral (lowFrequencyVorticity N) initialTime finalTime)
        localizedBound

open FrequencyLocalizedBKMAlternative public

bkmExpenditureCompositionImplemented : Bool
bkmExpenditureCompositionImplemented = true

bkmExpenditureCompositionImplementedIsTrue :
  bkmExpenditureCompositionImplemented ≡ true
bkmExpenditureCompositionImplementedIsTrue = refl

quarticControlImpliesUniformBKMExpenditureClosed : Bool
quarticControlImpliesUniformBKMExpenditureClosed = false

quarticControlImpliesUniformBKMExpenditureClosedIsFalse :
  quarticControlImpliesUniformBKMExpenditureClosed ≡ false
quarticControlImpliesUniformBKMExpenditureClosedIsFalse = refl
