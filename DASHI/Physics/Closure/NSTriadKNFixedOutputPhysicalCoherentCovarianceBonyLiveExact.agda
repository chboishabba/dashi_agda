module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE PHYSICAL COVARIANCE -> THREE CENTERED BONY WORKS
--
-- On the literal physical output fibre:
--
--   rate_tau = nu (|p_tau|^2 + |q_tau|^2) = nu S_tau.
--
-- Therefore the exact d1b2 pair graph factors by viscosity:
--
--   sum_{a<b} (rate_a-rate_b)(w_a-w_b)
--     = nu sum_{a<b} (S_a-S_b)(w_a-w_b).
--
-- The existing centered-vector weld identifies the second pair graph with
-- W(M,R_S(A)), while the new Bony owner splits R_S(A) exactly, retaining the
-- GLOBAL centering data, into
--
--   R_FL + R_HH + R_CC.
--
-- Hence the ACTUAL live covariance numerator is exactly
--
--   nu * [ -W(M,R_FL) - W(M,R_HH) - W(M,R_CC) ].
--
-- No class-local recentering, norm, absolute value, pair count, or cutoff
-- factor is introduced.  This is the same-object surface on which the three
-- physical region estimates must now land.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianVectorResidualExact as Input
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianBonyVectorExact as Bony

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic finite scaling of the complete pair graph.
------------------------------------------------------------------------

pairAgainstHeadScale :
  ∀ {A : Set} →
  (scalar : ℚ) →
  (multiplier work : A → ℚ) →
  (head : A) →
  (rest : List A) →
  Pair.pairAgainstHead
    (λ x → scalar * multiplier x) work head rest
  ≡ scalar * Pair.pairAgainstHead multiplier work head rest
pairAgainstHeadScale scalar multiplier work head [] =
  solve (scalar ∷ [])
pairAgainstHeadScale scalar multiplier work head (x ∷ xs) =
  trans
    (cong₂ _+_
      (solve
        ( scalar
        ∷ multiplier head ∷ multiplier x
        ∷ work head ∷ work x
        ∷ []))
      (pairAgainstHeadScale scalar multiplier work head xs))
    (solve
      ( scalar
      ∷ (multiplier head - multiplier x) * (work head - work x)
      ∷ Pair.pairAgainstHead multiplier work head xs
      ∷ []))

pairDifferenceScale :
  ∀ {A : Set} →
  (scalar : ℚ) →
  (multiplier work : A → ℚ) →
  (items : List A) →
  Pair.pairDifferenceWorkSum
    (λ x → scalar * multiplier x) work items
  ≡ scalar * Pair.pairDifferenceWorkSum multiplier work items
pairDifferenceScale scalar multiplier work [] =
  solve (scalar ∷ [])
pairDifferenceScale scalar multiplier work (head ∷ rest) =
  trans
    (cong₂ _+_
      (pairAgainstHeadScale scalar multiplier work head rest)
      (pairDifferenceScale scalar multiplier work rest))
    (solve
      ( scalar
      ∷ Pair.pairAgainstHead multiplier work head rest
      ∷ Pair.pairDifferenceWorkSum multiplier work rest
      ∷ []))


pairAgainstHeadRateTransport :
  ∀ {A : Set} →
  (left right work : A → ℚ) →
  ((x : A) → left x ≡ right x) →
  (head : A) →
  (rest : List A) →
  Pair.pairAgainstHead left work head rest
  ≡ Pair.pairAgainstHead right work head rest
pairAgainstHeadRateTransport left right work pointwise head [] = refl
pairAgainstHeadRateTransport left right work pointwise head (x ∷ xs) =
  cong₂ _+_
    (cong
      (λ selected →
        selected * (work head - work x))
      (cong₂ _-_ (pointwise head) (pointwise x)))
    (pairAgainstHeadRateTransport
      left right work pointwise head xs)

pairDifferenceRateTransport :
  ∀ {A : Set} →
  (left right work : A → ℚ) →
  ((x : A) → left x ≡ right x) →
  (items : List A) →
  Pair.pairDifferenceWorkSum left work items
  ≡ Pair.pairDifferenceWorkSum right work items
pairDifferenceRateTransport left right work pointwise [] = refl
pairDifferenceRateTransport left right work pointwise (head ∷ rest) =
  cong₂ _+_
    (pairAgainstHeadRateTransport
      left right work pointwise head rest)
    (pairDifferenceRateTransport
      left right work pointwise rest)

module LiveBony
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  nu : ℚ
  nu = Field30.viscosity physicalSystem

  module Split =
    Bony.FixedOutputBony
      {E = E} {I = I}
      S Live.velocity Live.cutoff output

  inputMass :
    Physical.PhysicalTriadIncidence → ℚ
  inputMass = Input.inputMultiplier I

  rateMeaning :
    (tau : Physical.PhysicalTriadIncidence) →
    Live.rate tau ≡ nu * inputMass tau
  rateMeaning tau =
    solve
      ( nu
      ∷ C3.normSquared I (Physical.p tau)
      ∷ C3.normSquared I (Physical.q tau)
      ∷ [])

  pairDifferenceRateIsViscosityInput :
    Pair.pairDifferenceWorkSum
      Live.rate (Live.work output) (Live.fibre output)
    ≡
    nu * Pair.pairDifferenceWorkSum
      inputMass (Live.work output) (Live.fibre output)
  pairDifferenceRateIsViscosityInput =
    trans
      (pairDifferenceRateTransport
        Live.rate
        (λ tau → nu * inputMass tau)
        (Live.work output)
        rateMeaning
        (Live.fibre output))
      (pairDifferenceScale
        nu inputMass (Live.work output) (Live.fibre output))

  inputPairGraphIsCenteredResidualWork :
    Pair.pairDifferenceWorkSum
      inputMass (Live.work output) (Live.fibre output)
    ≡ Split.centeredResidualWork
  inputPairGraphIsCenteredResidualWork =
    Vector.pairDifferenceIsCenteredMultiplierWork
      inputMass Split.value (Live.fibre output)

  liveCovarianceIsViscosityTimesSignedCenteredWork :
    Live.coherentCovarianceNumerator output
    ≡ nu * Split.signedCenteredResidualWork
  liveCovarianceIsViscosityTimesSignedCenteredWork =
    trans
      (Live.exactCentering output)
      (trans
        (cong (0ℚ -_) pairDifferenceRateIsViscosityInput)
        (trans
          (cong
            (λ selected → 0ℚ - nu * selected)
            inputPairGraphIsCenteredResidualWork)
          (solve (nu ∷ Split.centeredResidualWork ∷ []))))

  liveCovarianceIsThreeCenteredBonyWorks :
    Live.coherentCovarianceNumerator output
    ≡
    nu *
      ( (0ℚ - Split.farLowWork)
      + ((0ℚ - Split.highHighWork)
        + (0ℚ - Split.comparableWork)) )
  liveCovarianceIsThreeCenteredBonyWorks =
    trans
      liveCovarianceIsViscosityTimesSignedCenteredWork
      (cong
        (nu *_)
        Split.signedCenteredResidualWorkIsThreeClassWork)

liveD1b2ExactThreeCenteredBonyWorkSplitClosed : Bool
liveD1b2ExactThreeCenteredBonyWorkSplitClosed = true

liveD1b2BonySplitUsesClassLocalCentering : Bool
liveD1b2BonySplitUsesClassLocalCentering = false

liveD1b2BonySplitIntroducesNorm : Bool
liveD1b2BonySplitIntroducesNorm = false

liveD1b2BonySplitIntroducesCardinalityFactor : Bool
liveD1b2BonySplitIntroducesCardinalityFactor = false

liveD1b2FarLowSignedPaymentClosedHere : Bool
liveD1b2FarLowSignedPaymentClosedHere = false

liveD1b2HighHighSignedPaymentClosedHere : Bool
liveD1b2HighHighSignedPaymentClosedHere = false

liveD1b2ComparableOrCriticalCorePaymentClosedHere : Bool
liveD1b2ComparableOrCriticalCorePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

liveD1b2ExactThreeCenteredBonyWorkSplitClosedIsTrue :
  liveD1b2ExactThreeCenteredBonyWorkSplitClosed ≡ true
liveD1b2ExactThreeCenteredBonyWorkSplitClosedIsTrue = refl
