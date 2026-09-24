module DASHI.Physics.Closure.NSTriadKNR567ForcingCellPhysicalEnvelopeExact where

------------------------------------------------------------------------
-- PERIODIC B / LITERAL R567 FORCING CELL -> POSITIVE PHYSICAL ENVELOPE
--
-- On one nonzero physical output fibre R566 gives exactly
--
--   forcingPair(alpha,beta)
--     = K(alpha,beta) Re <G_alpha,D_beta>.
--
-- The same-output unit-gap theorem gives
--
--   0 <= K(alpha,beta) <= 1/(2 nu),
--
-- while R579 gives the square-root-free Hermitian Young bound
--
--   |Re <G_alpha,D_beta>|
--     <= ||G_alpha||^2 + ||D_beta||^2.
--
-- Hence each literal R567 forcing cell obeys the cutoff-independent bound
--
--   forcingPair(alpha,beta)
--     <= C_nu ( ||G_alpha||^2 + ||D_beta||^2 ).
--
-- This is the first direct positive physical envelope on the SAME R567 cell.
-- No fibre-cardinality factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventUnitGapCeilingBidiExact as Ceiling
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as Young

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalEnvelope
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem) where

  module T = R566.PhysicalTranspose physicalSystem S
  module C = Ceiling.SameOutputResolventCeiling
    physicalSystem S viscosityPositive unitGap

  forcingMass :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  forcingMass alpha beta =
    L2.complex3NormSquared (T.Row.D.doubleForcing alpha)
    + L2.complex3NormSquared (T.Row.doubleCell beta)

  forcingMassNonnegative :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    0ℚ ≤ forcingMass alpha beta
  forcingMassNonnegative alpha beta =
    ℚP.+-mono-≤
      (Separation.complex3NormSquaredNonnegative
        (T.Row.D.doubleForcing alpha))
      (Separation.complex3NormSquaredNonnegative
        (T.Row.doubleCell beta))

  forcingCellBelowLocalMass :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    T.forcingPair alpha beta
    ≤ T.Row.Swap.pairResolvent alpha beta * forcingMass alpha beta
  forcingCellBelowLocalMass output outputNonzero alpha beta alphaK betaK =
    let
      k = T.Row.Swap.pairResolvent alpha beta
      c = R179.realHermitianCross
        (T.Row.D.doubleForcing alpha)
        (T.Row.doubleCell beta)
      kNN = C.pairResolventNonnegative
        output outputNonzero alpha beta alphaK betaK
      cYoung :
        ∣ c ∣ ≤ forcingMass alpha beta
      cYoung =
        Young.rationalRealHermitianYoung
          (T.Row.D.doubleForcing alpha)
          (T.Row.doubleCell beta)
      first :
        k * c ≤ k * ∣ c ∣
      first =
        let instance kNNI : NonNegative k
            kNNI = nonNegative kNN
        in
        ℚP.*-monoˡ-≤-nonNeg k (ℚP.p≤∣p∣ c)
      second :
        k * ∣ c ∣ ≤ k * forcingMass alpha beta
      second =
        let instance kNNI : NonNegative k
            kNNI = nonNegative kNN
        in
        ℚP.*-monoˡ-≤-nonNeg k cYoung
      scalarized :
        T.forcingPair alpha beta ≡ k * c
      scalarized = T.forcingPairScalarized alpha beta
    in
    subst
      (λ lower → lower ≤ k * forcingMass alpha beta)
      (sym scalarized)
      (ℚP.≤-trans first second)

  forcingCellBelowCutoffIndependentEnvelope :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    T.forcingPair alpha beta
    ≤ C.ceiling * forcingMass alpha beta
  forcingCellBelowCutoffIndependentEnvelope
      output outputNonzero alpha beta alphaK betaK =
    let
      local = forcingCellBelowLocalMass
        output outputNonzero alpha beta alphaK betaK
      kBelow = C.pairResolventBelowCeiling
        output outputNonzero alpha beta alphaK betaK
      massNN = forcingMassNonnegative alpha beta
      scaled :
        T.Row.Swap.pairResolvent alpha beta * forcingMass alpha beta
        ≤ C.ceiling * forcingMass alpha beta
      scaled =
        let instance massNNI : NonNegative (forcingMass alpha beta)
            massNNI = nonNegative massNN
        in
        ℚP.*-monoʳ-≤-nonNeg (forcingMass alpha beta) kBelow
    in
    ℚP.≤-trans local scaled

r567LiteralForcingCellPositiveEnvelopeClosed : Bool
r567LiteralForcingCellPositiveEnvelopeClosed = true

r567LiteralForcingCellEnvelopeCutoffDependent : Bool
r567LiteralForcingCellEnvelopeCutoffDependent = false

r567LiteralForcingCellEnvelopeUsesFibreCardinality : Bool
r567LiteralForcingCellEnvelopeUsesFibreCardinality = false

r567ForcingCellToR571ExactTaylorSampleClosedHere : Bool
r567ForcingCellToR571ExactTaylorSampleClosedHere = false

r567LiteralForcingCellPositiveEnvelopeClosedIsTrue :
  r567LiteralForcingCellPositiveEnvelopeClosed ≡ true
r567LiteralForcingCellPositiveEnvelopeClosedIsTrue = refl

r567LiteralForcingCellEnvelopeCutoffDependentIsFalse :
  r567LiteralForcingCellEnvelopeCutoffDependent ≡ false
r567LiteralForcingCellEnvelopeCutoffDependentIsFalse = refl
