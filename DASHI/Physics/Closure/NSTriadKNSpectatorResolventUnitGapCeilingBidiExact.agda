module DASHI.Physics.Closure.NSTriadKNSpectatorResolventUnitGapCeilingBidiExact where

------------------------------------------------------------------------
-- SAME-NONZERO-OUTPUT SPECTATOR RESOLVENT <= 1 / (2 nu)
--
-- Reuse R450's physical cell-rate floor and R449's positive reciprocal
-- antitonicity machinery.  If alpha and beta both lie over one nonzero physical
-- output, then
--
--   nu <= cellRate alpha,
--   nu <= cellRate beta,
--
-- hence
--
--   2 nu <= pairRate(alpha,beta)
--
-- and the literal R538/R541 pair resolvent obeys the cutoff-independent ceiling
--
--   1 / pairRate(alpha,beta) <= 1 / (2 nu).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

module SameOutputResolventCeiling
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem) where

  module Floor = R450.PhysicalCellRateFloor
    physicalSystem S viscosityPositive unitGap
  module Pair = R538.PairSwap physicalSystem S

  nu : ℚ
  nu = Floor.nu

  ceiling : ℚ
  ceiling = R449.diagonalCeilingAt nu Floor.nuPositive

  pairRateMeaning :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R291.pairRate (Pair.Q alpha beta)
    ≡ Floor.P.D.Pair.cellRate alpha + Floor.P.D.Pair.cellRate beta
  pairRateMeaning alpha beta = refl

  pairRateAtLeastTwoNu :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    R449.two * nu ≤ R291.pairRate (Pair.Q alpha beta)
  pairRateAtLeastTwoNu output outputNonzero alpha beta alphaK betaK =
    let
      alphaFloor =
        Floor.cellRateAtLeastNuFromNonzeroOutput
          output outputNonzero alpha alphaK
      betaFloor =
        Floor.cellRateAtLeastNuFromNonzeroOutput
          output outputNonzero beta betaK
      raw :
        nu + nu
        ≤ Floor.P.D.Pair.cellRate alpha + Floor.P.D.Pair.cellRate beta
      raw = ℚP.+-mono-≤ alphaFloor betaFloor
      upperRewritten :
        nu + nu ≤ R291.pairRate (Pair.Q alpha beta)
      upperRewritten =
        subst
          ((nu + nu) ≤_)
          (sym (pairRateMeaning alpha beta))
          raw
      lowerMeaning : nu + nu ≡ R449.two * nu
      lowerMeaning = solve (nu ∷ [])
    in
    subst
      (_≤ R291.pairRate (Pair.Q alpha beta))
      lowerMeaning
      upperRewritten

  pairRatePositive :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    0ℚ < R291.pairRate (Pair.Q alpha beta)
  pairRatePositive output outputNonzero alpha beta alphaK betaK =
    ℚP.<-≤-trans
      (R449.twicePositive Floor.nuPositive)
      (pairRateAtLeastTwoNu output outputNonzero alpha beta alphaK betaK)

  pairResolventBelowCeiling :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    Pair.pairResolvent alpha beta ≤ ceiling
  pairResolventBelowCeiling output outputNonzero alpha beta alphaK betaK =
    let
      denom = R291.pairRate (Pair.Q alpha beta)
      denomPositive =
        pairRatePositive output outputNonzero alpha beta alphaK betaK
      twoNuPositive = R449.twicePositive Floor.nuPositive
      floorBelow =
        pairRateAtLeastTwoNu output outputNonzero alpha beta alphaK betaK
      asPositive :
        Pair.pairResolvent alpha beta
        ≡ Quotient.positiveReciprocal denom denomPositive
      asPositive = R449.safeReciprocalIsPositiveReciprocal denom denomPositive
      antitone :
        Quotient.positiveReciprocal denom denomPositive
        ≤ Quotient.positiveReciprocal (R449.two * nu) twoNuPositive
      antitone =
        Quotient.reciprocalAntitonePositive
          (R449.two * nu) denom
          twoNuPositive denomPositive floorBelow
    in
    subst
      (_≤ ceiling)
      (sym asPositive)
      antitone

sameOutputSpectatorResolventCeilingClosed : Bool
sameOutputSpectatorResolventCeilingClosed = true

sameOutputSpectatorResolventCeilingCutoffDependent : Bool
sameOutputSpectatorResolventCeilingCutoffDependent = false

sameOutputSpectatorResolventCeilingRequiresUnitGap : Bool
sameOutputSpectatorResolventCeilingRequiresUnitGap = true

clayPromotion : Bool
clayPromotion = false
