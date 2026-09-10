module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeGramPairExpansionBidiExact where

------------------------------------------------------------------------
-- SPECTATOR-WEIGHTED AMPLITUDE GRAM DEBT -> EXACT THREE-INDEX PAIR KERNEL
--
-- For fixed spectator beta, R544's amplitude cell is
--
--   A^beta_alpha = w(alpha,beta) A_alpha,
--
-- with w the literal R541/R538 spectator resolvent.  R383 already proves that
-- R180.gramDebt is exactly the unordered pair sum of twice the real Hermitian
-- cross term.  Bilinearity therefore gives, before every norm/absolute value,
--
--   GramDebt(A^beta)
--     = sum_{alpha<gamma}
--         2 w(alpha,beta) w(gamma,beta) Re<A_alpha,A_gamma>.
--
-- This owner introduces no sign or size estimate.  Its purpose is to expose the
-- selected amplitude residual on the same literal pairwise algebra used by the
-- rest of the R290/R406 proof search, rather than leaving it as an opaque norm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeGramLedgerBidiExact as LedgerOwner

F : C3.RealField _
F = Rational.rationalRealField

module PairExpansion
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system

  module Spec = R541.Spectator physicalSystem S
  module Ledger = LedgerOwner.Ledger physicalSystem S

  unweightedAmplitude :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  unweightedAmplitude = R224.mixedPlusMinus S velocity

  weight :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  weight alpha beta = Spec.Swap.pairResolvent alpha beta

  weightedPairKernel :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  weightedPairKernel beta alpha gamma =
    R291.two *
      ((weight alpha beta * weight gamma beta)
        * R179.realHermitianCross
            (unweightedAmplitude alpha)
            (unweightedAmplitude gamma))

  headWeightedPairSum :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  headWeightedPairSum beta alpha [] = 0ℚ
  headWeightedPairSum beta alpha (gamma ∷ rest) =
    weightedPairKernel beta alpha gamma
      + headWeightedPairSum beta alpha rest

  allWeightedPairSum :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  allWeightedPairSum beta [] = 0ℚ
  allWeightedPairSum beta (alpha ∷ rest) =
    headWeightedPairSum beta alpha rest + allWeightedPairSum beta rest

  weightedCellMeaning :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    Ledger.weightedAmplitudeCell beta alpha
    ≡ R291.realScale (weight alpha beta) (unweightedAmplitude alpha)
  weightedCellMeaning beta alpha =
    cong
      (λ selectedWeight →
        C3.complex3Scale selectedWeight (unweightedAmplitude alpha))
      (Spec.spectatorWeightMeaning beta alpha)

  weightedPairGramMeaning :
    (beta alpha gamma : Physical.PhysicalTriadIncidence) →
    R383.pairGram
      (Ledger.weightedAmplitudeCell beta alpha)
      (Ledger.weightedAmplitudeCell beta gamma)
    ≡ weightedPairKernel beta alpha gamma
  weightedPairGramMeaning beta alpha gamma =
    let
      wa = weight alpha beta
      wg = weight gamma beta
      a = unweightedAmplitude alpha
      g = unweightedAmplitude gamma
      leftScale :
        R179.realHermitianCross
          (R291.realScale wa a)
          (R291.realScale wg g)
        ≡ wa *
            R179.realHermitianCross a (R291.realScale wg g)
      leftScale = R291.scaledRealCrossLeft wa a (R291.realScale wg g)
      rightScale :
        R179.realHermitianCross a (R291.realScale wg g)
        ≡ wg * R179.realHermitianCross a g
      rightScale = R291.scaledRealCrossRight wg a g
    in
    trans
      (cong₂
        (λ x y → R291.two * R179.realHermitianCross x y)
        (weightedCellMeaning beta alpha)
        (weightedCellMeaning beta gamma))
      (trans
        (cong (R291.two *_)
          (trans leftScale (cong (wa *_) rightScale)))
        (solve
          (R291.two ∷ wa ∷ wg ∷ R179.realHermitianCross a g ∷ [])))

  headPairExpansion :
    (beta alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    R383.headPairSum
      (Ledger.weightedAmplitudeCell beta alpha)
      (Ledger.weightedAmplitudeCells beta rest)
    ≡ headWeightedPairSum beta alpha rest
  headPairExpansion beta alpha [] = refl
  headPairExpansion beta alpha (gamma ∷ rest) =
    cong₂ _+_
      (weightedPairGramMeaning beta alpha gamma)
      (headPairExpansion beta alpha rest)

  allPairExpansion :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R383.allPairSum (Ledger.weightedAmplitudeCells beta items)
    ≡ allWeightedPairSum beta items
  allPairExpansion beta [] = refl
  allPairExpansion beta (alpha ∷ rest) =
    cong₂ _+_
      (headPairExpansion beta alpha rest)
      (allPairExpansion beta rest)

  weightedAmplitudeGramDebtIsPairKernel :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R180.gramDebt (Ledger.weightedAmplitudeCells beta items)
    ≡ allWeightedPairSum beta items
  weightedAmplitudeGramDebtIsPairKernel beta items =
    trans
      (R383.r180GramDebtIsAllPairSum
        (Ledger.weightedAmplitudeCells beta items))
      (allPairExpansion beta items)

weightedAmplitudeGramPairExpansionClosed : Bool
weightedAmplitudeGramPairExpansionClosed = true

weightedAmplitudeGramPairExpansionIntroducesEstimate : Bool
weightedAmplitudeGramPairExpansionIntroducesEstimate = false

weightedAmplitudeGramPairKernelCutoffUniformBoundClosed : Bool
weightedAmplitudeGramPairKernelCutoffUniformBoundClosed = false

clayPromotion : Bool
clayPromotion = false

weightedAmplitudeGramPairExpansionClosedIsTrue :
  weightedAmplitudeGramPairExpansionClosed ≡ true
weightedAmplitudeGramPairExpansionClosedIsTrue = refl

weightedAmplitudeGramPairExpansionIntroducesEstimateIsFalse :
  weightedAmplitudeGramPairExpansionIntroducesEstimate ≡ false
weightedAmplitudeGramPairExpansionIntroducesEstimateIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
