module DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact where

------------------------------------------------------------------------
-- ROUND545 / LITERAL PAIR-REMAINDER ROW -> TWO WEIGHTED VECTOR AGGREGATES
--
-- Fix a spectator beta.  R538's physical pair scalar is
--
--   F(alpha,beta)
--     = K(alpha,beta) * 2(
--         Re<G_alpha,D_beta> + Re<D_alpha,G_beta> ).
--
-- R541 realizes K(alpha,beta) as an R294 one-cell weight in alpha.  Finite
-- real-Hermitian bilinearity therefore gives, on any finite alpha list,
--
--   sum_alpha F(alpha,beta)
--     = 2( Re<sum K G_alpha,D_beta>
--          + Re<sum K D_alpha,G_beta> ).
--
-- On the complete fixed-output fibre, R542 and R544 identify those two vector
-- sums as four copies of the weighted commutator and amplitude folds.
-- No norm or spacetime estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleForcingCommutatorFoldRound542Exact as R542
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440

F : C3.RealField _
F = Rational.rationalRealField

module Row
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem

  module D = R388.PhysicalDoubleMixed physicalSystem S
  module Swap = R538.PairSwap physicalSystem S
  module Spec = R541.Spectator physicalSystem S

  system : Audit.FiniteComplex3GalerkinSystem F E I
  system = Field30.finiteSystem physicalSystem

  doubleCell : Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleCell = R225.doubleMixedCell S D.Pair.velocity

  pairScalar :
    Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairScalar = Swap.symmetricWeightedRemainder

  module Weighted (beta : Physical.PhysicalTriadIncidence) where
    W = Spec.spectatorWeight beta
    module Force = R542.Fold physicalSystem S W
    module Amp = R544.Fold physicalSystem S W

  spectatorRow :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  spectatorRow beta [] = 0ℚ
  spectatorRow beta (alpha ∷ rest) =
    pairScalar alpha beta + spectatorRow beta rest

  forcingHalf :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  forcingHalf beta [] = 0ℚ
  forcingHalf beta (alpha ∷ rest) =
    R179.realHermitianCross
      (Weighted.Force.weightedDouble beta alpha)
      (doubleCell beta)
    + forcingHalf beta rest

  amplitudeHalf :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  amplitudeHalf beta [] = 0ℚ
  amplitudeHalf beta (alpha ∷ rest) =
    R179.realHermitianCross
      (Weighted.Amp.weightedDoubleCell beta alpha)
      (D.doubleForcing beta)
    + amplitudeHalf beta rest

  pairScalarPointwise :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairScalar alpha beta
    ≡ R291.two *
        (R179.realHermitianCross
          (Weighted.Force.weightedDouble beta alpha)
          (doubleCell beta)
        + R179.realHermitianCross
          (Weighted.Amp.weightedDoubleCell beta alpha)
          (D.doubleForcing beta))
  pairScalarPointwise alpha beta
    rewrite Spec.spectatorWeightMeaning beta alpha
          | R291.scaledRealCrossLeft
              (Swap.pairResolvent alpha beta)
              (D.doubleForcing alpha) (doubleCell beta)
          | R291.scaledRealCrossLeft
              (Swap.pairResolvent alpha beta)
              (doubleCell alpha) (D.doubleForcing beta) =
    solve
      (Swap.pairResolvent alpha beta
        ∷ R179.realHermitianCross (D.doubleForcing alpha) (doubleCell beta)
        ∷ R179.realHermitianCross (doubleCell alpha) (D.doubleForcing beta)
        ∷ [])

  spectatorRowIsTwoHalves :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    spectatorRow beta items
    ≡ R291.two * (forcingHalf beta items + amplitudeHalf beta items)
  spectatorRowIsTwoHalves beta [] = refl
  spectatorRowIsTwoHalves beta (alpha ∷ rest)
    rewrite pairScalarPointwise alpha beta
          | spectatorRowIsTwoHalves beta rest =
    solve
      (R179.realHermitianCross
          (Weighted.Force.weightedDouble beta alpha) (doubleCell beta)
        ∷ forcingHalf beta rest
        ∷ R179.realHermitianCross
          (Weighted.Amp.weightedDoubleCell beta alpha) (D.doubleForcing beta)
        ∷ amplitudeHalf beta rest
        ∷ [])

  forcingHalfFactors :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    forcingHalf beta items
    ≡ R179.realHermitianCross
        (R224.foldVector (Weighted.Force.weightedDouble beta) items)
        (doubleCell beta)
  forcingHalfFactors beta [] =
    sym (R440.crossZeroLeft (doubleCell beta))
    where open import Relation.Binary.PropositionalEquality using (sym)
  forcingHalfFactors beta (alpha ∷ rest) =
    trans
      (cong₂ _+_ refl (forcingHalfFactors beta rest))
      (sym
        (R291.realCrossAddLeft
          (Weighted.Force.weightedDouble beta alpha)
          (R224.foldVector (Weighted.Force.weightedDouble beta) rest)
          (doubleCell beta)))
    where open import Relation.Binary.PropositionalEquality using (sym)

  amplitudeHalfFactors :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    amplitudeHalf beta items
    ≡ R179.realHermitianCross
        (R224.foldVector (Weighted.Amp.weightedDoubleCell beta) items)
        (D.doubleForcing beta)
  amplitudeHalfFactors beta [] =
    sym (R440.crossZeroLeft (D.doubleForcing beta))
    where open import Relation.Binary.PropositionalEquality using (sym)
  amplitudeHalfFactors beta (alpha ∷ rest) =
    trans
      (cong₂ _+_ refl (amplitudeHalfFactors beta rest))
      (sym
        (R291.realCrossAddLeft
          (Weighted.Amp.weightedDoubleCell beta alpha)
          (R224.foldVector (Weighted.Amp.weightedDoubleCell beta) rest)
          (D.doubleForcing beta)))
    where open import Relation.Binary.PropositionalEquality using (sym)

  spectatorRowFactors :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    spectatorRow beta items
    ≡ R291.two *
        (R179.realHermitianCross
          (R224.foldVector (Weighted.Force.weightedDouble beta) items)
          (doubleCell beta)
        + R179.realHermitianCross
          (R224.foldVector (Weighted.Amp.weightedDoubleCell beta) items)
          (D.doubleForcing beta))
  spectatorRowFactors beta items =
    trans
      (spectatorRowIsTwoHalves beta items)
      (cong
        (R291.two *_)
        (cong₂ _+_
          (forcingHalfFactors beta items)
          (amplitudeHalfFactors beta items)))

  fixedOutputSpectatorRowFactorsThroughR294 :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        C = R224.foldVector (Weighted.Force.commutator beta) items
        A = R224.foldVector (Weighted.Amp.amplitude beta) items
        fourC = C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
        fourA = C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
    in
    spectatorRow beta items
    ≡ R291.two *
        (R179.realHermitianCross fourC (doubleCell beta)
        + R179.realHermitianCross fourA (D.doubleForcing beta))
  fixedOutputSpectatorRowFactorsThroughR294 output beta =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    trans
      (spectatorRowFactors beta items)
      (cong
        (R291.two *_)
        (cong₂ _+_
          (cong
            (λ v → R179.realHermitianCross v (doubleCell beta))
            (Weighted.Force.fixedOutputWeightedDoubleIsFourCommutatorFolds beta output))
          (cong
            (λ v → R179.realHermitianCross v (D.doubleForcing beta))
            (Weighted.Amp.fixedOutputWeightedDoubleCellIsFourAmplitudeFolds beta output))))

round545LiteralSpectatorRowFactorizationClosed : Bool
round545LiteralSpectatorRowFactorizationClosed = true

round545FullSquareRowUsesR294Commutator : Bool
round545FullSquareRowUsesR294Commutator = true

round545IntroducesAnyNormEstimate : Bool
round545IntroducesAnyNormEstimate = false

round545SignedSpacetimeEstimateClosed : Bool
round545SignedSpacetimeEstimateClosed = false

round545ClayPromotion : Bool
round545ClayPromotion = false

round545LiteralSpectatorRowFactorizationClosedIsTrue :
  round545LiteralSpectatorRowFactorizationClosed ≡ true
round545LiteralSpectatorRowFactorizationClosedIsTrue = refl

round545IntroducesAnyNormEstimateIsFalse :
  round545IntroducesAnyNormEstimate ≡ false
round545IntroducesAnyNormEstimateIsFalse = refl

round545ClayPromotionIsFalse : round545ClayPromotion ≡ false
round545ClayPromotionIsFalse = refl
