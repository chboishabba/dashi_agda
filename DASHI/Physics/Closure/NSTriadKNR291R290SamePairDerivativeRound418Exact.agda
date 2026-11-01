module DASHI.Physics.Closure.NSTriadKNR291R290SamePairDerivativeRound418Exact where

------------------------------------------------------------------------
-- ROUND418 / SAME-PAIR TEMPORAL COMPILER: R291 -> R290
--
-- R417 proves that actual derivatives of the two literal cell curves give the
-- exact R291 real-Hermitian Gram tangent.  R416 proves that, for a fixed
-- resolvent weight, the Gram derivative gives the exact R290 weighted-flux
-- derivative.  The only remaining seam between those owners is carrier
-- identity: the R290 pair must literally be the scalar image of the SAME R291
-- pair at every time.
--
-- This owner makes that identity explicit and composes the two derivative
-- compilers.  No new PDE estimate, no alternate flux and no finite-sum
-- derivative theorem are introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417

F : C3.RealField _
F = Rational.rationalRealField

record SameR291R290PairCurve (Time : Set) : Set where
  field
    r291Curve : R417.DampedCellPairCurve Time
    r290Curve : R416.FixedResolventPairCurve Time

    sameGram :
      (time : Time) →
      R290.gram (R416.pairAt r290Curve time)
      ≡ R291.gram (R417.pairAt r291Curve time)

    sameGramTangent :
      (time : Time) →
      R290.gramTangent (R416.pairAt r290Curve time)
      ≡ R291.gramTangent (R417.pairAt r291Curve time)

open SameR291R290PairCurve public

module SamePairDerivative
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (H : R417.HermitianDerivativeCalculus
      Time VectorDerivativeOf ScalarDerivativeOf)
    (C : R416.ScalarConstantDerivativeCalculus
      Time ScalarDerivativeOf) where

  module Gram = R417.ActualGramDerivative
    Time VectorDerivativeOf ScalarDerivativeOf H
  module Flux = R416.PairDerivative Time ScalarDerivativeOf C

  r291GramDerivativeTransportedToR290 :
    (P : SameR291R290PairCurve Time) →
    VectorDerivativeOf
      (R417.cellACurve (r291Curve P))
      (R417.tangentACurve (r291Curve P)) →
    VectorDerivativeOf
      (R417.cellBCurve (r291Curve P))
      (R417.tangentBCurve (r291Curve P)) →
    ScalarDerivativeOf
      (R416.gramCurve (r290Curve P))
      (R416.gramTangentCurve (r290Curve P))
  r291GramDerivativeTransportedToR290 P dA dB =
    R416.transportDerivative C
      (λ time → sym (sameGram P time))
      (λ time → sym (sameGramTangent P time))
      (Gram.cellDerivativesBuildExactR291GramDerivative
        (r291Curve P) dA dB)

  cellDerivativesBuildExactR290WeightedFluxDerivative :
    (P : SameR291R290PairCurve Time) →
    VectorDerivativeOf
      (R417.cellACurve (r291Curve P))
      (R417.tangentACurve (r291Curve P)) →
    VectorDerivativeOf
      (R417.cellBCurve (r291Curve P))
      (R417.tangentBCurve (r291Curve P)) →
    ScalarDerivativeOf
      (R416.weightedFluxCurve (r290Curve P))
      (R416.weightedFluxTangentCurve (r290Curve P))
  cellDerivativesBuildExactR290WeightedFluxDerivative P dA dB =
    Flux.gramDerivativeBuildsWeightedFluxDerivative
      (r290Curve P)
      (r291GramDerivativeTransportedToR290 P dA dB)

round418R291ToR290TemporalCarrierWeldExplicit : Bool
round418R291ToR290TemporalCarrierWeldExplicit = true

round418PerPairWeightedFluxDerivativeReducedToTwoCellDerivatives : Bool
round418PerPairWeightedFluxDerivativeReducedToTwoCellDerivatives = true

round418NoNewNavierStokesEstimateIntroduced : Bool
round418NoNewNavierStokesEstimateIntroduced = true

round418PerPairWeightedFluxDerivativeReducedToTwoCellDerivativesIsTrue :
  round418PerPairWeightedFluxDerivativeReducedToTwoCellDerivatives ≡ true
round418PerPairWeightedFluxDerivativeReducedToTwoCellDerivativesIsTrue = refl
