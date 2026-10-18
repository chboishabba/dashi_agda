{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyNonlinearRemainderRound601Exact where

------------------------------------------------------------------------
-- ROUND601 / CENTERED CAUCHY DYNAMIC PAIR -> NONLINEAR REMAINDER NORMAL FORM
--
-- R600 isolates the remaining dynamic A3/Cauchy discrepancy as one complete
-- full-square pair scalar
--
--   2 R K_ab T_ab + n (r_a+r_b) G_ab.
--
-- On the literal R291 damped Gram pair,
--
--   T_ab = -(r_a+r_b) G_ab + N_ab,
--
-- and on the selected nonzero output fibre R595 proves
--
--   K_ab (r_a+r_b) = 1.
--
-- Hence, pointwise on the SAME physical fibre,
--
--   2 R K_ab T_ab + n (r_a+r_b) G_ab
--     =
--   2 R K_ab N_ab
--     + (n (r_a+r_b) - 2 R) G_ab.
--
-- This module lifts that exact rewrite to the literal complete full square
-- while carrying output-membership proofs explicitly.  No norm, absolute
-- value, sign estimate, spacetime estimate, or new PDE inequality enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact as R596
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as R595
import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact as R600
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Base = R600.FixedOutput physicalSystem S L H P output
  module Dynamic = Base.Dynamic viscosityPositive outputNonzero
  module C = R596.FixedOutput
    physicalSystem S viscosityPositive output outputNonzero
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Resolved = R595.PhysicalResolved physicalSystem S
  module OnOutput =
    Resolved.OnNonzeroOutput viscosityPositive output outputNonzero

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Base.fibre

  pair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence →
    R291.DampedCellPair
  pair = C.Swap.Q

  nonlinearRemainder :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  nonlinearRemainder alpha beta =
    R291.nonlinearGramRemainder (pair alpha beta)

  tangentLaw :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R291.gramTangent (pair alpha beta)
    ≡
    (0ℚ - (Base.rate alpha + Base.rate beta))
      * Base.gram alpha beta
      + nonlinearRemainder alpha beta
  tangentLaw alpha beta =
    R291.gramPairDampedTangent (pair alpha beta)

  pairResolventLaw :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    C.Swap.pairResolvent alpha beta
      * (Base.rate alpha + Base.rate beta)
    ≡ 1ℚ
  pairResolventLaw alpha beta alphaOutput betaOutput =
    OnOutput.physicalPairResolventLawOnOutput
      alpha beta alphaOutput betaOutput

  centeredDynamicRemainderPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  centeredDynamicRemainderPair alpha beta =
    R600.centeredDynamicRemainderPair
      Base.n Base.rateTotal
      Base.rate
      C.Swap.pairResolvent
      Base.gram
      nonlinearRemainder
      alpha beta

  pointwiseNormalForm :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    Dynamic.centeredDynamicResolvedPair alpha beta
    ≡ centeredDynamicRemainderPair alpha beta
  pointwiseNormalForm alpha beta alphaOutput betaOutput
    rewrite tangentLaw alpha beta
          | pairResolventLaw alpha beta alphaOutput betaOutput =
    solve
      ( Base.n
      ∷ Base.rateTotal
      ∷ Base.rate alpha
      ∷ Base.rate beta
      ∷ C.Swap.pairResolvent alpha beta
      ∷ Base.gram alpha beta
      ∷ nonlinearRemainder alpha beta
      ∷ [])

------------------------------------------------------------------------
-- Membership-aware finite lifting.
------------------------------------------------------------------------

  rowCongruentOnOutput :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn items → Physical.k beta ≡ output) →
    R539.rowSum Dynamic.centeredDynamicResolvedPair alpha items
    ≡ R539.rowSum centeredDynamicRemainderPair alpha items
  rowCongruentOnOutput alpha alphaOutput [] allOutput = refl
  rowCongruentOnOutput alpha alphaOutput (beta ∷ rest) allOutput =
    cong₂ _+_
      (pointwiseNormalForm
        alpha beta alphaOutput (allOutput beta R396.here))
      (rowCongruentOnOutput
        alpha alphaOutput rest
        (λ gamma member → allOutput gamma (R396.there member)))

  columnCongruentOnOutput :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.k beta ≡ output →
    R539.columnSum Dynamic.centeredDynamicResolvedPair items beta
    ≡ R539.columnSum centeredDynamicRemainderPair items beta
  columnCongruentOnOutput [] allOutput beta betaOutput = refl
  columnCongruentOnOutput (alpha ∷ rest) allOutput beta betaOutput =
    cong₂ _+_
      (pointwiseNormalForm
        alpha beta (allOutput alpha R396.here) betaOutput)
      (columnCongruentOnOutput
        rest
        (λ gamma member → allOutput gamma (R396.there member))
        beta betaOutput)

  fullSquareCongruentOnOutput :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    R543.fullSquareSum Dynamic.centeredDynamicResolvedPair items
    ≡ R543.fullSquareSum centeredDynamicRemainderPair items
  fullSquareCongruentOnOutput [] allOutput = refl
  fullSquareCongruentOnOutput (alpha ∷ rest) allOutput
    rewrite
      pointwiseNormalForm
        alpha alpha
        (allOutput alpha R396.here)
        (allOutput alpha R396.here)
        | rowCongruentOnOutput
            alpha
            (allOutput alpha R396.here)
            rest
            (λ beta member → allOutput beta (R396.there member))
        | columnCongruentOnOutput
            rest
            (λ beta member → allOutput beta (R396.there member))
            alpha
            (allOutput alpha R396.here)
        | fullSquareCongruentOnOutput
            rest
            (λ beta member → allOutput beta (R396.there member)) =
    refl

  literalCenteredDynamicNonlinearRemainderNormalForm :
    R543.fullSquareSum Dynamic.centeredDynamicResolvedPair fibre
    ≡ R543.fullSquareSum centeredDynamicRemainderPair fibre
  literalCenteredDynamicNonlinearRemainderNormalForm =
    fullSquareCongruentOnOutput
      fibre
      (Rate.allElementsHaveOutput Base.cutoff output)

------------------------------------------------------------------------
-- Status / exact remaining analytic boundary.
------------------------------------------------------------------------

round601LiteralR291DynamicRemainderNormalFormClosed : Bool
round601LiteralR291DynamicRemainderNormalFormClosed = true

round601CarriesNonzeroOutputReciprocalPremiseExactly : Bool
round601CarriesNonzeroOutputReciprocalPremiseExactly = true

round601IntroducesEstimate : Bool
round601IntroducesEstimate = false

round601CenteredDynamicRemainderPaid : Bool
round601CenteredDynamicRemainderPaid = false

round601CutoffUniformSpacetimeBoundClosed : Bool
round601CutoffUniformSpacetimeBoundClosed = false

round601ClayPromotion : Bool
round601ClayPromotion = false

round601LiteralR291DynamicRemainderNormalFormClosedIsTrue :
  round601LiteralR291DynamicRemainderNormalFormClosed ≡ true
round601LiteralR291DynamicRemainderNormalFormClosedIsTrue = refl

round601CarriesNonzeroOutputReciprocalPremiseExactlyIsTrue :
  round601CarriesNonzeroOutputReciprocalPremiseExactly ≡ true
round601CarriesNonzeroOutputReciprocalPremiseExactlyIsTrue = refl

round601IntroducesEstimateIsFalse :
  round601IntroducesEstimate ≡ false
round601IntroducesEstimateIsFalse = refl

round601CenteredDynamicRemainderPaidIsFalse :
  round601CenteredDynamicRemainderPaid ≡ false
round601CenteredDynamicRemainderPaidIsFalse = refl

round601CutoffUniformSpacetimeBoundClosedIsFalse :
  round601CutoffUniformSpacetimeBoundClosed ≡ false
round601CutoffUniformSpacetimeBoundClosedIsFalse = refl

round601ClayPromotionIsFalse :
  round601ClayPromotion ≡ false
round601ClayPromotionIsFalse = refl
