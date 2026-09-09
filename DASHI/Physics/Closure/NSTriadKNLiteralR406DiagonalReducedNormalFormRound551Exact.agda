module DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalReducedNormalFormRound551Exact where

------------------------------------------------------------------------
-- ROUND551 / LITERAL R406 REMAINDER WITH THE DIAGONAL ELIMINATED EXACTLY
--
-- R547 gives, on one physical output fibre,
--
--   factoredFull = diagonalNonlinear + 2 * literalWeightedRemainder.
--
-- R550 gives on the SAME diagonal carrier
--
--   diagonalNonlinear = selfGram + selfFluxTangent.
--
-- Therefore exactly
--
--   2 * literalWeightedRemainder
--     = factoredFull - selfGram - selfFluxTangent.
--
-- R400 constructs all positivity witnesses needed for both the unordered
-- off-diagonal R396 list and the self-pairs, so no caller-supplied positivity
-- strengthening is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNLiteralDiagonalSumDecompositionRound550Exact as R550

F : C3.RealField _
F = Rational.rationalRealField

module Reduced
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module NF = R547.NormalForm physicalSystem S
  module Diag = R550.LiteralDiagonal
    physicalSystem S viscosityPositive cutoff output outputNonzero

  items = Diag.fibre

  offDiagonalPositive : NF.O.E.PairRatePositiveOn items
  offDiagonalPositive =
    Rate.physicalOutputFibrePairRatesPositive cutoff output outputNonzero

  literalWeightedRemainder : ℚ
  literalWeightedRemainder =
    R385.sumWeightedRemainder
      (NF.O.E.allR290Pairs items offDiagonalPositive)

  factoredFull : ℚ
  factoredFull = NF.factoredFull output items

  selfGram : ℚ
  selfGram = Diag.literalSelfGramSum

  selfFluxTangent : ℚ
  selfFluxTangent = Diag.literalSelfFluxTangentSum

  twoRemainderIsFactoredMinusSelfTerms :
    R539.two * literalWeightedRemainder
    ≡ (factoredFull - selfGram) - selfFluxTangent
  twoRemainderIsFactoredMinusSelfTerms =
    let
      normal = NF.factoredFullIsDiagonalPlusTwoLiteralRemainder
        output offDiagonalPositive
      diagonal = Diag.literalDiagonalSumDecomposes
    in
    trans
      (sym
        (solve
          (NF.factoredFull output items
            ∷ Diag.literalDiagonalSum
            ∷ literalWeightedRemainder
            ∷ [])))
      (trans
        (cong
          (λ selectedDiagonal →
            (NF.factoredFull output items - selectedDiagonal))
          diagonal)
        (solve
          (factoredFull
            ∷ selfGram
            ∷ selfFluxTangent
            ∷ [])))
    where
    -- The first solver step uses the exact R547 normal-form equality.
    -- Rewriting it explicitly keeps the consumer identity visible.
    _ = normal

round551LiteralR406DiagonalReducedNormalFormClosed : Bool
round551LiteralR406DiagonalReducedNormalFormClosed = true

round551DiagonalCreatesIndependentNonlinearEstimate : Bool
round551DiagonalCreatesIndependentNonlinearEstimate = false

round551TemporalFTCStillRequired : Bool
round551TemporalFTCStillRequired = true

round551FactoredFullSpacetimeBoundClosed : Bool
round551FactoredFullSpacetimeBoundClosed = false

round551R503DirectOffDiagonalBudgetClosed : Bool
round551R503DirectOffDiagonalBudgetClosed = false

round551ClayPromotion : Bool
round551ClayPromotion = false

round551LiteralR406DiagonalReducedNormalFormClosedIsTrue :
  round551LiteralR406DiagonalReducedNormalFormClosed ≡ true
round551LiteralR406DiagonalReducedNormalFormClosedIsTrue = refl

round551ClayPromotionIsFalse : round551ClayPromotion ≡ false
round551ClayPromotionIsFalse = refl
