module DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalR290FluxDecompositionRound549Exact where

------------------------------------------------------------------------
-- ROUND549 / R547 DIAGONAL -> SELF-GRAM + WEIGHTED GRAM-FLUX TANGENT
--
-- R548 left the exact semantic role of the R547 diagonal open.  R290 already
-- contains the relevant algebraic identity pointwise:
--
--   weightedFluxTangent = -gram + weightedNonlinearRemainder.
--
-- Hence
--
--   weightedNonlinearRemainder = gram + weightedFluxTangent.
--
-- Specialising R290 to the literal double-mixed self pair (alpha,alpha) shows
-- that the R547 diagonal is not an unrelated nonlinear quantity.  It is exactly
-- the finite sum of a self-Gram term and a weighted Gram-flux tangent term.
--
-- This owner keeps self-pair positivity separate from R396's off-diagonal
-- PairRatePositiveOn carrier.  No positivity theorem is silently strengthened.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Generic R290 rearrangement.
------------------------------------------------------------------------

weightedRemainderIsGramPlusFluxTangent549 :
  (P : R290.DampedGramPair) →
  R290.weightedNonlinearRemainder P
  ≡ R290.gram P + R290.weightedGramFluxTangent P
weightedRemainderIsGramPlusFluxTangent549 P
  rewrite R290.weightedFluxDerivativeIdentity P =
  solve (R290.gram P ∷ R290.weightedNonlinearRemainder P ∷ [])

------------------------------------------------------------------------
-- 2. Literal physical self-pair specialization.
------------------------------------------------------------------------

module Diagonal
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  selfPair :
    (alpha : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha)) →
    R290.DampedGramPair
  selfPair alpha positive =
    Pair.pairRatePositiveBuildsR290 alpha alpha positive

  literalDiagonalPointwise549 :
    (alpha : Physical.PhysicalTriadIncidence) →
    (positive : Positive
      (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha))) →
    Swap.symmetricWeightedRemainder alpha alpha
    ≡ R290.gram (selfPair alpha positive)
      + R290.weightedGramFluxTangent (selfPair alpha positive)
  literalDiagonalPointwise549 alpha positive =
    trans
      (sym
        (Swap.literalR290WeightedRemainderIsSymmetricScalar
          alpha alpha positive))
      (weightedRemainderIsGramPlusFluxTangent549 (selfPair alpha positive))

  ----------------------------------------------------------------------
  -- 3. Least-privilege finite self-pair positivity carrier.
  ----------------------------------------------------------------------

  data SelfRatePositiveOn549 : List Physical.PhysicalTriadIncidence → Set where
    selfPositiveNil549 : SelfRatePositiveOn549 []
    selfPositiveCons549 :
      ∀ {alpha rest} →
      Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha)) →
      SelfRatePositiveOn549 rest →
      SelfRatePositiveOn549 (alpha ∷ rest)

  selfGramSum549 :
    (items : List Physical.PhysicalTriadIncidence) →
    SelfRatePositiveOn549 items → ℚ
  selfGramSum549 [] selfPositiveNil549 = 0ℚ
  selfGramSum549 (alpha ∷ rest) (selfPositiveCons549 positive tailPositive) =
    R290.gram (selfPair alpha positive) + selfGramSum549 rest tailPositive

  selfFluxTangentSum549 :
    (items : List Physical.PhysicalTriadIncidence) →
    SelfRatePositiveOn549 items → ℚ
  selfFluxTangentSum549 [] selfPositiveNil549 = 0ℚ
  selfFluxTangentSum549 (alpha ∷ rest)
      (selfPositiveCons549 positive tailPositive) =
    R290.weightedGramFluxTangent (selfPair alpha positive)
      + selfFluxTangentSum549 rest tailPositive

  literalDiagonalFiniteDecomposition549 :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : SelfRatePositiveOn549 items) →
    R543.diagonalSum Swap.symmetricWeightedRemainder items
    ≡ selfGramSum549 items positive + selfFluxTangentSum549 items positive
  literalDiagonalFiniteDecomposition549 [] selfPositiveNil549 = refl
  literalDiagonalFiniteDecomposition549
      (alpha ∷ rest) (selfPositiveCons549 positive tailPositive)
    rewrite literalDiagonalPointwise549 alpha positive
          | literalDiagonalFiniteDecomposition549 rest tailPositive =
    solve
      (R290.gram (selfPair alpha positive)
        ∷ R290.weightedGramFluxTangent (selfPair alpha positive)
        ∷ selfGramSum549 rest tailPositive
        ∷ selfFluxTangentSum549 rest tailPositive
        ∷ [])

------------------------------------------------------------------------
-- 4. Status: A2 is now an exact decomposition problem, not an opaque semantic
-- classification problem.
------------------------------------------------------------------------

round549GenericR290RemainderDecompositionClosed : Bool
round549GenericR290RemainderDecompositionClosed = true

round549LiteralSelfPairDecompositionClosed : Bool
round549LiteralSelfPairDecompositionClosed = true

round549FiniteDiagonalDecompositionClosed : Bool
round549FiniteDiagonalDecompositionClosed = true

round549SelfPairPositivityBorrowedFromOffDiagonalCarrier : Bool
round549SelfPairPositivityBorrowedFromOffDiagonalCarrier = false

round549DiagonalAutomaticallyZero : Bool
round549DiagonalAutomaticallyZero = false

round549DiagonalSpacetimeTreatmentClosed : Bool
round549DiagonalSpacetimeTreatmentClosed = false

round549LiteralR406SignedCrossPaymentClosed : Bool
round549LiteralR406SignedCrossPaymentClosed = false

round549CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round549CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round549ClayPromotion : Bool
round549ClayPromotion = false

round549GenericR290RemainderDecompositionClosedIsTrue :
  round549GenericR290RemainderDecompositionClosed ≡ true
round549GenericR290RemainderDecompositionClosedIsTrue = refl

round549FiniteDiagonalDecompositionClosedIsTrue :
  round549FiniteDiagonalDecompositionClosed ≡ true
round549FiniteDiagonalDecompositionClosedIsTrue = refl

round549SelfPairPositivityBorrowedFromOffDiagonalCarrierIsFalse :
  round549SelfPairPositivityBorrowedFromOffDiagonalCarrier ≡ false
round549SelfPairPositivityBorrowedFromOffDiagonalCarrierIsFalse = refl

round549ClayPromotionIsFalse : round549ClayPromotion ≡ false
round549ClayPromotionIsFalse = refl
