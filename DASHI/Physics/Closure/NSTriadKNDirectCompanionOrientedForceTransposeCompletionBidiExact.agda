module DASHI.Physics.Closure.NSTriadKNDirectCompanionOrientedForceTransposeCompletionBidiExact where

------------------------------------------------------------------------
-- R496/R497 DIRECT COMPANION -> ONE ORIENTED FORCE KERNEL
--
-- Define the oriented signed kernel
--
--   H(alpha,beta)
--     = w(alpha,beta) * Re < G_alpha , D_beta >.
--
-- R496's unordered direct companion pair is
--
--   C(alpha,beta)
--     = 1/2 * w(alpha,beta)
--         * (Re<G_alpha,D_beta> + Re<D_alpha,G_beta>).
--
-- The second cross is exactly the transpose H(beta,alpha), because the pair
-- resolvent is symmetric and the real Hermitian cross is symmetric.  Hence
--
--   C(alpha,beta) = 1/2 * (H(alpha,beta) + H(beta,alpha)).
--
-- The generic finite transpose-completion compiler then gives, on the exact
-- R497 unordered position-pair carrier,
--
--   DirectFibreCompanion(items)
--     = 1/2 * OrderedOffDiagonalSum(H,items).
--
-- Thus the historical "amplitude half" is not an independent analytic channel
-- after complete pair aggregation: it is the transpose completion of the force
-- half.  No norm, absolute value, Cauchy/Young/Schur estimate or integration is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNSymmetrizedHalfUnorderedOrderedExact as HalfOrdered

F : C3.RealField _
F = Rational.rationalRealField

module OrientedForce
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Swap = R538.PairSwap physicalSystem S
  module Direct = R496.DirectPair physicalSystem S
  module Fibre = R497.DirectFibre physicalSystem S
  module Local = R396.LocalEnumerate physicalSystem S

  orientedForceCross :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  orientedForceCross alpha beta =
    let Q = Swap.Q alpha beta in
    Swap.pairResolvent alpha beta
      * R179.realHermitianCross (R291.forcingA Q) (R291.cellB Q)

  transposeForceCrossMeaning :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    orientedForceCross beta alpha
    ≡ Swap.pairResolvent alpha beta
      * R179.realHermitianCross
          (R291.cellA (Swap.Q alpha beta))
          (R291.forcingB (Swap.Q alpha beta))
  transposeForceCrossMeaning alpha beta =
    cong₂ _*_
      (sym (Swap.pairResolventSymmetric alpha beta))
      (R287.realHermitianCrossSymmetric
        (R291.forcingB (Swap.Q alpha beta))
        (R291.cellA (Swap.Q alpha beta)))

  directPairIsSymmetrizedOrientedForce :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (positive : Positive (R291.pairRate (Swap.Q alpha beta))) →
    Direct.directResolventPairCompanion alpha beta positive
    ≡ HalfOrdered.symmetrizedHalf orientedForceCross alpha beta
  directPairIsSymmetrizedOrientedForce alpha beta positive
      rewrite transposeForceCrossMeaning alpha beta =
    let
      Q = Swap.Q alpha beta
      w = Swap.pairResolvent alpha beta
      left = R179.realHermitianCross (R291.forcingA Q) (R291.cellB Q)
      right = R179.realHermitianCross (R291.cellA Q) (R291.forcingB Q)
    in
    solve (w ∷ left ∷ right ∷ [])

  headCompanionIsSymmetrizedRow :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (R291.pairRate (Swap.Q alpha beta))) →
    Fibre.headCompanionSum alpha rest positive
    ≡ R539.rowSum
        (HalfOrdered.symmetrizedHalf orientedForceCross)
        alpha rest
  headCompanionIsSymmetrizedRow alpha [] positive = refl
  headCompanionIsSymmetrizedRow alpha (beta ∷ rest) positive =
    cong₂ _+_
      (directPairIsSymmetrizedOrientedForce
        alpha beta (positive beta R396.here))
      (headCompanionIsSymmetrizedRow alpha rest
        (λ gamma member → positive gamma (R396.there member)))

  directFibreIsUnorderedSymmetrizedForce :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    Fibre.directFibreCompanion items positive
    ≡ R539.unorderedPairSum
        (HalfOrdered.symmetrizedHalf orientedForceCross)
        items
  directFibreIsUnorderedSymmetrizedForce [] Local.positiveNil = refl
  directFibreIsUnorderedSymmetrizedForce (alpha ∷ rest)
      (Local.positiveCons headPositive tailPositive) =
    cong₂ _+_
      (headCompanionIsSymmetrizedRow alpha rest headPositive)
      (directFibreIsUnorderedSymmetrizedForce rest tailPositive)

  directFibreIsHalfOrderedOrientedForce :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    Fibre.directFibreCompanion items positive
    ≡ HalfOrdered.half *
        R539.orderedOffDiagonalSum orientedForceCross items
  directFibreIsHalfOrderedOrientedForce items positive =
    trans
      (directFibreIsUnorderedSymmetrizedForce items positive)
      (HalfOrdered.unorderedSymmetrizedHalfIsHalfOrderedOffDiagonal
        orientedForceCross items)

------------------------------------------------------------------------
-- Status / no-promotion boundary.
------------------------------------------------------------------------

directPairSecondChannelIsTransposeOfFirst : Bool
directPairSecondChannelIsTransposeOfFirst = true

directFibreAmplitudeHalfIndependentAnalyticLeaf : Bool
directFibreAmplitudeHalfIndependentAnalyticLeaf = false

directFibreOneOrientedOrderedKernelExact : Bool
directFibreOneOrientedOrderedKernelExact = true

directFibreOneOrientedKernelNormedBeforeTransposeCompletion : Bool
directFibreOneOrientedKernelNormedBeforeTransposeCompletion = false

directFibreOneOrientedKernelAbsoluteValuedBeforeTransposeCompletion : Bool
directFibreOneOrientedKernelAbsoluteValuedBeforeTransposeCompletion = false

cutoffUniformOrderedOrientedForceBudgetClosed : Bool
cutoffUniformOrderedOrientedForceBudgetClosed = false

clayPromotion : Bool
clayPromotion = false

directFibreOneOrientedOrderedKernelExactIsTrue :
  directFibreOneOrientedOrderedKernelExact ≡ true
directFibreOneOrientedOrderedKernelExactIsTrue = refl

directFibreAmplitudeHalfIndependentAnalyticLeafIsFalse :
  directFibreAmplitudeHalfIndependentAnalyticLeaf ≡ false
directFibreAmplitudeHalfIndependentAnalyticLeafIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
