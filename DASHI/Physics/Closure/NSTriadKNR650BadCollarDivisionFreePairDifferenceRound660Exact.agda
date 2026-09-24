{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarDivisionFreePairDifferenceRound660Exact where

------------------------------------------------------------------------
-- ROUND660 / FULL-FIBRE DIVISION-FREE COMMUTATOR -> PAIR DIFFERENCE
--
-- R658 places every active bad-collar output on the ordinary unweighted R230
-- fixed-output commutator carrier.  Do NOT splice that whole fibre directly
-- into the older R207/P3 comparable-only norm-mass compiler.
--
-- The full physical output fibre already has the correct same-object algebra:
--
--   W(M,C) = W(M,T) - W(M,D)
--
-- and
--
--   n W(M,D) + (sum_i r_i) W(M,M)
--     = - PairDiffWork.
--
-- Eliminating W(M,D), without dividing by n, gives exactly
--
--   n W(M,C)
--     = n W(M,T)
--       + (sum_i r_i) W(M,M)
--       + PairDiffWork.
--
-- This theorem is on the SAME physicalOutputFiber used by R658.  Therefore an
-- active bad-collar output inherits this division-free signed normal form with
-- no comparable-class restriction and no cardinality denominator.
--
-- The remaining quantitative theorem is still open: one must pay the endpoint
-- / tangent term together with the signed rate-weighted PairDiffWork (or prove
-- an equivalent direct estimate).  No sign of PairDiffWork is manufactured.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656
import DASHI.Physics.Closure.NSTriadKNR650BadCollarFixedOutputCarrierRound658Exact as R658

F : C3.RealField _
F = Rational.rationalRealField

fixedOutputDivisionFreeCommutatorPairDifference :
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = Work.fixedOutputMixedProduct S velocity cutoff output
    tangent = Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    commutator = Work.fixedOutputCommutator S velocity forcing cutoff output
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)
  in
  n * Work.coherentWork mixed commutator
  ≡
  n * Work.coherentWork mixed tangent
    + Pair.rateSum rate items * Work.coherentWork mixed mixed
    + Pair.pairDifferenceWorkSum rate work items
fixedOutputDivisionFreeCommutatorPairDifference
    rho S velocity forcing cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = Work.fixedOutputMixedProduct S velocity cutoff output
    tangent = Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    decay = Work.fixedOutputVariableDecay rho S velocity cutoff output
    commutator = Work.fixedOutputCommutator S velocity forcing cutoff output
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)

    tangentWork = Work.coherentWork mixed tangent
    decayWork = Work.coherentWork mixed decay
    commutatorWork = Work.coherentWork mixed commutator
    selfWork = Work.coherentWork mixed mixed
    rateTotal = Pair.rateSum rate items
    pairDiff = Pair.pairDifferenceWorkSum rate work items

    commutatorSplit :
      commutatorWork ≡ tangentWork - decayWork
    commutatorSplit =
      Work.fixedOutputCommutatorWorkIsTangentMinusDecay
        rho S velocity forcing cutoff output

    covarianceCentering :
      n * decayWork + rateTotal * selfWork
      ≡ 0ℚ - pairDiff
    covarianceCentering =
      Pair.fixedOutputCovariancePairDifference
        rho S velocity cutoff output

    scaledCommutator :
      n * commutatorWork
      ≡ n * (tangentWork - decayWork)
    scaledCommutator =
      cong (n *_) commutatorSplit

    targetFromCentering :
      n * (tangentWork - decayWork)
      ≡ n * tangentWork + rateTotal * selfWork + pairDiff
    targetFromCentering =
      let
        shifted =
          cong
            (λ value →
              n * tangentWork - value + rateTotal * selfWork)
            covarianceCentering
      in
      trans
        (solve
          ( n ∷ tangentWork ∷ decayWork
          ∷ rateTotal ∷ selfWork ∷ pairDiff ∷ [] ))
        (trans
          shifted
          (solve
            ( n ∷ tangentWork
            ∷ rateTotal ∷ selfWork ∷ pairDiff ∷ [] )))
  in
  trans scaledCommutator targetFromCentering

activeBadCollarDivisionFreeCommutatorPairDifference :
  (K : Nat) →
  (output : Z3.FourierMode) →
  R656.badCollarPacket K output ≡ true →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = Work.fixedOutputMixedProduct S velocity cutoff output
    tangent = Work.fixedOutputDampedTangent rho S velocity forcing cutoff output
    commutator = Work.fixedOutputCommutator S velocity forcing cutoff output
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)
  in
  n * Work.coherentWork mixed commutator
  ≡
  n * Work.coherentWork mixed tangent
    + Pair.rateSum rate items * Work.coherentWork mixed mixed
    + Pair.pairDifferenceWorkSum rate work items
activeBadCollarDivisionFreeCommutatorPairDifference
    K output active rho S velocity forcing cutoff =
  fixedOutputDivisionFreeCommutatorPairDifference
    rho S velocity forcing cutoff output

------------------------------------------------------------------------
-- Status / carrier firewall.
------------------------------------------------------------------------

round660FullPhysicalFibreDivisionFreePairDifferenceClosed : Bool
round660FullPhysicalFibreDivisionFreePairDifferenceClosed = true

round660ActiveBadCollarInheritsFullFibrePairDifferenceNormalForm : Bool
round660ActiveBadCollarInheritsFullFibrePairDifferenceNormalForm = true

-- R207/P3 is a comparable-only localized partner carrier.  It is a donor for
-- the comparable class, not definitionally the full R658 physical output fibre.
round660WholeBadCollarFibreIsR207ComparableCarrier : Bool
round660WholeBadCollarFibreIsR207ComparableCarrier = false

round660SignedFullFibrePairDifferencePaymentClosed : Bool
round660SignedFullFibrePairDifferencePaymentClosed = false

round660EndpointTangentPaymentClosed : Bool
round660EndpointTangentPaymentClosed = false

round660IntroducesNewClayLeaf : Bool
round660IntroducesNewClayLeaf = false

round660C2Closed : Bool
round660C2Closed = false

round660ClayPromotion : Bool
round660ClayPromotion = false

round660FullPhysicalFibreDivisionFreePairDifferenceClosedIsTrue :
  round660FullPhysicalFibreDivisionFreePairDifferenceClosed ≡ true
round660FullPhysicalFibreDivisionFreePairDifferenceClosedIsTrue = refl

round660ActiveBadCollarInheritsFullFibrePairDifferenceNormalFormIsTrue :
  round660ActiveBadCollarInheritsFullFibrePairDifferenceNormalForm ≡ true
round660ActiveBadCollarInheritsFullFibrePairDifferenceNormalFormIsTrue = refl

round660WholeBadCollarFibreIsR207ComparableCarrierIsFalse :
  round660WholeBadCollarFibreIsR207ComparableCarrier ≡ false
round660WholeBadCollarFibreIsR207ComparableCarrierIsFalse = refl

round660SignedFullFibrePairDifferencePaymentClosedIsFalse :
  round660SignedFullFibrePairDifferencePaymentClosed ≡ false
round660SignedFullFibrePairDifferencePaymentClosedIsFalse = refl

round660EndpointTangentPaymentClosedIsFalse :
  round660EndpointTangentPaymentClosed ≡ false
round660EndpointTangentPaymentClosedIsFalse = refl

round660IntroducesNewClayLeafIsFalse :
  round660IntroducesNewClayLeaf ≡ false
round660IntroducesNewClayLeafIsFalse = refl

round660C2ClosedIsFalse :
  round660C2Closed ≡ false
round660C2ClosedIsFalse = refl

round660ClayPromotionIsFalse :
  round660ClayPromotion ≡ false
round660ClayPromotionIsFalse = refl
