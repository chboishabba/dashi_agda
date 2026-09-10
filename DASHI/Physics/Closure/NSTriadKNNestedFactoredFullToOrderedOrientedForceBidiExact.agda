module DASHI.Physics.Closure.NSTriadKNNestedFactoredFullToOrderedOrientedForceBidiExact where

------------------------------------------------------------------------
-- NESTED FACTORED FULL -> DIAGONAL + FOUR ORDERED ORIENTED FORCE
--
-- Existing exact owners give, on one complete physical output fibre:
--
--   R547: FactoredFull = Diagonal + 2 * LiteralWeightedRemainder
--   R497: LiteralWeightedRemainder = 4 * DirectFibreCompanion
--   OrientedForce: DirectFibreCompanion = 1/2 * OrderedOffDiagonal(H)
--
-- where
--
--   H(alpha,beta) = w(alpha,beta) Re <G_alpha,D_beta>.
--
-- Therefore
--
--   FactoredFull = Diagonal + 4 * OrderedOffDiagonal(H).
--
-- This is only exact finite algebra / same-object composition.  It introduces
-- no norm, absolute value, estimate, time integration, or division-based
-- cancellation of a theorem hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNLiteralR396OrderedOffDiagonalRemainderRound540Exact as R540
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNDirectCompanionOrientedForceTransposeCompletionBidiExact as Oriented

F : C3.RealField _
F = Rational.rationalRealField

module OrderedNormalForm
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Normal = R547.NormalForm physicalSystem S
  module O = R540.LiteralOrdered physicalSystem S
  module Direct = R497.DirectFibre physicalSystem S
  module H = Oriented.OrientedForce physicalSystem S

  system = Field30.finiteSystem physicalSystem

  factoredFullIsDiagonalPlusFourOrderedForce :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    (positive : O.E.PairRatePositiveOn items) →
    Normal.factoredFull output items
    ≡ R547.R543.diagonalSum Normal.R.pairScalar items
      + R299.four * R539.orderedOffDiagonalSum H.orientedForceCross items
  factoredFullIsDiagonalPlusFourOrderedForce output positive =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      direct = Direct.directFibreCompanion items positive
      ordered = R539.orderedOffDiagonalSum H.orientedForceCross items
      remainderToDirect = Direct.allRemainderIsFourCompanion items positive
      directToOrdered = H.directFibreIsHalfOrderedOrientedForce items positive
    in
    trans
      (Normal.factoredFullIsDiagonalPlusTwoLiteralRemainder output positive)
      (trans
        (cong
          (R547.R543.diagonalSum Normal.R.pairScalar items +_)
          (cong (R547.R539.two *_)
            remainderToDirect))
        (trans
          (cong
            (R547.R543.diagonalSum Normal.R.pairScalar items +_)
            (cong (λ x → R547.R539.two * (R299.four * x))
              directToOrdered))
          (cong
            (R547.R543.diagonalSum Normal.R.pairScalar items +_)
            (solve (ordered ∷ [])))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

nestedFullOrderedOrientedForceNormalFormClosed : Bool
nestedFullOrderedOrientedForceNormalFormClosed = true

amplitudeHalfIndependentAfterOrderedCompletion : Bool
amplitudeHalfIndependentAfterOrderedCompletion = false

normIntroducedInOrderedNormalForm : Bool
normIntroducedInOrderedNormalForm = false

absoluteValueIntroducedInOrderedNormalForm : Bool
absoluteValueIntroducedInOrderedNormalForm = false

cutoffUniformOrderedForceBudgetClosed : Bool
cutoffUniformOrderedForceBudgetClosed = false

clayPromotion : Bool
clayPromotion = false
