module DASHI.Physics.Chemistry.AmmoniaMonster3BPhaseQuotientNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Algebra.Trit using (zer; pos)

import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Monster3B
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model

------------------------------------------------------------------------
-- PHASE QUOTIENT IS EXACT BUT LOSSY
--
-- Every basis state below lives in the zeta model sector, hence has the same
-- central C3 phase.  We exhibit separating pairs for BOTH fine coordinates:
--   * F3^6 / Heisenberg weight position;
--   * Fin 90 multiplicity.
-- Therefore no function of the three-valued phase coordinate alone can recover
-- the fine Monster-zeta basis state, its weight, or its multiplicity.
------------------------------------------------------------------------

origin : H.X6
origin = H.x6 zer zer zer zer zer zer

shifted0 : H.X6
shifted0 = H.x6 pos zer zer zer zer zer

multiplicity0 : Fin 90
multiplicity0 = zero

multiplicity1 : Fin 90
multiplicity1 = suc zero

weightState0 weightState1 : Model.ZetaModelBasis
weightState0 = Model.zetaBasis origin multiplicity0
weightState1 = Model.zetaBasis shifted0 multiplicity0

multiplicityState0 multiplicityState1 : Model.ZetaModelBasis
multiplicityState0 = Model.zetaBasis origin multiplicity0
multiplicityState1 = Model.zetaBasis origin multiplicity1

modelPhase : Model.ZetaModelBasis → Monster3B.CentralPhase3
modelPhase _ = Monster3B.phaseZeta

samePhaseWeightPair : modelPhase weightState0 ≡ modelPhase weightState1
samePhaseWeightPair = refl

samePhaseMultiplicityPair :
  modelPhase multiplicityState0 ≡ modelPhase multiplicityState1
samePhaseMultiplicityPair = refl

zerNotPos : zer ≡ pos → ⊥
zerNotPos ()

finZeroNotOne : multiplicity0 ≡ multiplicity1 → ⊥
finZeroNotOne ()

weightStatesDistinct : weightState0 ≡ weightState1 → ⊥
weightStatesDistinct eq =
  zerNotPos
    (cong H.x0
      (cong Model.weightPosition eq))

multiplicityStatesDistinct : multiplicityState0 ≡ multiplicityState1 → ⊥
multiplicityStatesDistinct eq =
  finZeroNotOne (cong Model.multiplicityCoordinate eq)

------------------------------------------------------------------------
-- Exact non-factorability surfaces.
------------------------------------------------------------------------

record PhaseRecoversModelBasis : Set where
  constructor phaseRecoversModelBasis
  field
    recover : Monster3B.CentralPhase3 → Model.ZetaModelBasis
    recovers : (state : Model.ZetaModelBasis) → recover (modelPhase state) ≡ state

open PhaseRecoversModelBasis public

phaseCannotRecoverModelBasis : PhaseRecoversModelBasis → ⊥
phaseCannotRecoverModelBasis r =
  weightStatesDistinct
    (trans
      (sym (recovers r weightState0))
      (recovers r weightState1))

record PhaseRecoversWeightPosition : Set where
  constructor phaseRecoversWeightPosition
  field
    recoverWeight : Monster3B.CentralPhase3 → H.X6
    recoversWeight :
      (state : Model.ZetaModelBasis) →
      recoverWeight (modelPhase state) ≡ Model.weightPosition state

open PhaseRecoversWeightPosition public

phaseCannotRecoverWeightPosition : PhaseRecoversWeightPosition → ⊥
phaseCannotRecoverWeightPosition r =
  zerNotPos
    (cong H.x0
      (trans
        (sym (recoversWeight r weightState0))
        (recoversWeight r weightState1)))

record PhaseRecoversMultiplicityCoordinate : Set where
  constructor phaseRecoversMultiplicityCoordinate
  field
    recoverMultiplicity : Monster3B.CentralPhase3 → Fin 90
    recoversMultiplicity :
      (state : Model.ZetaModelBasis) →
      recoverMultiplicity (modelPhase state) ≡ Model.multiplicityCoordinate state

open PhaseRecoversMultiplicityCoordinate public

phaseCannotRecoverMultiplicityCoordinate : PhaseRecoversMultiplicityCoordinate → ⊥
phaseCannotRecoverMultiplicityCoordinate r =
  finZeroNotOne
    (trans
      (sym (recoversMultiplicity r multiplicityState0))
      (recoversMultiplicity r multiplicityState1))

------------------------------------------------------------------------
-- What phase-only consumers CAN do: every observable that is literally a
-- function of the central phase transports losslessly across the quotient.
------------------------------------------------------------------------

transportPhaseObservable :
  ∀ {Observation : Set} →
  (Monster3B.CentralPhase3 → Observation) →
  Model.ZetaModelBasis → Observation
transportPhaseObservable observe state = observe (modelPhase state)

record PhaseQuotientNonFactorabilityBoundary : Set where
  constructor phaseQuotientNonFactorabilityBoundary
  field
    sharedZetaPhaseSeparatingPairPaid : Bool
    sharedZetaPhaseSeparatingPairPaidIsTrue :
      sharedZetaPhaseSeparatingPairPaid ≡ true
    phaseQuotientFineStateNonfactorabilityPaid : Bool
    phaseQuotientFineStateNonfactorabilityPaidIsTrue :
      phaseQuotientFineStateNonfactorabilityPaid ≡ true
    phaseQuotientWeightNonfactorabilityPaid : Bool
    phaseQuotientWeightNonfactorabilityPaidIsTrue :
      phaseQuotientWeightNonfactorabilityPaid ≡ true
    phaseQuotientMultiplicityNonfactorabilityPaid : Bool
    phaseQuotientMultiplicityNonfactorabilityPaidIsTrue :
      phaseQuotientMultiplicityNonfactorabilityPaid ≡ true
    phaseOnlyObservablesTransportable : Bool
    phaseOnlyObservablesTransportableIsTrue :
      phaseOnlyObservablesTransportable ≡ true
    phaseCoordinateIsSufficientForLiteralMonsterState : Bool
    phaseCoordinateIsSufficientForLiteralMonsterStateIsFalse :
      phaseCoordinateIsSufficientForLiteralMonsterState ≡ false
    requiredRefinement : String

open PhaseQuotientNonFactorabilityBoundary public

canonicalPhaseQuotientNonFactorabilityBoundary : PhaseQuotientNonFactorabilityBoundary
canonicalPhaseQuotientNonFactorabilityBoundary =
  phaseQuotientNonFactorabilityBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "refine the exact C3 phase quotient by the F3^6/Base369 weight coordinate and Fin 90 multiplicity coordinate, then prove the desired action equivariance and same-object physical identification"
