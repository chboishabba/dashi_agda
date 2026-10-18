{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantContinuationCompilerExact where

------------------------------------------------------------------------
-- SELECTED CMP119 WEYL RESPONSE + BOOST-INVARIANT ISOTROPIC LORENTZIAN
-- STRESS -> VACUUM CONTINUATION WELD -> NEGATIVE ACTIVE STRESS.
--
-- Compared with CMP119CosmologyVacuumContinuationCompilerExact, this module
-- removes p = -rho as a primitive input.  Instead it requires:
--
--   1. an isotropic Lorentzian stress on the selected continued state;
--   2. invariance of that stress under the explicit nontrivial rational boost
--      from CMP119CosmologyBoostInvariantVacuumExact;
--   3. same-object trace continuation from the selected finite Euclidean
--      R144 Weyl response.
--
-- The boost theorem derives p = -rho.  The older vacuum continuation compiler
-- then closes the trace/active-stress algebra.
--
-- Still open physically: proving the reconstructed selected CMP119 vacuum
-- state actually supplies this boost invariance and same-object continuation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantVacuumExact as Boost
import DASHI.Physics.Foundations.CMP119CosmologyVacuumContinuationCompilerExact as Continue

record SelectedBoostInvariantContinuationWeld : Set where
  field
    selectedFiniteEuclideanWeylResponse : ℚ

    lorentzianIsotropicStress :
      Vacuum.IsotropicLorentzianStress

    selectedBoostOffDiagonalInvariant :
      Boost.boosted01 lorentzianIsotropicStress ≡ 0ℚ

    sameObjectTraceContinuation :
      Vacuum.trace lorentzianIsotropicStress
      ≡ selectedFiniteEuclideanWeylResponse

open SelectedBoostInvariantContinuationWeld public

boostInvariantStress :
  SelectedBoostInvariantContinuationWeld →
  Boost.SelectedBoostInvariantIsotropicStress
boostInvariantStress weld = record
  { Boost.SelectedBoostInvariantIsotropicStress.stress =
      lorentzianIsotropicStress weld
  ; Boost.SelectedBoostInvariantIsotropicStress.selectedBoostOffDiagonalInvariant =
      selectedBoostOffDiagonalInvariant weld
  }

derivedVacuumStress :
  SelectedBoostInvariantContinuationWeld →
  Vacuum.VacuumLikeLorentzianStress
derivedVacuumStress weld =
  Boost.asVacuumLikeLorentzianStress
    (boostInvariantStress weld)

asVacuumContinuationWeld :
  SelectedBoostInvariantContinuationWeld →
  Continue.SelectedVacuumContinuationWeld
asVacuumContinuationWeld weld = record
  { Continue.SelectedVacuumContinuationWeld.selectedFiniteEuclideanWeylResponse =
      selectedFiniteEuclideanWeylResponse weld
  ; Continue.SelectedVacuumContinuationWeld.lorentzianVacuumStress =
      derivedVacuumStress weld
  ; Continue.SelectedVacuumContinuationWeld.sameObjectTraceContinuation =
      sameObjectTraceContinuation weld
  }

boostInvariantContinuationForcesVacuumEquationOfState :
  ∀ weld →
  Vacuum.pressure (lorentzianIsotropicStress weld)
  ≡ - Vacuum.rho (lorentzianIsotropicStress weld)
boostInvariantContinuationForcesVacuumEquationOfState weld =
  Boost.boostInvarianceForcesVacuumEquationOfState
    (boostInvariantStress weld)

continuedBoostInvariantTraceIsTwiceActive :
  ∀ weld →
  Vacuum.trace (lorentzianIsotropicStress weld)
  ≡
  Vacuum.activeStress (lorentzianIsotropicStress weld)
  + Vacuum.activeStress (lorentzianIsotropicStress weld)
continuedBoostInvariantTraceIsTwiceActive weld =
  Boost.boostInvariantTraceIsTwiceActive
    (boostInvariantStress weld)

continuedBoostInvariantPositiveRhoClosesNegativeActive :
  ∀ weld →
  0ℚ < Vacuum.rho (lorentzianIsotropicStress weld) →
  Vacuum.activeStress (lorentzianIsotropicStress weld) < 0ℚ
continuedBoostInvariantPositiveRhoClosesNegativeActive weld positiveRho =
  Continue.continuedVacuumPositiveRhoClosesNegativeActive
    (asVacuumContinuationWeld weld)
    positiveRho

continuedBoostInvariantPositiveRhoClosesNegativeSelectedTrace :
  ∀ weld →
  0ℚ < Vacuum.rho (lorentzianIsotropicStress weld) →
  selectedFiniteEuclideanWeylResponse weld < 0ℚ
continuedBoostInvariantPositiveRhoClosesNegativeSelectedTrace weld positiveRho =
  Continue.continuedVacuumPositiveRhoClosesNegativeTrace
    (asVacuumContinuationWeld weld)
    positiveRho

------------------------------------------------------------------------
-- FRONTIER FLAGS
------------------------------------------------------------------------

vacuumEquationOfStateNoLongerPrimitiveOnBoostBranch : Bool
vacuumEquationOfStateNoLongerPrimitiveOnBoostBranch = true

selectedCMP119BoostInvariantContinuationStillOpen : Bool
selectedCMP119BoostInvariantContinuationStillOpen = true

genericStateStillNeedsIndependentT00Control : Bool
genericStateStillNeedsIndependentT00Control = true
