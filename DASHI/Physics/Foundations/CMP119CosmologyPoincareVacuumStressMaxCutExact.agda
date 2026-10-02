{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPoincareVacuumStressMaxCutExact where

------------------------------------------------------------------------
-- CMP119 COSMOLOGY / ANTIGRAVITY MAX-CUT:
--
--   same literal continuum stress pairing
--      + selected reconstructed Poincare-vacuum package
--      + ONE stress-covariance equality for the explicit rational boost
--      + same-object Euclidean/Lorentzian trace continuation
--
--   ==> boost-invariant isotropic stress
--   ==> p = -rho
--   ==> Theta = 2 Active
--   ==> positive rho -> negative active stress.
--
-- Upstream status:
-- * CMP119CosmologyContinuumWeylStressPairingExact already identifies the
--   recovered generated-action continuum metric response with the SAME literal
--   continuum stress tensor pairing.
-- * Sprint128/Sprint130 record the reconstructed Poincare-covariance and
--   limiting-vacuum consumer package.
--
-- What those receipts do NOT yet supply is the operator-level statement that
-- the selected CMP119 stress expectation transforms as a rank-two Lorentz
-- tensor on that SAME reconstructed vacuum.  This module makes that exact
-- missing theorem visible rather than reading receipt-level Poincare
-- covariance as stress covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.YMSprint128SymmetryAndGroupClosure as Sprint128
import DASHI.Physics.Closure.YMSprint130PoincareSpectrumWightmanClosure as Sprint130
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantVacuumExact as Boost
import DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantContinuationCompilerExact as Continue
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum

------------------------------------------------------------------------
-- The selected boost expectation carrier.
--
-- boostedStress01Expectation is the expectation value obtained by acting with
-- the selected reconstructed boost on the SAME stress operator/state pair.
--
-- stressCovarianceIdentifiesBoosted01 is the real operator-covariance seam:
-- it identifies that expectation with the explicit tensor transformation
-- computed in CMP119CosmologyBoostInvariantVacuumExact.
--
-- vacuumInvarianceReturnsUnboosted01 uses the SAME reconstructed vacuum and
-- isotropy of the original stress, whose unboosted 01 component is zero.
------------------------------------------------------------------------

record SelectedPoincareVacuumStressBoostWeld : Set where
  field
    lorentzianIsotropicStress :
      Vacuum.IsotropicLorentzianStress

    boostedStress01Expectation :
      ℚ

    stressCovarianceIdentifiesBoosted01 :
      boostedStress01Expectation
      ≡
      Boost.boosted01 lorentzianIsotropicStress

    vacuumInvarianceReturnsUnboosted01 :
      boostedStress01Expectation ≡ 0ℚ

open SelectedPoincareVacuumStressBoostWeld public

selectedStressBoosted01IsZero :
  ∀ weld →
  Boost.boosted01 (lorentzianIsotropicStress weld) ≡ 0ℚ
selectedStressBoosted01IsZero weld =
  trans
    (sym (stressCovarianceIdentifiesBoosted01 weld))
    (vacuumInvarianceReturnsUnboosted01 weld)

asBoostInvariantIsotropicStress :
  SelectedPoincareVacuumStressBoostWeld →
  Boost.SelectedBoostInvariantIsotropicStress
asBoostInvariantIsotropicStress weld = record
  { Boost.SelectedBoostInvariantIsotropicStress.stress =
      lorentzianIsotropicStress weld
  ; Boost.SelectedBoostInvariantIsotropicStress.selectedBoostOffDiagonalInvariant =
      selectedStressBoosted01IsZero weld
  }

selectedPoincareVacuumStressForcesVacuumEquationOfState :
  ∀ weld →
  Vacuum.pressure (lorentzianIsotropicStress weld)
  ≡ - Vacuum.rho (lorentzianIsotropicStress weld)
selectedPoincareVacuumStressForcesVacuumEquationOfState weld =
  Boost.boostInvarianceForcesVacuumEquationOfState
    (asBoostInvariantIsotropicStress weld)

------------------------------------------------------------------------
-- Full max-cut input.
--
-- selectedEuclideanWeylResponse is the already-computed/continued scalar
-- response of the SAME selected continuum stress pairing.  The only
-- continuation law required here is equality with the Lorentzian trace.
------------------------------------------------------------------------

record SelectedCMP119CosmologyMaxCut : Set where
  field
    selectedEuclideanWeylResponse : ℚ

    boostWeld :
      SelectedPoincareVacuumStressBoostWeld

    sameObjectTraceContinuation :
      Vacuum.trace
        (lorentzianIsotropicStress boostWeld)
      ≡
      selectedEuclideanWeylResponse

open SelectedCMP119CosmologyMaxCut public

asBoostInvariantContinuationWeld :
  SelectedCMP119CosmologyMaxCut →
  Continue.SelectedBoostInvariantContinuationWeld
asBoostInvariantContinuationWeld cut = record
  { Continue.SelectedBoostInvariantContinuationWeld.selectedFiniteEuclideanWeylResponse =
      selectedEuclideanWeylResponse cut
  ; Continue.SelectedBoostInvariantContinuationWeld.lorentzianIsotropicStress =
      lorentzianIsotropicStress (boostWeld cut)
  ; Continue.SelectedBoostInvariantContinuationWeld.selectedBoostOffDiagonalInvariant =
      selectedStressBoosted01IsZero (boostWeld cut)
  ; Continue.SelectedBoostInvariantContinuationWeld.sameObjectTraceContinuation =
      sameObjectTraceContinuation cut
  }

maxCutForcesVacuumEquationOfState :
  ∀ cut →
  Vacuum.pressure
    (lorentzianIsotropicStress (boostWeld cut))
  ≡
  - Vacuum.rho
    (lorentzianIsotropicStress (boostWeld cut))
maxCutForcesVacuumEquationOfState cut =
  Continue.boostInvariantContinuationForcesVacuumEquationOfState
    (asBoostInvariantContinuationWeld cut)

maxCutTraceIsTwiceActive :
  ∀ cut →
  Vacuum.trace
    (lorentzianIsotropicStress (boostWeld cut))
  ≡
  Vacuum.activeStress
    (lorentzianIsotropicStress (boostWeld cut))
  +
  Vacuum.activeStress
    (lorentzianIsotropicStress (boostWeld cut))
maxCutTraceIsTwiceActive cut =
  Continue.continuedBoostInvariantTraceIsTwiceActive
    (asBoostInvariantContinuationWeld cut)

maxCutPositiveRhoGivesNegativeActive :
  ∀ cut →
  0ℚ <
    Vacuum.rho
      (lorentzianIsotropicStress (boostWeld cut)) →
  Vacuum.activeStress
    (lorentzianIsotropicStress (boostWeld cut))
  < 0ℚ
maxCutPositiveRhoGivesNegativeActive cut positiveRho =
  Continue.continuedBoostInvariantPositiveRhoClosesNegativeActive
    (asBoostInvariantContinuationWeld cut)
    positiveRho

maxCutPositiveRhoGivesNegativeSelectedTrace :
  ∀ cut →
  0ℚ <
    Vacuum.rho
      (lorentzianIsotropicStress (boostWeld cut)) →
  selectedEuclideanWeylResponse cut < 0ℚ
maxCutPositiveRhoGivesNegativeSelectedTrace cut positiveRho =
  Continue.continuedBoostInvariantPositiveRhoClosesNegativeSelectedTrace
    (asBoostInvariantContinuationWeld cut)
    positiveRho

------------------------------------------------------------------------
-- Upstream receipt facts consumed by this max-cut.
--
-- These are intentionally only receipt facts.  They do not inhabit
-- stressCovarianceIdentifiesBoosted01.
------------------------------------------------------------------------

sprint128PoincareCovarianceConsumerClosed :
  Sprint128.dashiNativePoincareCovarianceClosedHere ≡ true
sprint128PoincareCovarianceConsumerClosed =
  Sprint128.dashiNativePoincareCovarianceClosedHereIsTrue

sprint130PoincareConsumerClosed :
  Sprint130.wightmanPoincareCovarianceConsumerClosedHere ≡ true
sprint130PoincareConsumerClosed =
  Sprint130.wightmanPoincareCovarianceConsumerClosedHereIsTrue

sprint130VacuumIdentityConsumerClosed :
  Sprint130.rp4VacuumIdentityConsumerClosedHere ≡ true
sprint130VacuumIdentityConsumerClosed =
  Sprint130.rp4VacuumIdentityConsumerClosedHereIsTrue

------------------------------------------------------------------------
-- HONEST FRONTIER FLAGS
------------------------------------------------------------------------

poincareReceiptAloneImpliesSelectedStressBoostCovariance : Bool
poincareReceiptAloneImpliesSelectedStressBoostCovariance = false

literalContinuumStressPairingAlreadyAvailable : Bool
literalContinuumStressPairingAlreadyAvailable = true

singleSelectedBoostCovarianceSufficesForVacuumEquationOfState : Bool
singleSelectedBoostCovarianceSufficesForVacuumEquationOfState = true

sameObjectTraceContinuationStillRequired : Bool
sameObjectTraceContinuationStillRequired = true

selectedStressBoostCovarianceStillRequired : Bool
selectedStressBoostCovarianceStillRequired = true
