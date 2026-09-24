{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedSelectionRound621Exact where

------------------------------------------------------------------------
-- ROUND621 / CANONICAL ORBIT-RESOLVED SELECTION FROM EXECUTABLE MODE EQUALITY
--
-- R619/R620 are total once a proof-relevant fixed/nonfixed swap-orbit choice
-- is supplied for tau and its p/q energy legs.  On the literal Z^3 carrier
-- those choices are not analytic data: R617 identifies the fixed loci with
--
--   p = q,    k = -q,    k = -p,
--
-- and PhysicalOutputFiber.modeEqual is a reflected executable equality test.
--
-- This owner therefore constructs all three SwapOrbitCase values canonically,
-- and packages the R619 ThreeLegOrbitResolvedSelection from one actual
-- own-fibre membership witness.
--
-- No norm, estimate, cancellation, shell decomposition, or Clay promotion is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNThreeLegResidualNonfixedGeometryRound617Exact as R617
import DASHI.Physics.Closure.NSTriadKNExternalSelfOrbitMultiplicityRound618Exact as R618
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeOrbitResolvedRound619Exact as R619

modeDifferentFromFalse :
  ∀ {left right : Z3.FourierMode} →
  Output.modeEqual left right ≡ false →
  left ≢ right
modeDifferentFromFalse decision equality =
  Output.falseNotTrue
    (trans
      (sym decision)
      (Output.modeEqualComplete equality))

kOrbitCaseCanonical :
  (tau : Physical.PhysicalTriadIncidence) →
  R618.SwapOrbitCase tau
kOrbitCaseCanonical tau
  with Output.modeEqual (Physical.p tau) (Physical.q tau) in decision
... | true =
  R618.fixed
    (R617.inputsEqualImpliesSwapFixed tau
      (Output.modeEqualSound decision))
... | false =
  R618.nonfixed
    (R617.swapNonfixedFromInputsDifferent tau
      (modeDifferentFromFalse decision))

pEnergyLegOrbitCaseCanonical :
  (tau : Physical.PhysicalTriadIncidence) →
  R618.SwapOrbitCase (Orbit.pEnergyLeg tau)
pEnergyLegOrbitCaseCanonical tau
  with Output.modeEqual
    (Physical.k tau)
    (Z3.negateMode (Physical.q tau)) in decision
... | true =
  R618.fixed
    (R617.inputsEqualImpliesSwapFixed
      (Orbit.pEnergyLeg tau)
      (trans
        (Orbit.pEnergyLegFirstInput tau)
        (trans
          (Output.modeEqualSound decision)
          (sym (Orbit.pEnergyLegSecondInput tau)))))
... | false =
  R618.nonfixed
    (R617.pEnergyLegNonfixedFromModeInequality tau
      (modeDifferentFromFalse decision))

qEnergyLegOrbitCaseCanonical :
  (tau : Physical.PhysicalTriadIncidence) →
  R618.SwapOrbitCase (Orbit.qEnergyLeg tau)
qEnergyLegOrbitCaseCanonical tau
  with Output.modeEqual
    (Physical.k tau)
    (Z3.negateMode (Physical.p tau)) in decision
... | true =
  R618.fixed
    (R617.inputsEqualImpliesSwapFixed
      (Orbit.qEnergyLeg tau)
      (trans
        (Orbit.qEnergyLegFirstInput tau)
        (trans
          (Output.modeEqualSound decision)
          (sym (Orbit.qEnergyLegSecondInput tau)))))
... | false =
  R618.nonfixed
    (R617.qEnergyLegNonfixedFromModeInequality tau
      (modeDifferentFromFalse decision))

canonicalThreeLegOrbitResolvedSelection :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  R619.ThreeLegOrbitResolvedSelection system tau
canonicalThreeLegOrbitResolvedSelection system tau tauMember =
  record
    { R619.kMember = tauMember
    ; R619.kOrbit = kOrbitCaseCanonical tau
    ; R619.pOrbit = pEnergyLegOrbitCaseCanonical tau
    ; R619.qOrbit = qEnergyLegOrbitCaseCanonical tau
    }

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round621SwapOrbitCasesDecidableFromLiteralModeGeometry : Bool
round621SwapOrbitCasesDecidableFromLiteralModeGeometry = true

round621CanonicalThreeLegOrbitSelectionConstructed : Bool
round621CanonicalThreeLegOrbitSelectionConstructed = true

round621RequiresUserSuppliedOrbitCaseChoice : Bool
round621RequiresUserSuppliedOrbitCaseChoice = false

round621PreservesFixedOrbitMultiplicityCorrection : Bool
round621PreservesFixedOrbitMultiplicityCorrection = true

round621IntroducesEstimate : Bool
round621IntroducesEstimate = false

round621AnalyticPaymentClosed : Bool
round621AnalyticPaymentClosed = false

round621SwapOrbitCasesDecidableFromLiteralModeGeometryIsTrue :
  round621SwapOrbitCasesDecidableFromLiteralModeGeometry ≡ true
round621SwapOrbitCasesDecidableFromLiteralModeGeometryIsTrue = refl

round621CanonicalThreeLegOrbitSelectionConstructedIsTrue :
  round621CanonicalThreeLegOrbitSelectionConstructed ≡ true
round621CanonicalThreeLegOrbitSelectionConstructedIsTrue = refl

round621RequiresUserSuppliedOrbitCaseChoiceIsFalse :
  round621RequiresUserSuppliedOrbitCaseChoice ≡ false
round621RequiresUserSuppliedOrbitCaseChoiceIsFalse = refl

round621PreservesFixedOrbitMultiplicityCorrectionIsTrue :
  round621PreservesFixedOrbitMultiplicityCorrection ≡ true
round621PreservesFixedOrbitMultiplicityCorrectionIsTrue = refl

round621IntroducesEstimateIsFalse :
  round621IntroducesEstimate ≡ false
round621IntroducesEstimateIsFalse = refl

round621AnalyticPaymentClosedIsFalse :
  round621AnalyticPaymentClosed ≡ false
round621AnalyticPaymentClosedIsFalse = refl
