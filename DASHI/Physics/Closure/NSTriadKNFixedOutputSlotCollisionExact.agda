module DASHI.Physics.Closure.NSTriadKNFixedOutputSlotCollisionExact where

------------------------------------------------------------------------
-- PR #890 / FIXED-OUTPUT SLOT-OBSERVABLE COLLISION NEGATIVE CONTROL
--
-- The centered-partner attempt now exposes every R207 same-output raw-curl
-- slot through one literal bilinear observable
--
--   Phi_k(a,b)
--     = a <k,b> + b <a,k> - k <a,b>.
--
-- This owner records the exact carrier-level collision law: once the output
-- mode and the two velocity arguments agree, the slot observable agrees,
-- independently of which physical p/q incidence supplied those amplitudes.
--
-- This is NOT yet a concrete distinct-incidence counterexample.  It is the
-- exact negative-control theorem needed before attempting any lower bound in
-- raw incidence geometry.  A separate witness must still exhibit two distinct
-- localized CC incidences in one output fibre whose velocity arguments agree.
-- Until that witness is source-written, the stronger no-go remains fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact as Adapter

F = Adapter.F

fixedOutputEqualVelocityArgumentsHaveEqualSlotKernel :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (alpha beta : R207.FixedOutputLocalizedComparablePartner system output) →
  let alphaPartner = R207.partner alpha
      betaPartner = R207.partner beta
      alphaTau = R204.incidence (R205.localizedComparable alphaPartner)
      betaTau = R204.incidence (R205.localizedComparable betaPartner)
      alphaUP = Audit.velocity system (Physical.p alphaTau)
      alphaUQ = Audit.velocity system (Physical.q alphaTau)
      betaUP = Audit.velocity system (Physical.p betaTau)
      betaUQ = Audit.velocity system (Physical.q betaTau)
  in
  alphaUP ≡ betaUP →
  alphaUQ ≡ betaUQ →
  Adapter.compressedPartnerSlotKernel alphaPartner
  ≡ Adapter.compressedPartnerSlotKernel betaPartner
fixedOutputEqualVelocityArgumentsHaveEqualSlotKernel
    {E = E} {system = system} {output = output} alpha beta pAgreement qAgreement =
  trans
    (Adapter.fixedOutputSlotKernelIsLiteralOutputFormula alpha)
    (trans
      (cong₂
        (Adapter.literalOutputSlotFormula E output)
        pAgreement
        qAgreement)
      (sym (Adapter.fixedOutputSlotKernelIsLiteralOutputFormula beta)))

roundFixedOutputEqualAmplitudeCollisionLawClosed : Bool
roundFixedOutputEqualAmplitudeCollisionLawClosed = true

roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed : Bool
roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed = false

roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted : Bool
roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted = false

roundFixedOutputCollisionClayPromotion : Bool
roundFixedOutputCollisionClayPromotion = false

roundFixedOutputEqualAmplitudeCollisionLawClosedIsTrue :
  roundFixedOutputEqualAmplitudeCollisionLawClosed ≡ true
roundFixedOutputEqualAmplitudeCollisionLawClosedIsTrue = refl

roundFixedOutputConcreteDistinctCCCollisionWitnessConstructedIsFalse :
  roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed ≡ false
roundFixedOutputConcreteDistinctCCCollisionWitnessConstructedIsFalse = refl

roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefutedIsFalse :
  roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted ≡ false
roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefutedIsFalse = refl
