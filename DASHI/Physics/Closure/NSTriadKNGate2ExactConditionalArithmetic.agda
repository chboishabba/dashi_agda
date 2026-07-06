module DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_*_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl)
open import DASHI.Physics.Closure.ExactGate2ConditionalTheoremBase
  using ( ExactGate2ConditionalTheoremModel
        ; mkExactGate2ConditionalTheoremModel
        )
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using ( ExactKNAOperatorTransferModel
        ; mkExactKNAOperatorTransferModel
        )
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  as ExactTransfer
open import DASHI.Physics.Closure.NSTriadKNGate2AQuotientAwareLiftDefectExpansion
  using (canonicalQuotientAwareLiftDefectExpansionModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalTheorem
  using ( exactGate2ConditionalBound
        ; exactGate2NoPollutionConditionalBound
        ; exactGate2TransferInputBound
        ; exactGate2OutsideSeamInputBound
        ; exactGate2NoPollutionInputBound
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTrueCarrierHypotheses
  using ( NSTriadKNGate2ExactTrueCarrierHypotheses
        ; mkNSTriadKNGate2ExactTrueCarrierHypotheses
        ; projectSplitConditionalHypotheses
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteArithmetic
  using (canonicalExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRouteArithmetic
  using (canonicalExactTransferFromFactorRoute)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamArithmetic
  using (canonicalOutsideSeamTrueCarrierHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalHypotheses
  using (NSTriadKNGate2SplitConditionalHypotheses)
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using ( OutsideSeamAbsorptionModel
        ; mkOutsideSeamAbsorptionModel
        )
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  as Outside

----------------------------------------------------------------------
-- Concrete arithmetic instantiation of the full exact Gate 2 conditional
-- theorem shape on the seam-local twelfths carrier.
--
-- This is not the true NS carrier theorem.  It is the inhabited end-to-end
-- model showing that the exact Gate 2 composition now closes algebraically
-- once the true-carrier hypotheses are supplied.

1# : Nat
1# = suc 0

3# : Nat
3# = suc (suc (suc 0))

12# : Nat
12# =
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 0)))))))))))

canonicalExactKNAOperatorTransferModel :
  ExactKNAOperatorTransferModel
canonicalExactKNAOperatorTransferModel =
  mkExactKNAOperatorTransferModel
    canonicalQuotientAwareLiftDefectExpansionModel
    _*_
    3#
    3#
    3#
    1#
    refl
    refl
    NatP.≤-refl
    NatP.≤-refl

canonicalOutsideSeamAbsorptionModel :
  OutsideSeamAbsorptionModel
canonicalOutsideSeamAbsorptionModel =
  mkOutsideSeamAbsorptionModel
    canonicalExactKNAOperatorTransferModel
    0
    0
    3#
    refl
    NatP.≤-refl
    NatP.≤-refl
    refl

canonicalExactGate2ConditionalTheoremModel :
  ExactGate2ConditionalTheoremModel
canonicalExactGate2ConditionalTheoremModel =
  mkExactGate2ConditionalTheoremModel
    canonicalOutsideSeamAbsorptionModel
    12#
    (s≤s (s≤s (s≤s z≤n)))

canonicalSchurLinearityTransfer :
  ExactTransfer.schurLinearityTransfer
    canonicalExactKNAOperatorTransferModel
canonicalSchurLinearityTransfer = refl

canonicalExactRestrictionIdentity :
  ExactTransfer.exactRestrictionIdentity
    canonicalExactKNAOperatorTransferModel
canonicalExactRestrictionIdentity = refl

canonicalDirectionalTransportBound :
  ExactTransfer.directionalTransportBound
    canonicalExactKNAOperatorTransferModel
canonicalDirectionalTransportBound = NatP.≤-refl

canonicalSubcriticalDirectionalBudget :
  ExactTransfer.subcriticalDirectionalBudget
    canonicalExactKNAOperatorTransferModel
canonicalSubcriticalDirectionalBudget = NatP.≤-refl

canonicalTotalDecomposition :
  Outside.totalDecomposition
    canonicalOutsideSeamAbsorptionModel
canonicalTotalDecomposition = refl

canonicalOutsideAbsorbed :
  Outside.outside≤absorbed
    canonicalOutsideSeamAbsorptionModel
canonicalOutsideAbsorbed = NatP.≤-refl

canonicalExactPlusAbsorbedQuarter :
  Outside.exactPlusAbsorbed≤quarter
    canonicalOutsideSeamAbsorptionModel
canonicalExactPlusAbsorbedQuarter = NatP.≤-refl

canonicalAbsorbedOutsideVanishes :
  Outside.absorbedOutsideVanishes
    canonicalOutsideSeamAbsorptionModel
canonicalAbsorbedOutsideVanishes = refl

canonicalQuarterLeqUnit :
  ExactGate2ConditionalTheoremModel.quarter≤unit
    canonicalExactGate2ConditionalTheoremModel
canonicalQuarterLeqUnit = s≤s (s≤s (s≤s z≤n))

canonicalExactGate2ConditionalBound :
  ExactGate2ConditionalTheoremModel._≤_
    canonicalExactGate2ConditionalTheoremModel
    (ExactGate2ConditionalTheoremModel.total-leakage
      canonicalExactGate2ConditionalTheoremModel)
    (ExactGate2ConditionalTheoremModel.unit-threshold
      canonicalExactGate2ConditionalTheoremModel)
canonicalExactGate2ConditionalBound =
  exactGate2ConditionalBound
    canonicalExactGate2ConditionalTheoremModel

canonicalExactGate2NoPollutionConditionalBound :
  ExactGate2ConditionalTheoremModel._≤_
    canonicalExactGate2ConditionalTheoremModel
    (ExactGate2ConditionalTheoremModel._+_
      canonicalExactGate2ConditionalTheoremModel
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio
        canonicalExactGate2ConditionalTheoremModel)
      (ExactGate2ConditionalTheoremModel.0#
        canonicalExactGate2ConditionalTheoremModel))
    (ExactGate2ConditionalTheoremModel.unit-threshold
      canonicalExactGate2ConditionalTheoremModel)
canonicalExactGate2NoPollutionConditionalBound =
  exactGate2NoPollutionConditionalBound
    canonicalExactGate2ConditionalTheoremModel

canonicalExactTrueCarrierHypotheses :
  NSTriadKNGate2ExactTrueCarrierHypotheses
canonicalExactTrueCarrierHypotheses =
  mkNSTriadKNGate2ExactTrueCarrierHypotheses
    canonicalExactGate2ConditionalTheoremModel
    "Exact Gate 2 true-carrier hypothesis package: once the true carrier supplies exact restriction identity, Schur linearity transfer, directional transport budget, outside-seam decomposition/absorption, and quarter-to-unit margin, the full exact Gate 2 conditional theorem is immediate."
    refl
    canonicalExactKNAOperatorTransferModel
    refl
    canonicalOutsideSeamAbsorptionModel
    refl
    canonicalExactFactorRouteHypotheses
    canonicalExactTransferFromFactorRoute
    canonicalOutsideSeamTrueCarrierHypotheses
    refl
    refl
    refl
    canonicalSchurLinearityTransfer
    canonicalExactRestrictionIdentity
    canonicalDirectionalTransportBound
    canonicalSubcriticalDirectionalBudget
    canonicalTotalDecomposition
    canonicalOutsideAbsorbed
    canonicalExactPlusAbsorbedQuarter
    canonicalAbsorbedOutsideVanishes
    canonicalQuarterLeqUnit
    (exactGate2TransferInputBound
      canonicalExactGate2ConditionalTheoremModel)
    (exactGate2OutsideSeamInputBound
      canonicalExactGate2ConditionalTheoremModel)
    (exactGate2NoPollutionInputBound
      canonicalExactGate2ConditionalTheoremModel)
    canonicalExactGate2ConditionalBound
    canonicalExactGate2NoPollutionConditionalBound
    true
    refl
    true
    refl
    true
    refl

canonicalProjectedSplitConditionalHypotheses :
  NSTriadKNGate2SplitConditionalHypotheses
canonicalProjectedSplitConditionalHypotheses =
  projectSplitConditionalHypotheses
    canonicalExactTrueCarrierHypotheses
