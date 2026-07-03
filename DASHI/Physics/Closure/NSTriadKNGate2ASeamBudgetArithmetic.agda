module DASHI.Physics.Closure.NSTriadKNGate2ASeamBudgetArithmetic where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_*_)
open import Data.Nat.Properties as NatP
  using (≤-refl; *-mono-≤)
open import DASHI.Physics.Closure.ConeWidthDefectScalingBase
  using (ConeWidthDefectScalingModel; mkConeWidthDefectScalingModel)
open import DASHI.Physics.Closure.DefectBudgetBase
  using (DefectBudget; mkDefectBudget)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance
  using (NatOrderedMonoid)
open import DASHI.Physics.Closure.NearExtremizerDefectEstimateBase
  using (NearExtremizerDefectEstimateModel;
         mkNearExtremizerDefectEstimateModel)
open import DASHI.Physics.Closure.QuarterMarginBase
  using (QuarterMarginModel; mkQuarterMarginModel)

------------------------------------------------------------------------
-- Concrete arithmetic carrier for the seam-local Gate 2-A closure.
--
-- We measure all defect and margin constants in twelfths:
--
--   η-cross     = 1   = 1/12
--   η-pure      = 0   = 0/12
--   η-defect    = 1   = 1/12
--   θ-principal = 2   = 1/6
--   1/4         = 3   = 3/12
--
-- This gives an exact seam-local budget closure:
--
--   θ-principal + η-defect = 2 + 1 = 3 = 1/4.

0# : Nat
0# = zero

1# : Nat
1# = suc 0#

2# : Nat
2# = suc 1#

3# : Nat
3# = suc 2#

ε# : Nat
ε# = 1#

α# : Nat
α# = 1#

β# : Nat
β# = 0#

η-cross# : Nat
η-cross# = 1#

η-pure# : Nat
η-pure# = 0#

η-defect# : Nat
η-defect# = 1#

θ-principal# : Nat
θ-principal# = 2#

one-sixth# : Nat
one-sixth# = 2#

one-twelfth# : Nat
one-twelfth# = 1#

one-quarter# : Nat
one-quarter# = 3#

canonicalGate2ADefectBudget : DefectBudget
canonicalGate2ADefectBudget =
  mkDefectBudget
    NatOrderedMonoid
    η-cross#
    η-pure#
    η-defect#
    refl

canonicalNearExtremizerDefectEstimateModel :
  NearExtremizerDefectEstimateModel
canonicalNearExtremizerDefectEstimateModel =
  mkNearExtremizerDefectEstimateModel
    canonicalGate2ADefectBudget
    η-cross#
    η-pure#
    η-defect#
    NatP.≤-refl
    NatP.≤-refl
    NatP.≤-refl

canonicalConeWidthDefectScalingModel : ConeWidthDefectScalingModel
canonicalConeWidthDefectScalingModel =
  mkConeWidthDefectScalingModel
    NatOrderedMonoid
    _*_
    ε#
    α#
    β#
    η-cross#
    η-pure#
    NatP.≤-refl
    NatP.≤-refl
    (λ a b c d a≤b c≤d → NatP.*-mono-≤ a≤b c≤d)

canonicalQuarterMarginModel : QuarterMarginModel
canonicalQuarterMarginModel =
  mkQuarterMarginModel
    NatOrderedMonoid
    θ-principal#
    η-defect#
    one-sixth#
    one-twelfth#
    one-quarter#
    NatP.≤-refl
    NatP.≤-refl
    NatP.≤-refl
