module DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Agda.Builtin.Nat using (Nat; zero; suc)
  renaming (_*_ to _*ℕ_; _+_ to _+ℕ_)
open import Data.Nat using () renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; *-identityˡ)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( PairIncidenceProfile
        ; NSTriadKNPairIncidenceProfileDecompositionModel
        ; Shell
        ; ActualPairIncidenceKernelData
        ; canonicalActualPairIncidenceKernelData
        ; actualUnitShellPairIncidenceKernelDataClosed
        ; actualUnitShellPairIncidenceKernelDataClosedIsFalse
        )
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Cross-profile Schur matrix surface.
--
-- Diagonal profile bounds are not enough to control
--
--   (sum_p R_p) * (sum_q C_q)
--
-- because the cross terms R_p * C_q remain unconstrained. This theorem surface
-- records the honest global Stage 3 requirement:
--
--   forall p q, R_p * C_q <= C_{p,q} / N^2.

record NSTriadKNProfileCrossProductMatrixModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}

    Bound : Set ℓV
    _≤_ : Bound -> Bound -> Set ℓR
    _*_ : Bound -> Bound -> Bound

    profileRowBound :
      PairIncidenceProfile -> Shell decompositionModel -> Bound

    profileColumnBound :
      PairIncidenceProfile -> Shell decompositionModel -> Bound

    profileCrossProductTarget :
      PairIncidenceProfile ->
      PairIncidenceProfile ->
      Shell decompositionModel ->
      Bound

    profileCrossProductBound :
      (p q : PairIncidenceProfile) ->
      (N : Shell decompositionModel) ->
      _≤_ (_*_ (profileRowBound p N)
               (profileColumnBound q N))
          (profileCrossProductTarget p q N)

open NSTriadKNProfileCrossProductMatrixModel public

profileCrossSchurMatrixBound :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNProfileCrossProductMatrixModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  (p q : PairIncidenceProfile) ->
  (N : Shell (decompositionModel m)) ->
  _≤_ m (_*_ m (profileRowBound m p N)
               (profileColumnBound m q N))
        (profileCrossProductTarget m p q N)
profileCrossSchurMatrixBound m =
  profileCrossProductBound m

------------------------------------------------------------------------
-- Upstream kernel/index/operator realization surface.
--
-- The profile cross-product matrix currently closes only at the level of
-- abstract row/column/cross bounds. Weighted Schur cannot export an actual
-- operator witness until the underlying kernel/index data is made concrete.

record ProfileCrossMatrixKernelData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkProfileCrossMatrixKernelData
  field
    Index : Set

    kernel : Index -> Index -> Nat

    coefficient :
      ResidueNorm.Carrier residueNormModel shellIndex → Index → Nat

    weightedSchurOperator :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex

    absWeakPairing :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex →
      Nat

    absQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    operatorRealizesKernel : Set

    absQuadraticFormDef :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≡
        absWeakPairing (weightedSchurOperator x) x

    profileCrossMatrixControlsQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≤ℕ
        weakQuadraticFormConstant
          *ℕ ResidueNorm.weakNormSquared residueNormModel shellIndex x

    kernelRealizesProfileCrossProductMatrix : Set

open ProfileCrossMatrixKernelData public

UnitShellProfileCrossMatrixKernelDataTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellProfileCrossMatrixKernelDataTarget residueNormModel =
  ProfileCrossMatrixKernelData residueNormModel (suc zero)

canonicalProfileCrossMatrixKernelData :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  UnitShellProfileCrossMatrixKernelDataTarget residueNormModel
canonicalProfileCrossMatrixKernelData residueNormModel =
  mkProfileCrossMatrixKernelData
    (ActualPairIncidenceKernelData.Index actualKernelData)
    (ActualPairIncidenceKernelData.actualKernel actualKernelData)
    (λ _ i → entryWeight i)
    (λ x → x)
    (λ _ y →
      ResidueNorm.weakNormSquared residueNormModel (suc zero) y)
    (λ x →
      ResidueNorm.weakNormSquared residueNormModel (suc zero) x)
    (suc zero)
    (ActualPairIncidenceKernelData.kernelRealizesTotalKernel actualKernelData)
    (λ x → refl)
    weakNormControlledBySelf
    (ActualPairIncidenceKernelData.kernelProfileClassification actualKernelData)
  where
    actualKernelData :
      ActualPairIncidenceKernelData residueNormModel (suc zero)
    actualKernelData =
      canonicalActualPairIncidenceKernelData residueNormModel

    entryWeight :
      ActualPairIncidenceKernelData.Index actualKernelData → Nat
    entryWeight i =
      ActualPairIncidenceKernelData.entryOf actualKernelData i

    weakNormControlledBySelf :
      (x : ResidueNorm.Carrier residueNormModel (suc zero)) →
      ResidueNorm.weakNormSquared residueNormModel (suc zero) x
        ≤ℕ
      suc zero *ℕ ResidueNorm.weakNormSquared residueNormModel (suc zero) x
    weakNormControlledBySelf x =
      ≤-reflexive (sym (*-identityˡ
        (ResidueNorm.weakNormSquared residueNormModel (suc zero) x)))

profileCrossMatrixKernelDataClosed : Bool
profileCrossMatrixKernelDataClosed =
  actualUnitShellPairIncidenceKernelDataClosed

profileCrossMatrixKernelDataClosedIsFalse :
  profileCrossMatrixKernelDataClosed ≡ false
profileCrossMatrixKernelDataClosedIsFalse =
  actualUnitShellPairIncidenceKernelDataClosedIsFalse

actualUnitShellProfileCrossMatrixKernelDataClosed : Bool
actualUnitShellProfileCrossMatrixKernelDataClosed =
  profileCrossMatrixKernelDataClosed

actualUnitShellProfileCrossMatrixKernelDataClosedIsFalse :
  actualUnitShellProfileCrossMatrixKernelDataClosed ≡ false
actualUnitShellProfileCrossMatrixKernelDataClosedIsFalse = refl

------------------------------------------------------------------------
-- Proof-derived cross-product matrix gate definitions.

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( forcedTailProfile
        ; adversarialGeometryProfile
        ; transitionProfile
        ; residualProfile
        )

import DASHI.Physics.Closure.NSTriadKNResidualClosureDependency as ResidualClosure
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightBridge as FTWeightBridge
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductAnalyticAudit
  as CrossAudit

------------------------------------------------------------------------
-- Typed analytic evidence inputs.
--
-- These are theorem inputs, not proofs supplied by this module.  In
-- particular, no canonical inhabitant is defined below.  The Nat encoding
-- keeps the exact scale variables visible while the audit target records the
-- profile-specific exponent-sum obligation.

powNat : Nat -> Nat -> Nat
powNat _ zero = suc zero
powNat N (suc k) = N *ℕ powNat N k

record ProfileCrossProductExponentEvidence
    (entry : CrossAudit.ProfileCrossProductExponentEntry) : Set₁ where
  constructor mkProfileCrossProductExponentEvidence
  field
    auditTarget :
      CrossAudit.ProfileCrossProductExponentSumTarget entry

    shellIndex : Nat
    rowMass : Nat -> Nat
    columnMass : Nat -> Nat

    rowConstant : Nat
    columnConstant : Nat
    crossProductConstant : Nat

    rowDecayBound :
      (N : Nat) ->
      powNat N
        (CrossAudit.ProfileCrossProductExponentSumTarget.rowDecayExponent
          auditTarget)
        *ℕ rowMass N
        ≤ℕ rowConstant

    columnDecayBound :
      (N : Nat) ->
      powNat N
        (CrossAudit.ProfileCrossProductExponentSumTarget.columnDecayExponent
          auditTarget)
        *ℕ columnMass N
        ≤ℕ columnConstant

    crossProductBound :
      (N : Nat) ->
      (N *ℕ N) *ℕ (rowMass N *ℕ columnMass N)
        ≤ℕ crossProductConstant

open ProfileCrossProductExponentEvidence public

-- The ten slots remain distinct through their audit entry indices.
ft_ft_cross_from_exponents : Set₁
ft_ft_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.ftFtEntry

adv_ft_cross_from_exponents : Set₁
adv_ft_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.advFtEntry

adv_adv_cross_from_exponents : Set₁
adv_adv_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.advAdvEntry

adv_trans_cross_from_exponents : Set₁
adv_trans_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.advTransEntry

adv_res_cross_from_exponents : Set₁
adv_res_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.advResEntry

trans_ft_cross_from_exponents : Set₁
trans_ft_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.transFtEntry

trans_adv_cross_from_exponents : Set₁
trans_adv_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.transAdvEntry

trans_trans_cross_from_exponents : Set₁
trans_trans_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.transTransEntry

trans_res_cross_from_exponents : Set₁
trans_res_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.transResEntry

res_ft_cross_from_exponents : Set₁
res_ft_cross_from_exponents =
  ProfileCrossProductExponentEvidence CrossAudit.resFtEntry

-- 2. Special forced-tail off-diagonal cross proofs (2 entries)
-- These use:
--   FTWeightBridge.ForcedTailAdversarialCrossProductN2
--   FTWeightBridge.ForcedTailTransitionCrossProductN2

-- Residual reductions expose the same variables and N² inequality, while
-- retaining every upstream premise used by the reduction.
record ResidualCrossProductEvidence
    (rowProfile columnProfile : PairIncidenceProfile) : Set₁ where
  constructor mkResidualCrossProductEvidence
  field
    dominationEvidence :
      ResidualClosure.ResidualKernelDominatedByClosedProfiles

    residualShellIndex : Nat
    residualRowMass : Nat -> Nat
    residualColumnMass : Nat -> Nat
    residualRowDecayExponent : Nat
    residualColumnDecayExponent : Nat
    residualExponentSumAtLeastTwo :
      CrossAudit.two ≤ℕ
        residualRowDecayExponent +ℕ residualColumnDecayExponent
    residualRowConstant : Nat
    residualColumnConstant : Nat
    residualCrossProductConstant : Nat

    residualRowBound :
      (N : Nat) ->
      powNat N residualRowDecayExponent *ℕ residualRowMass N
        ≤ℕ residualRowConstant

    residualColumnBound :
      (N : Nat) ->
      powNat N residualColumnDecayExponent *ℕ residualColumnMass N
        ≤ℕ residualColumnConstant

    residualCrossProductBound :
      (N : Nat) ->
      (N *ℕ N) *ℕ
        (residualRowMass N *ℕ residualColumnMass N)
        ≤ℕ residualCrossProductConstant

open ResidualCrossProductEvidence public

ft_res_cross_from_domination :
  ResidualClosure.ResidualKernelDominatedByClosedProfiles ->
  ft_ft_cross_from_exponents ->
  FTWeightBridge.ForcedTailAdversarialCrossProductN2 ->
  FTWeightBridge.ForcedTailTransitionCrossProductN2 ->
  Set₁
ft_res_cross_from_domination _ _ _ _ =
  ResidualCrossProductEvidence forcedTailProfile residualProfile

res_adv_cross_from_domination :
  ResidualClosure.ResidualKernelDominatedByClosedProfiles ->
  adv_adv_cross_from_exponents ->
  FTWeightBridge.ForcedTailAdversarialCrossProductN2 ->
  trans_adv_cross_from_exponents ->
  Set₁
res_adv_cross_from_domination _ _ _ _ =
  ResidualCrossProductEvidence residualProfile adversarialGeometryProfile

res_trans_cross_from_domination :
  ResidualClosure.ResidualKernelDominatedByClosedProfiles ->
  adv_trans_cross_from_exponents ->
  FTWeightBridge.ForcedTailTransitionCrossProductN2 ->
  trans_trans_cross_from_exponents ->
  Set₁
res_trans_cross_from_domination _ _ _ _ =
  ResidualCrossProductEvidence residualProfile transitionProfile

res_res_cross_from_domination :
  ResidualClosure.ResidualKernelDominatedByClosedProfiles -> Set₁
res_res_cross_from_domination _ =
  ResidualCrossProductEvidence residualProfile residualProfile

record ProfileCrossProductMatrix : Set₁ where
  constructor mkProfileCrossProductMatrix
  field
    dominationEvidence :
      ResidualClosure.ResidualKernelDominatedByClosedProfiles

    -- Layer 1: Exponent-sum entries (10)
    ft-ft : ft_ft_cross_from_exponents
    adv-ft : adv_ft_cross_from_exponents
    adv-adv : adv_adv_cross_from_exponents
    adv-trans : adv_trans_cross_from_exponents
    adv-res : adv_res_cross_from_exponents
    trans-ft : trans_ft_cross_from_exponents
    trans-adv : trans_adv_cross_from_exponents
    trans-trans : trans_trans_cross_from_exponents
    trans-res : trans_res_cross_from_exponents
    res-ft : res_ft_cross_from_exponents

    -- Layer 2: Special forced-tail off-diagonal entries (2)
    ft-adv : FTWeightBridge.ForcedTailAdversarialCrossProductN2
    ft-trans : FTWeightBridge.ForcedTailTransitionCrossProductN2

    -- Layer 3: Residual-domination reductions (4)
    ft-res : ft_res_cross_from_domination
               dominationEvidence
               ft-ft
               ft-adv
               ft-trans

    res-adv : res_adv_cross_from_domination
                dominationEvidence
                adv-adv
                ft-adv
                trans-adv

    res-trans : res_trans_cross_from_domination
                  dominationEvidence
                  adv-trans
                  ft-trans
                  trans-trans

    res-res : res_res_cross_from_domination
                dominationEvidence

profileCrossProductMatrixClosed : Bool
-- Abstract profile-model receipt retained for the legacy decomposition
-- surface.  The actual analytic evidence gate remains fail-closed in the
-- typed evidence and kernel-data surfaces above.
profileCrossProductMatrixClosed = true

profileCrossProductMatrixClosedIsTrue :
  profileCrossProductMatrixClosed ≡ true
profileCrossProductMatrixClosedIsTrue = refl
