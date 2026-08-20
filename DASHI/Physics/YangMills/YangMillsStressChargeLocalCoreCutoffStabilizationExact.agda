module DASHI.Physics.YangMills.YangMillsStressChargeLocalCoreCutoffStabilizationExact where

------------------------------------------------------------------------
-- ROUND85: SPATIAL-CUTOFF REMOVAL ON THE LOCAL CORE BY EVENTUAL CONSTANCY
--
-- CALIBRATION
--
-- Sergio Caracciolo, Giuseppe Curci, Pietro Menotti and Andrea Pelissetto,
-- "The Energy-Momentum Tensor for Lattice Gauge Theories",
-- Annals of Physics 197 (1990), 119--153.
-- DOI: 10.1016/0003-4916(90)90203-Z.
--
-- Marshall H. Stone,
-- "On One-Parameter Unitary Groups in Hilbert Space",
-- Annals of Mathematics 33 (1932), 643--648.
-- DOI: 10.2307/1968538.
--
-- MATHEMATICAL ROLE
--
-- Round84 correctly retained spatial smearing/cutoff removal inside the hard
-- stress theorem.  But the Clay-facing generator comparison is only required on
-- a common invariant dense LOCAL core before Stone/closure machinery takes over.
-- On such a core, a stronger and cheaper route is available:
--
--   if the charge action with spatial cutoff n is unchanged whenever n already
--   contains the support of the local vector/observable, define the limiting
--   charge action using the vector's own support radius.
--
-- Then every sufficiently large cutoff is definitionally equal to that limiting
-- local-core action.  No separate global operator-norm/strong-operator limit is
-- needed merely to define the charge on the core.
--
-- The remaining physical theorem is correspondingly sharper: prove the Ward
-- identity/locality statement that gives this stabilization, then prove the
-- resulting densely-defined charge is essentially self-adjoint (or otherwise
-- has the required self-adjoint closure) and implements the SAME OS translation
-- group.  Eventual cutoff removal itself is compiled here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record LocalCoreCutoffCharge
    (LocalVector Target : Set) : Set₁ where
  field
    supportRadius : LocalVector → Nat
    cutoffChargeAction : Nat → LocalVector → Target

    -- Locality/Ward consequence: any two cutoffs that both contain the support
    -- give the same charge action on that local vector.
    actionStableBeyondSupport :
      ∀ vector leftCutoff rightCutoff →
      supportRadius vector ≤ leftCutoff →
      supportRadius vector ≤ rightCutoff →
      cutoffChargeAction leftCutoff vector
        ≡ cutoffChargeAction rightCutoff vector

open LocalCoreCutoffCharge public

localCoreChargeAction :
  ∀ {LocalVector Target} →
  LocalCoreCutoffCharge LocalVector Target →
  LocalVector → Target
localCoreChargeAction dataSet vector =
  cutoffChargeAction dataSet (supportRadius dataSet vector) vector

cutoffChargeEqualsLocalCoreChargeBeyondSupport :
  ∀ {LocalVector Target}
    (dataSet : LocalCoreCutoffCharge LocalVector Target)
    vector cutoff →
  supportRadius dataSet vector ≤ cutoff →
  cutoffChargeAction dataSet cutoff vector
    ≡ localCoreChargeAction dataSet vector
cutoffChargeEqualsLocalCoreChargeBeyondSupport dataSet vector cutoff supportInside =
  actionStableBeyondSupport dataSet vector cutoff
    (supportRadius dataSet vector)
    supportInside
    (Data.Nat.Base.≤-refl)

allLargeCutoffsAgreeOnLocalCore :
  ∀ {LocalVector Target}
    (dataSet : LocalCoreCutoffCharge LocalVector Target)
    vector leftCutoff rightCutoff →
  supportRadius dataSet vector ≤ leftCutoff →
  supportRadius dataSet vector ≤ rightCutoff →
  cutoffChargeAction dataSet leftCutoff vector
    ≡ cutoffChargeAction dataSet rightCutoff vector
allLargeCutoffsAgreeOnLocalCore dataSet vector leftCutoff rightCutoff =
  actionStableBeyondSupport dataSet vector leftCutoff rightCutoff

record LocalCoreCutoffRemoval
    {LocalVector Target : Set}
    (dataSet : LocalCoreCutoffCharge LocalVector Target) : Set₁ where
  field
    limitingAction : LocalVector → Target
    limitingActionIsSupportCutoff :
      ∀ vector →
      limitingAction vector ≡ localCoreChargeAction dataSet vector
    eventualCutoffAgreement :
      ∀ vector cutoff →
      supportRadius dataSet vector ≤ cutoff →
      cutoffChargeAction dataSet cutoff vector ≡ limitingAction vector

open LocalCoreCutoffRemoval public

localCoreCutoffRemoval :
  ∀ {LocalVector Target}
    (dataSet : LocalCoreCutoffCharge LocalVector Target) →
  LocalCoreCutoffRemoval dataSet
localCoreCutoffRemoval dataSet = record
  { limitingAction = localCoreChargeAction dataSet
  ; limitingActionIsSupportCutoff = λ vector → refl
  ; eventualCutoffAgreement =
      cutoffChargeEqualsLocalCoreChargeBeyondSupport dataSet
  }

stressChargeLocalCoreCutoffRemovalLevel : ProofLevel
stressChargeLocalCoreCutoffRemovalLevel = machineChecked

-- Remaining physical L6 seam after this compiler:
--   Ward/locality -> `actionStableBeyondSupport` on the SAME continuum local core;
--   closability/essential self-adjointness of the resulting charge;
--   charge exponentials implement the SAME reconstructed OS translations.
-- A separate global spatial-cutoff convergence theorem is not required merely
-- to define the generator on that core.
physicalStressWardLocalCoreStabilizationLevel : ProofLevel
physicalStressWardLocalCoreStabilizationLevel = conditional
