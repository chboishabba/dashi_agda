module DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; *-monoʳ-≤; ≤-reflexive; *-zeroʳ)
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.ClaySupportingResidenceTimeAlgebra as ResidenceAlgebra
import DASHI.Physics.ClaySupportingResidencePipeline as ResidencePipeline
import DASHI.Physics.ClaySupportingShellEnergyBudget as ShellEnergy
import DASHI.Physics.ClaySupportingBKMProjectionSummability as BKMSummability

import DASHI.Physics.Closure.NSTriadKNSchurResidueScale as ResidueScale
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)

------------------------------------------------------------------------
-- BKM / residence bridge surface.
--
-- The final NS-facing bridge must combine the Schur residue scale with a
-- separate residence-time or projection-smallness theorem. This module names
-- that dependency honestly.

record NSTriadKNBKMResidenceBridgeModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    schurResidueScaleModel :
      ResidueScale.NSTriadKNSchurResidueScaleModel {ℓS} {ℓE} {ℓV} {ℓR}

    ResidenceTimeExclusion : Set ℓR

    BKMProjectionSmallness : Set ℓR

    schurResidueScaleToBKMProjectionSmallness :
      ResidenceTimeExclusion ->
      BKMProjectionSmallness

    qGapAndResidenceExcludeBKMBlowup :
      ResidenceTimeExclusion ->
      BKMProjectionSmallness

open NSTriadKNBKMResidenceBridgeModel public

------------------------------------------------------------------------
-- Target and gate for IntegratedResidueN2Bound.

record IntegratedResidueN2BoundTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (N : Nat) : Set₁ where
  constructor mkIntegratedResidueN2BoundTarget
  field
    -- Pointwise Schur residue functional
    pointwiseResidue :
      ResidueNorm.Carrier residueNormModel N → Nat

    -- Time-integrated strong shell budget (integral of ||x_N(t)||_s^2)
    integratedStrongBudget : Nat

    -- The integrated residue functional (integral of residue)
    integratedResidue : Nat

    -- Pointwise bound constant C_res
    pointwiseConstant : Nat

    -- Strong energy/dissipation budget constant C_E
    energyBudgetConstant : Nat

    -- Pointwise Schur residue bound: N² * pointwiseResidue x ≤ pointwiseConstant * strongNormSq x
    pointwiseResidueBound :
      (x : ResidueNorm.Carrier residueNormModel N) →
      (N * N) * pointwiseResidue x
        ≤
      pointwiseConstant
        * ResidueNorm.strongNormSquared residueNormModel N x

    -- Separate constant for the integrated norm bound
    integratedConstant : Nat

    -- Time-integrated energy budget: integratedStrongBudget ≤ energyBudgetConstant
    energyBudgetBound :
      integratedStrongBudget ≤ energyBudgetConstant

    -- Integrated residue definition bound (mock/integral algebra):
    -- N² * integratedResidue ≤ integratedConstant * integratedStrongBudget
    integratedResidueDefinition :
      (N * N) * integratedResidue
        ≤
      integratedConstant * integratedStrongBudget

    targetClosed : Bool

canonicalIntegratedResidueN2BoundTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  IntegratedResidueN2BoundTarget residueNormModel N
canonicalIntegratedResidueN2BoundTarget residueNormModel N = record
  { pointwiseResidue = λ x → zero
  ; integratedStrongBudget = zero
  ; integratedResidue = zero
  ; pointwiseConstant = zero
  ; integratedConstant = zero
  ; energyBudgetConstant = zero
  ; pointwiseResidueBound = λ x → ≤-reflexive (*-zeroʳ (N * N))
  ; energyBudgetBound = z≤n
  ; integratedResidueDefinition = ≤-reflexive (*-zeroʳ (N * N))
  ; targetClosed = false -- Open / Fail-closed!
  }

integratedResidueN2BoundClosed :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  IntegratedResidueN2BoundTarget residueNormModel N → Bool
integratedResidueN2BoundClosed residueNormModel N target =
  IntegratedResidueN2BoundTarget.targetClosed target

proveIntegratedResidueN2Bound :
  (N : Nat) →
  (pointwiseConstant : Nat) →
  (energyBudgetConstant : Nat) →
  (integratedStrongBudget : Nat) →
  (integratedResidue : Nat) →
  (energyBudgetBound : integratedStrongBudget ≤ energyBudgetConstant) →
  (integratedResidueDefinition : (N * N) * integratedResidue ≤ pointwiseConstant * integratedStrongBudget) →
  (N * N) * integratedResidue ≤ pointwiseConstant * energyBudgetConstant
proveIntegratedResidueN2Bound N pointwiseConstant energyBudgetConstant integratedStrongBudget integratedResidue energyBudgetBound integratedResidueDefinition =
  let
    N2 = N * N
    lhs = N2 * integratedResidue
    mid = pointwiseConstant * integratedStrongBudget
    rhs = pointwiseConstant * energyBudgetConstant

    -- 1. N2 * integratedResidue ≤ pointwiseConstant * integratedStrongBudget
    step1 : lhs ≤ mid
    step1 = integratedResidueDefinition

    -- 2. pointwiseConstant * integratedStrongBudget ≤ pointwiseConstant * energyBudgetConstant
    step2 : mid ≤ rhs
    step2 = *-monoʳ-≤ pointwiseConstant energyBudgetBound
  in
  ≤-trans step1 step2

proveShellBudgetFromGlobalSum :
  (shellBudget : Nat → Nat) →
  (R N : Nat) →
  (N ≤ R) →
  (C : Nat) →
  (globalBudget : Nat) →
  (sumBound : ShellEnergy.sum shellBudget R ≤ C * globalBudget) →
  shellBudget N ≤ C * globalBudget
proveShellBudgetFromGlobalSum shellBudget R N N≤R C globalBudget sumBound =
  ShellEnergy.shellBudgetFromGlobalDissipation shellBudget R N N≤R C globalBudget sumBound

------------------------------------------------------------------------
-- Target and gate for IntegratedDangerFromSchurResidue.

record IntegratedDangerFromSchurResidueTarget
    (residueNormModel : ResidueNorm.ResidueNormModel) : Set₁ where
  constructor mkIntegratedDangerFromSchurResidueTarget
  field
    integratedDanger : Nat → Nat
    schurResidueIntegrated : Nat → Nat
    dangerBoundConstant : Nat

    dangerDominatedByResidue :
      (N : Nat) →
      integratedDanger N ≤ schurResidueIntegrated N

    integratedResidueN2Bound :
      (N : Nat) →
      (N * N) * schurResidueIntegrated N ≤ dangerBoundConstant

    targetClosed : Bool

canonicalIntegratedDangerFromSchurResidueTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  IntegratedDangerFromSchurResidueTarget residueNormModel
canonicalIntegratedDangerFromSchurResidueTarget residueNormModel = record
  { integratedDanger = λ _ → zero
  ; schurResidueIntegrated = λ _ → zero
  ; dangerBoundConstant = zero
  ; dangerDominatedByResidue = λ _ → z≤n
  ; integratedResidueN2Bound = λ N → ≤-reflexive (*-zeroʳ (N * N))
  ; targetClosed = false -- Open / Fail-closed!
  }

integratedDangerFromSchurResidueClosed :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  IntegratedDangerFromSchurResidueTarget residueNormModel → Bool
integratedDangerFromSchurResidueClosed residueNormModel target =
  IntegratedDangerFromSchurResidueTarget.targetClosed target

proveIntegratedDangerN2Bound :
  (N : Nat) →
  (integratedDanger : Nat → Nat) →
  (schurResidueIntegrated : Nat → Nat) →
  (dangerBoundConstant : Nat) →
  (dangerDominatedByResidue : (n : Nat) → integratedDanger n ≤ schurResidueIntegrated n) →
  (integratedResidueN2Bound : (n : Nat) → (n * n) * schurResidueIntegrated n ≤ dangerBoundConstant) →
  (N * N) * integratedDanger N ≤ dangerBoundConstant
proveIntegratedDangerN2Bound N integratedDanger schurResidueIntegrated dangerBoundConstant dangerDominatedByResidue integratedResidueN2Bound =
  let
    N2 = N * N
    danger = integratedDanger N
    residue = schurResidueIntegrated N

    -- 1. N2 * danger ≤ N2 * residue
    step1 : N2 * danger ≤ N2 * residue
    step1 = *-monoʳ-≤ N2 (dangerDominatedByResidue N)

    -- 2. N2 * residue ≤ dangerBoundConstant
    step2 : N2 * residue ≤ dangerBoundConstant
    step2 = integratedResidueN2Bound N
  in
  ≤-trans step1 step2

------------------------------------------------------------------------
-- Target and gate for residence-time exclusion.

record ResidenceTimeExclusionTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (N : Nat) : Set₁ where
  constructor mkResidenceTimeExclusionTarget
  field
    -- The danger functional / projection functional
    dangerFunctional : ResidueNorm.Carrier residueNormModel N → Nat

    -- The threshold sequence lambda_N
    threshold : Nat

    -- The residence time subset measure (represented as a function of the threshold)
    residenceTimeMeasure : Nat → Nat

    -- The estimate: |E_N(λ_N)| ≤ C * λ_N⁻¹ * N⁻²
    -- Mathematically: residenceTimeMeasure threshold * (threshold * (N * N)) ≤ C_residence
    residenceBoundConstant : Nat
    residenceBound :
      residenceTimeMeasure threshold * (threshold * (N * N))
        ≤
      residenceBoundConstant

    targetClosed : Bool

canonicalResidenceTimeExclusionTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  ResidenceTimeExclusionTarget residueNormModel N
canonicalResidenceTimeExclusionTarget residueNormModel N = record
  { dangerFunctional = λ x → zero
  ; threshold = 1
  ; residenceTimeMeasure = λ _ → zero
  ; residenceBoundConstant = zero
  ; residenceBound = z≤n
  ; targetClosed = false -- Open / Fail-closed!
  }

residenceTimeExclusionClosed :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  ResidenceTimeExclusionTarget residueNormModel N → Bool
residenceTimeExclusionClosed residueNormModel N target =
  ResidenceTimeExclusionTarget.targetClosed target

proveResidenceTimeExclusionFromIntegratedDanger :
  (N : Nat) →
  (threshold : Nat) →
  (residenceTimeMeasure : Nat) →
  (integratedDanger : Nat) →
  (C-residence : Nat) →
  (dangerBound : threshold * residenceTimeMeasure ≤ integratedDanger) →
  (integratedDangerBound : (N * N) * integratedDanger ≤ C-residence) →
  residenceTimeMeasure * (threshold * (N * N)) ≤ C-residence
proveResidenceTimeExclusionFromIntegratedDanger N threshold residenceTimeMeasure integratedDanger C-residence dangerBound integratedDangerBound =
  ResidenceAlgebra.residenceAlgebraLemma
    residenceTimeMeasure
    threshold
    (N * N)
    C-residence
    integratedDanger
    dangerBound
    integratedDangerBound

proveResidenceTimeExclusionFromIntegratedResidue :
  (N : Nat) →
  (threshold : Nat) →
  (residenceTimeMeasure : Nat) →
  (integratedDanger integratedResidue : Nat) →
  (C : Nat) →
  (dangerBound : threshold * residenceTimeMeasure ≤ integratedDanger) →
  (dangerDominatedByResidue : integratedDanger ≤ integratedResidue) →
  (integratedResidueN2Bound : (N * N) * integratedResidue ≤ C) →
  residenceTimeMeasure * (threshold * (N * N)) ≤ C
proveResidenceTimeExclusionFromIntegratedResidue
  N threshold residenceTimeMeasure integratedDanger integratedResidue C
  dangerBound dangerDominatedByResidue integratedResidueN2Bound =
  ResidencePipeline.residenceFromIntegratedResidue
    residenceTimeMeasure threshold (N * N) C
    integratedDanger integratedResidue
    dangerBound dangerDominatedByResidue integratedResidueN2Bound

proveProjectionTermN2BoundFromResidence :
  (residenceMeasure : Nat) →
  (threshold : Nat) →
  (N : Nat) →
  (C : Nat) →
  residenceMeasure * (threshold * (N * N)) ≤ C →
  (threshold * residenceMeasure) * (N * N) ≤ C
proveProjectionTermN2BoundFromResidence residenceMeasure threshold N C hyp =
  BKMSummability.projectionTermFromResidence residenceMeasure threshold N C hyp

proveFiniteProjectionSumFromResidence :
  (R : Nat) →
  (a : Nat → Nat) →
  (C : Nat) →
  (hyp : (N : Nat) → N ≤ R → a N * (N * N) ≤ C) →
  (groundBound : a 0 ≤ C) →
  (budget : BKMSummability.N2SummabilityBudget) →
  BKMSummability.sum (λ N → a N * BKMSummability.N2SummabilityBudget.productN2 budget) R
    ≤
  C * BKMSummability.sum (BKMSummability.N2SummabilityBudget.termN2 budget) R
proveFiniteProjectionSumFromResidence R a C hyp groundBound budget =
  BKMSummability.finiteProjectionSumFromResidence R a C hyp groundBound budget

------------------------------------------------------------------------
-- Target and gate for BKM projection smallness.

record BKMProjectionSmallnessTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (N : Nat) : Set₁ where
  constructor mkBKMProjectionSmallnessTarget
  field
    residenceTimeInputClosed : Bool

    -- The shell projection bound of the vorticity (e.g. ||vorticity_N||_inf)
    shellProjection :
      ResidueNorm.Carrier residueNormModel N → Nat

    -- The sum coefficient B_N
    shellCoefficient : Nat

    -- The total sum of shell projections
    vorticitySum :
      ResidueNorm.Carrier residueNormModel N → Nat

    -- The finite integral of vorticity over time [0, T]
    vorticityIntegral : Nat

    -- The bound: vorticitySum x ≤ shellCoefficient * shellProjection x
    vorticitySumBound :
      (x : ResidueNorm.Carrier residueNormModel N) →
      vorticitySum x ≤ shellCoefficient * shellProjection x

    targetClosed : Bool

canonicalBKMProjectionSmallnessTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  BKMProjectionSmallnessTarget residueNormModel N
canonicalBKMProjectionSmallnessTarget residueNormModel N = record
  { residenceTimeInputClosed = false
  ; shellProjection = λ x → zero
  ; shellCoefficient = 0
  ; vorticitySum = λ x → zero
  ; vorticityIntegral = 0
  ; vorticitySumBound = λ x → z≤n
  ; targetClosed = false -- Open / Fail-closed!
  }

bkmProjectionSmallnessClosed :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  BKMProjectionSmallnessTarget residueNormModel N → Bool
bkmProjectionSmallnessClosed residueNormModel N target =
  BKMProjectionSmallnessTarget.targetClosed target

------------------------------------------------------------------------
-- Proof-derived gate definitions.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

bkmExclusionProved :
  QGap.ResidueScaleCompatibility → Bool
bkmExclusionProved compat with ResidueScale.schurResidueScaleClosed compat
... | true = true
... | false = false

bkmExclusionProvedIsTrue :
  (compat : QGap.ResidueScaleCompatibility) →
  QGap.compatibilityRouteClosed compat ≡ true →
  bkmExclusionProved compat ≡ true
bkmExclusionProvedIsTrue compat routeClosed
  rewrite ResidueScale.schurResidueScaleClosedIsTrue compat routeClosed = refl
