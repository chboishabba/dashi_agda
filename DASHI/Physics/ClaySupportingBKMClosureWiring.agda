module DASHI.Physics.ClaySupportingBKMClosureWiring where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-reflexive; ≤-trans; *-mono-≤; *-assoc )
open import DASHI.Physics.ClaySupportingShellEnergyBudget
  using (sum; sumDomination)
open import DASHI.Physics.ClaySupportingFiniteShellDissipation
  using ( FiniteShellAlmostOrthogonality; GlobalDissipationBudget )
open import DASHI.Physics.ClaySupportingFiniteShellResidueBridge
  using ( integratedResidueN2BoundFromShellBudget )
open import DASHI.Physics.ClaySupportingBKMProjectionSummability
  using ( N2SummabilityBudget )
open import DASHI.Physics.ClaySupportingBKMIntegralBridge
  using (BKMIntegralBridge)
open import DASHI.Physics.ClaySupportingBKMContinuation
  using (BKMCriterionHypothesis)

import DASHI.Physics.ClaySupportingShellCarrierIdentification as CarrierID
open CarrierID
  using ( ShellCarrier; ShellCarrierFamily
         ; weakSqFamily; strongSqFamily; residueFamily; dangerFamily
         ; projectionTermFamily
         ; BernsteinCarrierBridge; ResidueN2CarrierBridge
         ; DangerResidueCarrierBridge; ProjectionSummabilityCarrierBridge
         ; shellCarrierResidueNormModel
         ; NSDissipationShellBudgetInput; nsFiniteShellStrongBudget
         ; MarkovResidenceCarrierBridge
         )

open import DASHI.Physics.Closure.NSTriadKNResidueNormModel
  using ( ResidueNormModel; Carrier; weakNormSquared; strongNormSquared )
open import DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge
  using ( IntegratedResidueN2BoundTarget
         ; IntegratedDangerFromSchurResidueTarget
         ; ResidenceTimeExclusionTarget
         ; BKMProjectionSmallnessTarget
         )

----------------------------------------------------------------------
-- §1  Helper lemma: intermediate residue bound against strong budget
----------------------------------------------------------------------

intermediateResidueDefinition :
  (residueInt shellNormInt : Nat → Nat) (R N C_res : Nat) →
  (N ≤ R) →
  ((N * N) * residueInt N ≤ C_res * shellNormInt N) →
  (shellNormInt N ≤ sum shellNormInt R) →
  (N * N) * residueInt N ≤ C_res * sum shellNormInt R
intermediateResidueDefinition residueInt shellNormInt R N C_res N≤R
  residueBound normDom =
  let
    step1 : (N * N) * residueInt N ≤ C_res * shellNormInt N
    step1 = residueBound

    step2 : C_res * shellNormInt N ≤ C_res * sum shellNormInt R
    step2 = *-mono-≤ (≤-refl {C_res}) normDom
  in
  ≤-trans step1 step2

----------------------------------------------------------------------
-- §2  Target inhabitation module
----------------------------------------------------------------------
--
-- Given a ShellCarrierFamily, universal bridges, and analytic inputs,
-- inhabits the NSTriadKN targets for a specific shell N ≤ R.
-- All targets remain targetClosed = false.

module InhabitTargets
    (budgetInput : NSDissipationShellBudgetInput)
    (N : Nat)
    (C_res C_budget C_bridge : Nat)
    (N≤R : N ≤ NSDissipationShellBudgetInput.R budgetInput)
    (resBridge : ResidueN2CarrierBridge C_res)
    (projBridge : ProjectionSummabilityCarrierBridge C_budget)
    (strongDWBN : ∀ N (x : ShellCarrier N) → N * ShellCarrier.weakSq x ≤ ShellCarrier.strongSq x)
    (summabilityBudget : N2SummabilityBudget)
  where

  open NSDissipationShellBudgetInput budgetInput
    renaming ( shellCarrierIdentification to c )

  -- Instantiate the theorem chain
  open CarrierID.TheoremChain
    c R C_shell C_LP C_res C_budget 0
    totalGradSq dissipationBudget
    shellPoincare resBridge projBridge
    lpAlmostOrthogonality lerayDissipationBudget summabilityBudget

  -- Concrete ResidueNormModel with the N-weighted Bernstein bound
  rnm : ResidueNormModel
  rnm = shellCarrierResidueNormModel strongDWBN

  ------------------------------------------------------------------
  -- §2a  IntegratedResidueN2BoundTarget (for shell N)
  ------------------------------------------------------------------

  integratedResidueN2Target : IntegratedResidueN2BoundTarget rnm N
  integratedResidueN2Target = record
    { pointwiseResidue = λ x → ShellCarrier.residueIntegrated x
    ; integratedStrongBudget = sum (weakSqFamily c) R
    ; integratedResidue = residueFamily c N
    ; pointwiseConstant = C_res * C_shell
    ; integratedConstant = C_res
    ; energyBudgetConstant = (C_shell * C_LP) * dissipationBudget
    ; pointwiseResidueBound = λ x →
        let
          resN2 : (N * N) * ShellCarrier.residueIntegrated x
                  ≤ C_res * ShellCarrier.weakSq x
          resN2 = ResidueN2CarrierBridge.residueN2Bound resBridge N x

          weak2strong : ShellCarrier.weakSq x
                        ≤ C_shell * ShellCarrier.strongSq x
          weak2strong = BernsteinCarrierBridge.bnStrongBound shellPoincare N x

          step1 : (N * N) * ShellCarrier.residueIntegrated x
                  ≤ C_res * (C_shell * ShellCarrier.strongSq x)
          step1 = ≤-trans resN2 (*-mono-≤ (≤-refl {C_res}) weak2strong)

          -- C_res * (C_shell * strongSq) = (C_res * C_shell) * strongSq
          assoc : C_res * (C_shell * ShellCarrier.strongSq x)
                  ≡ (C_res * C_shell) * ShellCarrier.strongSq x
          assoc = sym (*-assoc C_res C_shell (ShellCarrier.strongSq x))
        in
        ≤-trans step1 (≤-reflexive assoc)
    ; energyBudgetBound = strongBudget
    ; integratedResidueDefinition =
        let
          resBound : (N * N) * residueFamily c N ≤ C_res * weakSqFamily c N
          resBound = ResidueN2CarrierBridge.residueN2Bound resBridge N (c N)

          normDom : weakSqFamily c N ≤ sum (weakSqFamily c) R
          normDom = sumDomination (weakSqFamily c) R N N≤R
        in
        ≤-trans
          resBound
          (*-mono-≤ (≤-refl {C_res}) normDom)
    ; targetClosed = false
    }

  ------------------------------------------------------------------
  -- §2b  ResidenceTimeExclusionTarget (for shell N)
  ------------------------------------------------------------------

  residenceExclusionTarget :
    (thresholds : Nat → Nat) → (resTimes : Nat → Nat) →
    (markovBridge : MarkovResidenceCarrierBridge c thresholds resTimes) →
    ResidenceTimeExclusionTarget rnm N
  residenceExclusionTarget thresholds resTimes markovBridge = record
    { dangerFunctional = λ x → ShellCarrier.integratedDanger x
    ; threshold = thresholds N
    ; residenceTimeMeasure = λ _ → resTimes N
    ; residenceBoundConstant = C_res * ((C_shell * C_LP) * dissipationBudget)
    ; residenceBound =
        residenceExclusionBound N N≤R (thresholds N) (resTimes N)
          (MarkovResidenceCarrierBridge.markov markovBridge N)
    ; targetClosed = false
    }

  ------------------------------------------------------------------
  -- §2c  BKMProjectionSmallnessTarget (for shell N)
  ------------------------------------------------------------------

  bkmProjectionSmallnessTarget :
    (bridge : ∀ N (x : ShellCarrier N) → ShellCarrier.integratedDanger x
              ≤ C_budget * ShellCarrier.projectionTerm x) →
    BKMProjectionSmallnessTarget rnm N
  bkmProjectionSmallnessTarget projBridge = record
    { residenceTimeInputClosed = false
    ; shellProjection = λ x → ShellCarrier.projectionTerm x
    ; shellCoefficient = C_budget
    ; vorticitySum = λ x → ShellCarrier.integratedDanger x
    ; vorticityIntegral = 0
    ; vorticitySumBound = λ x → projBridge N x
    ; targetClosed = false
    }

  ------------------------------------------------------------------
  -- §2d  BKM continuation from projection sum + integral bridge
  ------------------------------------------------------------------

  continuationFromProjectionSumWired :
    (integralBridge : BKMIntegralBridge) →
    (matchBound : BKMIntegralBridge.finiteProjectionSum integralBridge
                  ≤ sumProjProduct) →
    (criterion : BKMCriterionHypothesis) →
    DASHI.Physics.ClaySupportingBKMContinuation.ContinuationConclusion
  continuationFromProjectionSumWired integralBridge matchBound criterion =
    continuationFromProjectionSum integralBridge matchBound criterion
