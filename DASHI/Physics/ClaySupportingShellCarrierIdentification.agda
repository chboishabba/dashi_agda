module DASHI.Physics.ClaySupportingShellCarrierIdentification where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; *-mono-≤ )
open import DASHI.Physics.ClaySupportingShellEnergyBudget
  using (sum; sumDomination)
open import DASHI.Physics.ClaySupportingFiniteShellDissipation
  using ( FiniteShellStrongBudget
         ; finiteShellStrongBudgetFromDissipation
         ; ShellStrongDominatedByDissipation
         ; FiniteShellAlmostOrthogonality
         ; GlobalDissipationBudget
         )
open import DASHI.Physics.ClaySupportingFiniteShellResidueBridge
  using ( PointwiseResidueN2Bound
         ; integratedResidueN2BoundFromShellBudget
         )
open import DASHI.Physics.ClaySupportingResidencePipeline
  using (residenceFromIntegratedResidue)
open import DASHI.Physics.ClaySupportingBKMProjectionSummability
  using ( N2SummabilityBudget; finiteProjectionSumFromResidence )
open import DASHI.Physics.ClaySupportingBKMIntegralBridge
  using (BKMIntegralBridge; applyFiniteProjectionSumBound)
open import DASHI.Physics.ClaySupportingBKMContinuation
  using ( BKMCriterionHypothesis; ContinuationConclusion
         ; bkmContinuationTheorem
         )

open import DASHI.Physics.Closure.NSTriadKNResidueNormModel
  using ( ResidueNormModel; strongDominatesWeakByN
         ; Carrier; weakNormSquared; strongNormSquared
         )

----------------------------------------------------------------------
-- §1  ShellCarrier: concrete per-shell PDE carrier
----------------------------------------------------------------------
--
-- Each carrier N holds the Nat-wrapped PDE data for frequency shell N.
-- The fields correspond, respectively, to:
--
--   weakSq           —  ‖P_N u‖_2²        (L² shell norm squared)
--   strongSq         —  ‖∇P_N u‖_2²       (dissipation shell norm)
--   pointwiseResidue —  Residue_N          (Schur residue functional)
--   integratedDanger —  Danger_N           (integrated danger measure)
--   integratedResidue—  ∫ Residue_N(t) dt  (time-integrated residue)
--   danger≤residue  —  Danger_N ≤ Residue_N (carrier-level semantics)
--   projectionTerm   —  a_N                (BKM projection term)

record ShellCarrier (N : Nat) : Set where
  field
    weakSq            : Nat   -- ∫ ‖P_N u‖₂² dt
    strongSq          : Nat   -- ∫ ‖∇P_N u‖₂² dt
    residueIntegrated : Nat   -- ∫ Residue_N(t) dt
    integratedDanger  : Nat   -- ∫ Danger_N(t) dt
    danger≤residue    : integratedDanger ≤ residueIntegrated
    projectionTerm    : Nat   -- a_N (BKM projection term)

open ShellCarrier public

----------------------------------------------------------------------
-- §2  ShellCarrierFamily — carrier for every shell
----------------------------------------------------------------------

ShellCarrierFamily : Set
ShellCarrierFamily = (N : Nat) → ShellCarrier N

-- Lift fields to Nat → Nat functions

weakSqFamily : ShellCarrierFamily → Nat → Nat
weakSqFamily c N = weakSq (c N)

strongSqFamily : ShellCarrierFamily → Nat → Nat
strongSqFamily c N = strongSq (c N)

residueFamily : ShellCarrierFamily → Nat → Nat
residueFamily c N = residueIntegrated (c N)

dangerFamily : ShellCarrierFamily → Nat → Nat
dangerFamily c N = integratedDanger (c N)

projectionTermFamily : ShellCarrierFamily → Nat → Nat
projectionTermFamily c N = projectionTerm (c N)

----------------------------------------------------------------------
-- §3  Concrete ResidueNormModel for ShellCarrier
----------------------------------------------------------------------
--
--   weakNormSquared   = weakSq
--   strongNormSquared = strongSq
--
-- The N-weighted Bernstein bound:
--   N * weakSq c ≤ strongSq c
-- is an **imported hypothesis** (strongDominatesWeakByN),
-- because it follows from the LP Bernstein inequality which is
-- not yet proved in the repo.  The model carries it as a field.

shellCarrierResidueNormModel :
  (∀ N (c : ShellCarrier N) → N * weakSq c ≤ strongSq c) →
  ResidueNormModel
shellCarrierResidueNormModel strongDWBN =
  record
    { Carrier          = ShellCarrier
    ; weakNormSquared  = λ _ c → weakSq c
    ; strongNormSquared = λ _ c → strongSq c
    ; strongDominatesWeakByN = strongDWBN
    ; modelClosed      = false
    }

----------------------------------------------------------------------
-- §4  Bridge predicates
----------------------------------------------------------------------
--
-- Each bridge records a PDE-facing hypothesis that must be
-- discharged by the concrete Littlewood–Paley / Schur analysis.
-- The carrier identification layer shows what theorems become
-- available once these bridges are inhabited.

-- Bernstein shell inequality:  ∀ carriers, weakSq ≤ C_shell * strongSq
--
record BernsteinCarrierBridge (C_shell : Nat) : Set where
  field
    bnStrongBound : (N : Nat) (x : ShellCarrier N) → weakSq x ≤ C_shell * strongSq x

-- Residue N²-bound:  ∀ carriers, N² * residue ≤ C_res * weakSq
--
record ResidueN2CarrierBridge (C_res : Nat) : Set where
  field
    residueN2Bound : (N : Nat) (x : ShellCarrier N) → (N * N) * residueIntegrated x ≤ C_res * weakSq x

-- Danger dominated by residue:  ∀ carriers, danger ≤ residue
--
record DangerResidueCarrierBridge : Set where
  field
    dangerDominated : (N : Nat) (x : ShellCarrier N) → integratedDanger x ≤ residueIntegrated x

dangerResidueFromCarrierSemantics : DangerResidueCarrierBridge
dangerResidueFromCarrierSemantics = record
  { dangerDominated = λ _ x → ShellCarrier.danger≤residue x
  }

-- BKM projection summability:  ∀ carriers, a_N * N² ≤ C for N ≤ R
--
record ProjectionSummabilityCarrierBridge (C : Nat) : Set where
  field
    perShellN2Bound : (N R : Nat) → (N ≤ R) → (x : ShellCarrier N) → projectionTerm x * (N * N) ≤ C
    groundBound     : (x : ShellCarrier 0) → projectionTerm x ≤ C

----------------------------------------------------------------------
-- §5  Theorem chain: bridge predicates → target bounds
----------------------------------------------------------------------

module TheoremChain
    (c : ShellCarrierFamily)
    (R C_shell C_LP C_res C C_budget : Nat)
    (totalGradSq dissipationBudget : Nat)
    (bnBridge : BernsteinCarrierBridge C_shell)
    (resBridge : ResidueN2CarrierBridge C_res)
    (projBridge : ProjectionSummabilityCarrierBridge C)
    (almostOrthogonality : FiniteShellAlmostOrthogonality
                            (strongSqFamily c) totalGradSq C_LP R)
    (lerayBudget : GlobalDissipationBudget totalGradSq dissipationBudget)
    (summabilityBudget : N2SummabilityBudget)
  where

  open BernsteinCarrierBridge bnBridge
  open ResidueN2CarrierBridge resBridge
  open DangerResidueCarrierBridge dangerResidueFromCarrierSemantics
  open ProjectionSummabilityCarrierBridge projBridge

  ------------------------------------------------------------------
  -- §5a  Per-shell finite strong budget
  --
  --   sum weakSq ≤ (C_shell * C_LP) * dissipationBudget
  ------------------------------------------------------------------

  strongBudget : FiniteShellStrongBudget
                   (weakSqFamily c) R C_shell C_LP dissipationBudget
  strongBudget =
    finiteShellStrongBudgetFromDissipation
      (weakSqFamily c) (strongSqFamily c) R C_shell C_LP
      totalGradSq dissipationBudget
      (λ N → bnStrongBound N (c N)) almostOrthogonality lerayBudget

  ------------------------------------------------------------------
  -- §5b  Per-shell integrated residue N² bound
  --
  --   (N*N) * residue N ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
  ------------------------------------------------------------------

  perShellResidueN2Bound :
    (N : Nat) → N ≤ R → (N * N) * residueFamily c N
              ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
  perShellResidueN2Bound N N≤R =
    integratedResidueN2BoundFromShellBudget
      (residueFamily c) (weakSqFamily c)
      R N C_res C_shell C_LP dissipationBudget
      N≤R
      (residueN2Bound N (c N))
      strongBudget

  ------------------------------------------------------------------
  -- §5c  Integrated danger → residence exclusion bridge
  --
  --   residence * (λ * N²) ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
  --
  -- where λ is the Chebyshev threshold and residence is the
  -- residence-time measure (supplied inline when inhabited).
  ------------------------------------------------------------------

  dangerN2BoundFromResidue :
    (N : Nat) → N ≤ R → (N * N) * dangerFamily c N
              ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
  dangerN2BoundFromResidue N N≤R =
    let
      danger≤res : dangerFamily c N ≤ residueFamily c N
      danger≤res = dangerDominated N (c N)

      N2 : Nat
      N2 = N * N

      step1 : N2 * dangerFamily c N ≤ N2 * residueFamily c N
      step1 = *-mono-≤ (≤-refl {N2}) danger≤res

      step2 : N2 * residueFamily c N
              ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
      step2 = perShellResidueN2Bound N N≤R
    in
    ≤-trans step1 step2

  residenceExclusionBound :
    (N : Nat) → N ≤ R → (lambda residence : Nat) →
    lambda * residence ≤ dangerFamily c N →
    residence * (lambda * (N * N)) ≤ C_res * ((C_shell * C_LP) * dissipationBudget)
  residenceExclusionBound N N≤R lambda res markovBound =
    residenceFromIntegratedResidue
      res lambda (N * N) (C_res * ((C_shell * C_LP) * dissipationBudget))
      (dangerFamily c N) (residueFamily c N)
      markovBound (dangerDominated N (c N)) (perShellResidueN2Bound N N≤R)

  ------------------------------------------------------------------
  -- §5d  Finite projection sum from summability
  --
  --   sum (a_N * productN2) ≤ C * sum (termN2)
  ------------------------------------------------------------------

  projectionSumBound :
    sum (λ N → projectionTermFamily c N
             * N2SummabilityBudget.productN2 summabilityBudget) R
      ≤
    C * sum (N2SummabilityBudget.termN2 summabilityBudget) R
  projectionSumBound =
    finiteProjectionSumFromResidence
      R (projectionTermFamily c) C
      (λ N N≤R′ → perShellN2Bound N R N≤R′ (c N))
      (groundBound (c 0))
      summabilityBudget

  ------------------------------------------------------------------
  -- §5e  BKM integral bridge from projection sum
  --
  -- When an external BKMIntegralBridge is instantiated with
  -- finiteProjectionSum matching our computed shell sum, the
  -- projection sum bound chains through to the BKM integral bound
  -- and, with the BKM criterion, to continuation.
  ------------------------------------------------------------------

  sumProjProduct : Nat
  sumProjProduct =
    sum (λ N → projectionTermFamily c N
             * N2SummabilityBudget.productN2 summabilityBudget) R

  sumTermN2 : Nat
  sumTermN2 = sum (N2SummabilityBudget.termN2 summabilityBudget) R

  chainIntegralFromProjectionSum :
    (integralBridge : BKMIntegralBridge) →
    (matchBound : BKMIntegralBridge.finiteProjectionSum integralBridge ≤ sumProjProduct) →
    BKMIntegralBridge.vorticitySupIntegral integralBridge
      ≤ BKMIntegralBridge.projectionConstant integralBridge * (C * sumTermN2)
  chainIntegralFromProjectionSum integralBridge matchBound =
    let
      open BKMIntegralBridge integralBridge

      total : Nat
      total = C * sumTermN2

      -- finiteProjectionSum ≤ sumProjProduct ≤ C * sumTermN2
      fpSum≤total : finiteProjectionSum ≤ total
      fpSum≤total = ≤-trans matchBound projectionSumBound
    in
    applyFiniteProjectionSumBound integralBridge total fpSum≤total

  continuationFromProjectionSum :
    (integralBridge : BKMIntegralBridge) →
    (matchBound : BKMIntegralBridge.finiteProjectionSum integralBridge ≤ sumProjProduct) →
    BKMCriterionHypothesis → ContinuationConclusion
  continuationFromProjectionSum integralBridge matchBound criterion =
    let
      open BKMIntegralBridge integralBridge

      total : Nat
      total = C * sumTermN2

      fpSum≤total : finiteProjectionSum ≤ total
      fpSum≤total = ≤-trans matchBound projectionSumBound
    in
    bkmContinuationTheorem integralBridge total fpSum≤total criterion

----------------------------------------------------------------------
-- §6  NSDissipationShellBudgetInput & nsFiniteShellStrongBudget
----------------------------------------------------------------------

record NSDissipationShellBudgetInput : Set where
  field
    shellCarrierIdentification : ShellCarrierFamily
    R                          : Nat
    C_shell                    : Nat
    C_LP                       : Nat
    totalGradSq                : Nat
    dissipationBudget          : Nat
    shellPoincare              : BernsteinCarrierBridge C_shell
    lpAlmostOrthogonality      : FiniteShellAlmostOrthogonality
                                   (strongSqFamily shellCarrierIdentification)
                                   totalGradSq C_LP R
    lerayDissipationBudget     : GlobalDissipationBudget totalGradSq dissipationBudget

nsFiniteShellStrongBudget :
  (inp : NSDissipationShellBudgetInput) →
  FiniteShellStrongBudget
    (weakSqFamily (NSDissipationShellBudgetInput.shellCarrierIdentification inp))
    (NSDissipationShellBudgetInput.R inp)
    (NSDissipationShellBudgetInput.C_shell inp)
    (NSDissipationShellBudgetInput.C_LP inp)
    (NSDissipationShellBudgetInput.dissipationBudget inp)
nsFiniteShellStrongBudget inp =
  let
    open NSDissipationShellBudgetInput inp
    open BernsteinCarrierBridge shellPoincare
  in
  finiteShellStrongBudgetFromDissipation
    (weakSqFamily shellCarrierIdentification)
    (strongSqFamily shellCarrierIdentification)
    R C_shell C_LP totalGradSq dissipationBudget
    (λ N → bnStrongBound N (shellCarrierIdentification N))
    lpAlmostOrthogonality
    lerayDissipationBudget

----------------------------------------------------------------------
-- §7  MarkovResidenceCarrierBridge
----------------------------------------------------------------------

record MarkovResidenceCarrierBridge
    (c : ShellCarrierFamily)
    (thresholds : Nat → Nat)
    (resTimes : Nat → Nat) : Set where
  field
    markov : (N : Nat) → thresholds N * resTimes N ≤ dangerFamily c N
