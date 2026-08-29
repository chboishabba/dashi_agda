{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2LiteralSameHistoryPrefixSensitivityRound103Exact where

------------------------------------------------------------------------
-- ROUND103 A2: PHYSICAL-SHELL SENSITIVITIES -> CUMULATIVE SAME-HISTORY q
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ; 0ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_
  ; ≤ℝ-refl; ≤ℝ-trans; +-mono-≤; absZero; absAddSubadditive
  ; *-distribʳ-+; subAddDistributes; subSelf; mulZeroˡ )
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanBetaPrefixSensitivityToTubeContractionExact as Shoot

transport≤ : ∀ {a b c d : ℝ} → a ≡ b → c ≡ d → b ≤ℝ c → a ≤ℝ d
transport≤ refl refl proof = proof

sumReal : (Nat → ℝ) → Nat → ℝ
sumReal f zero = 0ℝ
sumReal f (suc n) = sumReal f n +ℝ f n

record LiteralSameHistoryShellSensitivity (TubePoint : Set) (K : Nat) : Set₁ where
  field
    initialInverseSquare : TubePoint → ℝ
    dynamics : TubePoint → BetaLaw.BalabanCutoffCouplingDynamics K
    shellSensitivity : Nat → ℝ

    -- Only j<K is requested.  No bound is imposed on the total-function
    -- extension of betaCorrection after the physical cutoff.
    shellLipschitz : ∀ u v j → j ℕ.< K →
      absℝ
        (Trajectory.betaCorrection
            (BetaLaw.step (dynamics u)) (suc j)
          -ℝ Trajectory.betaCorrection
            (BetaLaw.step (dynamics v)) (suc j))
      ≤ℝ shellSensitivity j *ℝ
          absℝ (initialInverseSquare u -ℝ initialInverseSquare v)

open LiteralSameHistoryShellSensitivity public

betaPrefixAt :
  ∀ {TubePoint K} →
  LiteralSameHistoryShellSensitivity TubePoint K → TubePoint → Nat → ℝ
betaPrefixAt dataSet point zero = 0ℝ
betaPrefixAt dataSet point (suc n) =
  betaPrefixAt dataSet point n
    +ℝ Trajectory.betaCorrection
      (BetaLaw.step (dynamics dataSet point)) (suc n)

prefixDifferenceBound :
  ∀ {TubePoint K}
    (dataSet : LiteralSameHistoryShellSensitivity TubePoint K)
    u v n → n ℕ.≤ K →
  absℝ (betaPrefixAt dataSet u n -ℝ betaPrefixAt dataSet v n)
  ≤ℝ sumReal (shellSensitivity dataSet) n *ℝ
      absℝ (initialInverseSquare dataSet u -ℝ initialInverseSquare dataSet v)
prefixDifferenceBound dataSet u v zero zero≤K =
  let
    leftZero = trans (cong absℝ (subSelf 0ℝ)) absZero
    distance = absℝ
      (initialInverseSquare dataSet u -ℝ initialInverseSquare dataSet v)
    rightZero = mulZeroˡ distance
  in
  transport≤ leftZero (sym rightZero) ≤ℝ-refl
prefixDifferenceBound {K = K} dataSet u v (suc n) sn≤K =
  let
    bu = betaPrefixAt dataSet u n
    bv = betaPrefixAt dataSet v n
    eu = Trajectory.betaCorrection
      (BetaLaw.step (dynamics dataSet u)) (suc n)
    ev = Trajectory.betaCorrection
      (BetaLaw.step (dynamics dataSet v)) (suc n)
    distance = absℝ
      (initialInverseSquare dataSet u -ℝ initialInverseSquare dataSet v)

    n≤K : n ℕ.≤ K
    n≤K = ℕP.≤-trans (ℕP.n≤1+n n) sn≤K

    n<K : n ℕ.< K
    n<K = sn≤K

    split = subAddDistributes bu eu bv ev
    triangle = absAddSubadditive (bu -ℝ bv) (eu -ℝ ev)
    ih = prefixDifferenceBound dataSet u v n n≤K
    shell = shellLipschitz dataSet u v n n<K
    added = +-mono-≤ ih shell
    distribute = *-distribʳ-+
      (sumReal (shellSensitivity dataSet) n)
      (shellSensitivity dataSet n) distance
  in
  transport≤
    (cong absℝ split)
    (sym distribute)
    (≤ℝ-trans triangle added)

record LiteralSameHistoryShootingData (TubePoint : Set) (K : Nat) : Set₁ where
  field
    shells : LiteralSameHistoryShellSensitivity TubePoint K
    renormalisationMap : TubePoint → TubePoint
    renormalisedInverseSquare : ℝ

    mapHasLiteralPrefixFormula : ∀ u →
      initialInverseSquare shells (renormalisationMap u)
      ≡ renormalisedInverseSquare +ℝ betaPrefixAt shells u K

open LiteralSameHistoryShootingData public

asBetaPrefixShootingMap :
  ∀ {TubePoint K} →
  LiteralSameHistoryShootingData TubePoint K → Shoot.BetaPrefixShootingMap TubePoint
asBetaPrefixShootingMap {K = K} dataSet = record
  { Shoot.BetaPrefixShootingMap.initialInverseSquare =
      initialInverseSquare (shells dataSet)
  ; Shoot.BetaPrefixShootingMap.renormalisationMap = renormalisationMap dataSet
  ; Shoot.BetaPrefixShootingMap.renormalisedInverseSquare =
      renormalisedInverseSquare dataSet
  ; Shoot.BetaPrefixShootingMap.cumulativeBeta =
      λ u → betaPrefixAt (shells dataSet) u K
  ; Shoot.BetaPrefixShootingMap.mapHasSourceFormula =
      mapHasLiteralPrefixFormula dataSet
  }

literalCumulativePrefixSensitivity :
  ∀ {TubePoint K}
    (dataSet : LiteralSameHistoryShootingData TubePoint K) u v →
  absℝ
    (Shoot.cumulativeBeta (asBetaPrefixShootingMap dataSet) u
      -ℝ Shoot.cumulativeBeta (asBetaPrefixShootingMap dataSet) v)
  ≤ℝ sumReal (shellSensitivity (shells dataSet)) K *ℝ
      absℝ
        (Shoot.initialInverseSquare (asBetaPrefixShootingMap dataSet) u
          -ℝ Shoot.initialInverseSquare (asBetaPrefixShootingMap dataSet) v)
literalCumulativePrefixSensitivity {K = K} dataSet =
  λ u v → prefixDifferenceBound (shells dataSet) u v K ℕP.≤-refl

a2ShellToCumulativeSensitivityLevel : ProofLevel
a2ShellToCumulativeSensitivityLevel = machineChecked

-- Remaining physical A2 source leaf: instantiate shellwise response coefficients
-- on pairs of literal generated CMP109 histories.  The existing mixed-Cauchy,
-- cubic-drift and irrelevant-response machinery supplies the cutoff-uniform
-- subunit sum; cumulative Lipschitzness itself is now finite algebra.
literalCMP109SameHistoryShellSensitivityLevel : ProofLevel
literalCMP109SameHistoryShellSensitivityLevel = conditional
