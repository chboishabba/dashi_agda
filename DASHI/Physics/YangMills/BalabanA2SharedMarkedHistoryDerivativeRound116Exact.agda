{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2SharedMarkedHistoryDerivativeRound116Exact where

------------------------------------------------------------------------
-- ROUND116 A2 BIDI SHORTCUT: USE THE EXISTING DIFFERENTIATED BETA MARK DIRECTLY
--
-- Backward target: Row A only needs a finite propagated-history derivative
-- constant L_history to add to the already-owned local mixed-Cauchy derivative.
--
-- Forward source: `BalabanSharedMarkedAnalyticShellExact` already has a beta mark
-- for separation in preceding RG history and proves
--
--   betaHistoryPartial(K) <= (1/2) C_beta
--
-- from the same differentiated CMP116 analytic/localization mechanism used for
-- the Hessian and composite marks.
--
-- Therefore, if the literal generated-history derivative is identified with
-- that beta-mark response on the same source family, there is no need to derive
-- A2 through a second response-kernel recurrence.  Round113's
--   r_(n+1) <= R s_n + (1/2) r_n
-- route remains a valid fallback/producer decomposition, but the direct marked
-- derivative route is strictly shorter whenever the source-native beta mark is
-- the actual history derivative consumed by shooting.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact as Mixed
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as Cauchy
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as Ward

mulNN : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
mulNN {a} {b} aNN bNN =
  let
    instance
      aNonnegative : NonNegative a
      aNonnegative = ℚ.nonNegative aNN
      bNonnegative : NonNegative b
      bNonnegative = ℚ.nonNegative bNN
  in
  ℚP.nonNegative⁻¹ (a * b)

record LiteralBetaHistoryMarkedDerivative : Set₁ where
  field
    Scale Volume Root : Set
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    -- Literal derivative/sensitivity partial sums on the generated trajectory.
    -- The only physical same-object seam in this shortcut is that they are the
    -- existing source-native CMP116 beta-mark partial sums.
    literalHistoryDerivativePartial : Nat → ℚ
    literalHistoryDerivativeIsBetaMark : ∀ K →
      literalHistoryDerivativePartial K
      ≡ Shared.betaHistoryPartial shared scale volume root K

open LiteralBetaHistoryMarkedDerivative public

historyDerivativeConstant : LiteralBetaHistoryMarkedDerivative → ℚ
historyDerivativeConstant dataSet =
  StepV.half * Shared.betaAnalyticConstant (shared dataSet)

historyDerivativeConstantNonnegative :
  (dataSet : LiteralBetaHistoryMarkedDerivative) →
  0ℚ ≤ historyDerivativeConstant dataSet
historyDerivativeConstantNonnegative dataSet =
  mulNN
    (ℚP.<⇒≤ StepV.etaGapPositive)
    (Shared.markedConstantNonnegative (shared dataSet) Shared.betaMark)

literalHistoryDerivativePartialBound :
  (dataSet : LiteralBetaHistoryMarkedDerivative) →
  ∀ K →
  literalHistoryDerivativePartial dataSet K
  ≤ historyDerivativeConstant dataSet
literalHistoryDerivativePartialBound dataSet K =
  subst
    (λ left → left ≤ historyDerivativeConstant dataSet)
    (literalHistoryDerivativeIsBetaMark dataSet K)
    (Shared.betaHistoryPartialBelowHalfAnalyticConstant
      (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet) K)

rowACauchySourceFromMarkedHistory :
  Mixed.MixedInteractionCauchyData →
  LiteralBetaHistoryMarkedDerivative →
  Cauchy.RowACauchySourceConstants
rowACauchySourceFromMarkedHistory mixed history = record
  { Cauchy.RowACauchySourceConstants.gaussianFloor = Ward.wardGaussianFloor
  ; Cauchy.RowACauchySourceConstants.gaussianFloorPositive =
      Ward.wardGaussianFloorPositive
  ; Cauchy.RowACauchySourceConstants.mixedInteraction = mixed
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstant =
      historyDerivativeConstant history
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstantNonnegative =
      historyDerivativeConstantNonnegative history
  }

markedHistoryCanonicalGamma :
  Mixed.MixedInteractionCauchyData →
  LiteralBetaHistoryMarkedDerivative → ℚ
markedHistoryCanonicalGamma mixed history =
  Cauchy.canonicalSourceGamma (rowACauchySourceFromMarkedHistory mixed history)

markedHistoryCanonicalGammaPositive :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (history : LiteralBetaHistoryMarkedDerivative) →
  0ℚ < markedHistoryCanonicalGamma mixed history
markedHistoryCanonicalGammaPositive mixed history =
  Cauchy.canonicalSourceGammaPositive
    (rowACauchySourceFromMarkedHistory mixed history)

markedHistoryCanonicalGammaPaysFullDerivativeGate :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (history : LiteralBetaHistoryMarkedDerivative) →
  (Cauchy.sourceInteractionConstant
      (rowACauchySourceFromMarkedHistory mixed history)
    + Cauchy.sourceDerivativeConstant
      (rowACauchySourceFromMarkedHistory mixed history))
    * markedHistoryCanonicalGamma mixed history
  < Ward.wardGaussianFloor
markedHistoryCanonicalGammaPaysFullDerivativeGate mixed history =
  Cauchy.canonicalSourceGammaPaysCombinedGate
    (rowACauchySourceFromMarkedHistory mixed history)

a2SharedMarkedHistoryDerivativeCompilerLevel : ProofLevel
a2SharedMarkedHistoryDerivativeCompilerLevel = machineChecked

a2SharedMarkedHistoryToCanonicalGammaLevel : ProofLevel
a2SharedMarkedHistoryToCanonicalGammaLevel = machineChecked

-- Highest-alpha source seam for this shorter route:
-- instantiate `LiteralBetaHistoryMarkedDerivative` by the SAME generated
-- CMP109/CMP119 trajectory and prove that the literal preceding-history
-- derivative partial sum is the beta-mark response already localized by CMP116.
-- Once that equality is supplied, L_history <= C_beta/2 and the canonical full
-- Row-A derivative/small-coupling gate are automatic.
--
-- If this same-object identification fails because the current beta mark is only
-- an absolute activity tail rather than the differentiated shooting response,
-- fall back to Round113's explicit response-kernel/quartic-injection route.
literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel : ProofLevel
literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel = conditional
