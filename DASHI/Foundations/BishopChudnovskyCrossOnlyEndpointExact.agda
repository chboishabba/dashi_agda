module DASHI.Foundations.BishopChudnovskyCrossOnlyEndpointExact where

-- Source-written assembly, not kernel checked. Reuse the actual literal
-- interval, native totality, width, Machin budget and limit owners.
-- The universal common-value cross is an explicit input, not a postulate.
open import Agda.Builtin.Nat using (Nat)
import Real as R
import Sequence as S
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskyOverlapBudgetExact as B
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W

literalConvergenceFromCrossOnly :
  (c : ∀ k → O.Cross (O.window k)
    (Stage.qMachinStage k) (O.machinRadius k)) →
  S._ConvergesTo_ (λ k → R._⋆ (CH.midpoint (O.window k))) M.bishopMachinPi
literalConvergenceFromCrossOnly =
  B.literalConvergenceFromWidthAndCross W.literalWidthBound

literalConvergenceFromMembership :
  (lo : ∀ k → R._≤_ (R._⋆ (CH.lower (O.window k))) M.bishopMachinPi) →
  (hi : ∀ k → R._≤_ M.bishopMachinPi (R._⋆ (CH.upper (O.window k)))) →
  S._ConvergesTo_ (λ k → R._⋆ (CH.midpoint (O.window k))) M.bishopMachinPi
literalConvergenceFromMembership lo hi =
  literalConvergenceFromCrossOnly (λ k → O.nativeMembershipToCross k (lo k) (hi k))
