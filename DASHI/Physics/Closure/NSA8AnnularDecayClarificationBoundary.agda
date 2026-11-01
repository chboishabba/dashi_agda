module DASHI.Physics.Closure.NSA8AnnularDecayClarificationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data A8Stage : Set where
  annularLocalizationStage : A8Stage
  cknAnnulusSplitStage : A8Stage
  contractionFactorStage : A8Stage
  iterativeDecayStage : A8Stage
  theoremClarificationStage : A8Stage
  clayPromotionGuardStage : A8Stage

canonicalA8Stages : List A8Stage
canonicalA8Stages =
  annularLocalizationStage
  ∷ cknAnnulusSplitStage
  ∷ contractionFactorStage
  ∷ iterativeDecayStage
  ∷ theoremClarificationStage
  ∷ clayPromotionGuardStage
  ∷ []

a8StageCount : Nat
a8StageCount = listLength canonicalA8Stages

a8StageCountIs6 : a8StageCount ≡ 6
a8StageCountIs6 = refl

data A8KeyRow : Set where
  recursionRow : A8KeyRow
  qThetaMRow : A8KeyRow
  qStrictlyLessThanOneRow : A8KeyRow
  dyadicIterationToZeroRow : A8KeyRow

canonicalA8Rows : List A8KeyRow
canonicalA8Rows =
  recursionRow ∷ qThetaMRow ∷ qStrictlyLessThanOneRow ∷ dyadicIterationToZeroRow ∷ []

data NSA8AnnularDecayClarificationBoundary : Set where
  mkNSA8AnnularDecayClarificationBoundary :
    NSA8AnnularDecayClarificationBoundary

canonicalNSA8AnnularDecayClarificationBoundary :
  NSA8AnnularDecayClarificationBoundary
canonicalNSA8AnnularDecayClarificationBoundary =
  mkNSA8AnnularDecayClarificationBoundary

boundaryRecorded :
  NSA8AnnularDecayClarificationBoundary → Bool
boundaryRecorded _ = true

recursionText :
  NSA8AnnularDecayClarificationBoundary → String
recursionText _ =
  "D_{theta r} <= q(theta,M) D_r + C(R,M) D_r^(1+alpha)"

qText :
  NSA8AnnularDecayClarificationBoundary → String
qText _ =
  "q(theta,M) = (theta^2 + C M) / (1 + C M) < 1"

iterativeDecayText :
  NSA8AnnularDecayClarificationBoundary → String
iterativeDecayText _ =
  "D_{theta^k r} -> 0 under admissible recursion and sufficiently small initial defect"

receiptOnlyClarification :
  NSA8AnnularDecayClarificationBoundary → Bool
receiptOnlyClarification _ = true

a8Proved :
  NSA8AnnularDecayClarificationBoundary → Bool
a8Proved _ = false

a9Proved :
  NSA8AnnularDecayClarificationBoundary → Bool
a9Proved _ = false

clayNavierStokesPromoted :
  NSA8AnnularDecayClarificationBoundary → Bool
clayNavierStokesPromoted _ = false

terminalPromotion :
  NSA8AnnularDecayClarificationBoundary → Bool
terminalPromotion _ = false

boundaryRecordedTrue :
  boundaryRecorded canonicalNSA8AnnularDecayClarificationBoundary ≡ true
boundaryRecordedTrue = refl

receiptOnlyClarificationTrue :
  receiptOnlyClarification canonicalNSA8AnnularDecayClarificationBoundary ≡ true
receiptOnlyClarificationTrue = refl

a8StillOpen :
  a8Proved canonicalNSA8AnnularDecayClarificationBoundary ≡ false
a8StillOpen = refl

clayPromotionStillFalse :
  clayNavierStokesPromoted canonicalNSA8AnnularDecayClarificationBoundary
  ≡ false
clayPromotionStillFalse = refl

