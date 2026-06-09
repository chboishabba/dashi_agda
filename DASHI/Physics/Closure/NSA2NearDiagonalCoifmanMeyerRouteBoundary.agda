module DASHI.Physics.Closure.NSA2NearDiagonalCoifmanMeyerRouteBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data A2Stage : Set where
  targetEstimateStage : A2Stage
  naiveL4BernsteinShortcutStage : A2Stage
  nearDiagonalSymbolLocalizationStage : A2Stage
  coifmanMeyerMultiplierStage : A2Stage
  lerayTriadicGeometryStage : A2Stage
  clayPromotionGuardStage : A2Stage

canonicalA2Stages : List A2Stage
canonicalA2Stages =
  targetEstimateStage
  ∷ naiveL4BernsteinShortcutStage
  ∷ nearDiagonalSymbolLocalizationStage
  ∷ coifmanMeyerMultiplierStage
  ∷ lerayTriadicGeometryStage
  ∷ clayPromotionGuardStage
  ∷ []

a2StageCount : Nat
a2StageCount = listLength canonicalA2Stages

a2StageCountIs6 : a2StageCount ≡ 6
a2StageCountIs6 = refl

data A2Blocker : Set where
  naiveL4RouteLosesNearDiagonalStructure : A2Blocker
  trueCoifmanMeyerEstimateMissing : A2Blocker
  lerayProjectorShellGeometryMissing : A2Blocker
  tight2minjkGainStillOpen : A2Blocker

canonicalA2Blockers : List A2Blocker
canonicalA2Blockers =
  naiveL4RouteLosesNearDiagonalStructure
  ∷ trueCoifmanMeyerEstimateMissing
  ∷ lerayProjectorShellGeometryMissing
  ∷ tight2minjkGainStillOpen
  ∷ []

data NSA2NearDiagonalCoifmanMeyerRouteBoundary : Set where
  mkNSA2NearDiagonalCoifmanMeyerRouteBoundary :
    NSA2NearDiagonalCoifmanMeyerRouteBoundary

canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary
canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary =
  mkNSA2NearDiagonalCoifmanMeyerRouteBoundary

boundaryRecorded :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → Bool
boundaryRecorded _ = true

tightTargetText :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → String
tightTargetText _ =
  "||P_j u · ∇P_k ω||_L2 <= C * 2^min(j,k) * ||P_j u||_L2 * ||P_k ω||_L2"

naiveShortcutRejected :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → Bool
naiveShortcutRejected _ = true

nearDiagonalCoifmanMeyerProved :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → Bool
nearDiagonalCoifmanMeyerProved _ = false

a2Proved :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → Bool
a2Proved _ = false

clayNavierStokesPromoted :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → Bool
clayNavierStokesPromoted _ = false

terminalPromotion :
  NSA2NearDiagonalCoifmanMeyerRouteBoundary → Bool
terminalPromotion _ = false

boundaryRecordedTrue :
  boundaryRecorded canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary ≡ true
boundaryRecordedTrue = refl

naiveShortcutRejectedTrue :
  naiveShortcutRejected canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary
  ≡ true
naiveShortcutRejectedTrue = refl

coifmanMeyerStillOpen :
  nearDiagonalCoifmanMeyerProved canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary
  ≡ false
coifmanMeyerStillOpen = refl

a2StillOpen :
  a2Proved canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary ≡ false
a2StillOpen = refl

clayPromotionStillFalse :
  clayNavierStokesPromoted canonicalNSA2NearDiagonalCoifmanMeyerRouteBoundary
  ≡ false
clayPromotionStillFalse = refl

