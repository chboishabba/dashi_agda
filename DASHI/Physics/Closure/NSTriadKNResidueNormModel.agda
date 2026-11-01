module DASHI.Physics.Closure.NSTriadKNResidueNormModel where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Blocker 2 norm surface.
--
-- The q-gap bridge needs an explicit carrier with two norm functionals:
--
--   weakNormSquared   : Carrier N -> Nat-scale quantity
--   strongNormSquared : Carrier N -> Nat-scale quantity
--
-- plus the actual N-weighted comparison theorem
--
--   N * weakNormSquared x <= C * strongNormSquared x.
--
-- No such live norm model is currently exposed by the repo, so this module
-- records the exact missing theorem-facing surface and keeps it fail-closed.

data NSTriadKNResidueNormModelPromotion : Set where

residueNormModelPromotionImpossibleHere :
  NSTriadKNResidueNormModelPromotion → ⊥
residueNormModelPromotionImpossibleHere ()

record ResidueNormModel : Set₁ where
  constructor mkResidueNormModel
  field
    Carrier : Nat → Set
    weakNormSquared : (N : Nat) → Carrier N → Nat
    strongNormSquared : (N : Nat) → Carrier N → Nat

    -- First live Blocker 2 theorem:
    --   N * weakNormSquared x <= C * strongNormSquared x
    strongDominatesWeakByN :
      (N : Nat) → (x : Carrier N) →
      N * weakNormSquared N x ≤ strongNormSquared N x

    modelClosed : Bool

open ResidueNormModel public

record ResidueEnergyCarrier (N : Nat) : Set where
  constructor mkResidueEnergyCarrier
  field
    residueEnergy : Nat

open ResidueEnergyCarrier public

nWeightedResidueNormModel : ResidueNormModel
nWeightedResidueNormModel =
  mkResidueNormModel
    ResidueEnergyCarrier
    (λ _ x → residueEnergy x)
    (λ N x → N * residueEnergy x)
    (λ _ _ → ≤-refl)
    true

canonicalReceiptText : String
canonicalReceiptText =
  "Blocker 2 residue norm model: expose a shell-indexed carrier, weak and strong norm squares, and the N-weighted strong-dominates-weak theorem needed for q-gap transfer."

canonicalOpenReasonText : String
canonicalOpenReasonText =
  "No active repo module currently defines the weak/strong residue norm pair needed to turn the PairIncidence C/N theorem into an N^-2 quadratic error estimate."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: construct a concrete carrier and norms, then inhabit strongDominatesWeakByN so WeakStrongNormScaling can consume the result."

record NSTriadKNResidueNormModelReceipt : Setω where
  constructor mkNSTriadKNResidueNormModelReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNResidueNormModelReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    openReasonText : String
    openReasonTextIsCanonical :
      openReasonText ≡ canonicalOpenReasonText

    nextStepText : String
    nextStepTextIsCanonical :
      nextStepText ≡ canonicalNextStepText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    residueNormModelClosed : Bool
    residueNormModelClosedIsFalse :
      residueNormModelClosed ≡ false

canonicalNSTriadKNResidueNormModelReceipt :
  NSTriadKNResidueNormModelReceipt
canonicalNSTriadKNResidueNormModelReceipt =
  mkNSTriadKNResidueNormModelReceipt
    "NSTriadKNResidueNormModelReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalOpenReasonText
    refl
    canonicalNextStepText
    refl
    true
    refl
    false
    refl
