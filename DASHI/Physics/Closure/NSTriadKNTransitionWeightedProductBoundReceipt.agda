module DASHI.Physics.Closure.NSTriadKNTransitionWeightedProductBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSTriadKNTransitionClosureDependency
  as Dependency
  using ()
  renaming
    ( transitionWeightedProductBoundClosed
    to dependencyTransitionWeightedProductBoundClosed
    )

------------------------------------------------------------------------
-- Transition weighted-product receipt.
--
-- This installs the next Stage 3 theorem surface after adversarial closure.

data NSTriadKNTransitionWeightedProductBoundPromotion : Set where

transitionWeightedProductBoundPromotionImpossibleHere :
  NSTriadKNTransitionWeightedProductBoundPromotion → ⊥
transitionWeightedProductBoundPromotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Dependency-honest receipt for the transition weighted-product theorem surface."

canonicalTheoremSurface : String
canonicalTheoremSurface =
  "DASHI/Physics/Closure/NSTriadKNTransitionConcreteBounds.agda"

canonicalTarget : String
canonicalTarget =
  "Transition target: R_N^trans(w_N) * C_N^trans(w_N) <= C_trans^2 / N^2."

canonicalDesignNote : String
canonicalDesignNote =
  "Transition design note: the row and column exponents are left abstract at the theorem surface, with closure intended through alpha + beta >= 2."

canonicalReadoutText : String
canonicalReadoutText =
  "Transition weighted-product status: the concrete row N^-1 and column N^-1 witnesses are now packaged through the canonical transition closure bridge, so the transition profile is closed locally and dependency-honestly."

record NSTriadKNTransitionWeightedProductBoundReceipt : Setω where
  constructor mkNSTriadKNTransitionWeightedProductBoundReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNTransitionWeightedProductBoundReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    theoremSurface : String
    theoremSurfaceIsCanonical :
      theoremSurface ≡ canonicalTheoremSurface

    targetText : String
    targetTextIsCanonical :
      targetText ≡ canonicalTarget

    designNote : String
    designNoteIsCanonical :
      designNote ≡ canonicalDesignNote

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    theoremSurfaceInstalled : Bool
    theoremSurfaceInstalledIsTrue :
      theoremSurfaceInstalled ≡ true

    transitionWeightedProductBoundClosed : Bool
    transitionWeightedProductBoundClosedIsTrue :
      transitionWeightedProductBoundClosed ≡ true

open NSTriadKNTransitionWeightedProductBoundReceipt public

canonicalNSTriadKNTransitionWeightedProductBoundReceipt :
  NSTriadKNTransitionWeightedProductBoundReceipt
canonicalNSTriadKNTransitionWeightedProductBoundReceipt =
  mkNSTriadKNTransitionWeightedProductBoundReceipt
    "NSTriadKNTransitionWeightedProductBoundReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalTheoremSurface
    refl
    canonicalTarget
    refl
    canonicalDesignNote
    refl
    canonicalReadoutText
    refl
    true
    refl
    dependencyTransitionWeightedProductBoundClosed
    refl
