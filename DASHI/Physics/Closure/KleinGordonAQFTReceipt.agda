module DASHI.Physics.Closure.KleinGordonAQFTReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AQFTNetReceipt as AQFT

------------------------------------------------------------------------
-- Klein-Gordon AQFT witness surface.
--
-- Source surface: arXiv:2404.14510v2, Theorem 4.41.
--
-- This receipt records the paper witness that the Klein-Gordon field defines
-- a point of the improved Haag-Kastler stacks.  It does not reconstruct the
-- C*-algebra net, select an interacting QFT, derive a vacuum, or promote a
-- Born-rule theorem.

data KleinGordonPromotionAuthorityToken : Set where

record KleinGordonAQFTReceipt : Setω where
  field
    source :
      String

    aqftNetReceipt :
      AQFT.AQFTNetReceipt

    theoremWitness :
      String

    theoremWitness-v :
      theoremWitness ≡
        "arXiv:2404.14510v2-Theorem-4.41-Klein-Gordon-point-of-HK-rc-and-HK-rc-W"

    isPointOfHKrc :
      Bool

    isPointOfHKrc-v :
      isPointOfHKrc ≡ true

    isPointOfHKrcW :
      Bool

    isPointOfHKrcW-v :
      isPointOfHKrcW ≡ true

    vacuumState :
      String

    vacuumState-v :
      vacuumState ≡
        "Minkowski-Poincare-invariant-vacuum-as-external-GNS-state"

    vacuumIsAdapter :
      Bool

    vacuumIsAdapter-v :
      vacuumIsAdapter ≡ true

    bornRule :
      String

    bornRule-v :
      bornRule ≡
        "p(a)=omega(a-star-a)-from-selected-state-on-local-algebra"

    bornRuleIsAdapter :
      Bool

    bornRuleIsAdapter-v :
      bornRuleIsAdapter ≡ true

    interactingQFTStillOpen :
      Bool

    interactingQFTStillOpen-v :
      interactingQFTStillOpen ≡ true

    noGRQFTPromotionFromThisReceipt :
      Bool

    noGRQFTPromotionFromThisReceipt-v :
      noGRQFTPromotionFromThisReceipt ≡ true

    noPromotionWithoutAuthority :
      KleinGordonPromotionAuthorityToken → ⊥

    witnessBoundary :
      List String

open KleinGordonAQFTReceipt public

canonicalKleinGordonAQFTReceipt :
  KleinGordonAQFTReceipt
canonicalKleinGordonAQFTReceipt =
  record
    { source =
        "arXiv:2404.14510v2 Haag-Kastler stacks Theorem 4.41"
    ; aqftNetReceipt =
        AQFT.canonicalAQFTNetReceipt
    ; theoremWitness =
        "arXiv:2404.14510v2-Theorem-4.41-Klein-Gordon-point-of-HK-rc-and-HK-rc-W"
    ; theoremWitness-v =
        refl
    ; isPointOfHKrc =
        true
    ; isPointOfHKrc-v =
        refl
    ; isPointOfHKrcW =
        true
    ; isPointOfHKrcW-v =
        refl
    ; vacuumState =
        "Minkowski-Poincare-invariant-vacuum-as-external-GNS-state"
    ; vacuumState-v =
        refl
    ; vacuumIsAdapter =
        true
    ; vacuumIsAdapter-v =
        refl
    ; bornRule =
        "p(a)=omega(a-star-a)-from-selected-state-on-local-algebra"
    ; bornRule-v =
        refl
    ; bornRuleIsAdapter =
        true
    ; bornRuleIsAdapter-v =
        refl
    ; interactingQFTStillOpen =
        true
    ; interactingQFTStillOpen-v =
        refl
    ; noGRQFTPromotionFromThisReceipt =
        true
    ; noGRQFTPromotionFromThisReceipt-v =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; witnessBoundary =
        "Klein-Gordon is recorded as the first free-field AQFT stack witness"
        ∷ "The local algebra net and descent proof are cited from the paper, not reconstructed here"
        ∷ "Vacuum selection remains an external GNS-state adapter"
        ∷ "Born-rule probability remains an adapter over a selected state"
        ∷ "This receipt does not construct interacting QFT, Standard Model QFT, or GRQFT promotion"
        ∷ []
    }
