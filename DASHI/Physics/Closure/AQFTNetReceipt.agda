module DASHI.Physics.Closure.AQFTNetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Haag-Kastler / locally covariant AQFT intake receipt.
--
-- Source surface: arXiv:2404.14510v2.
--
-- This module transcribes the paper's usable contract into DASHI as a
-- receipt surface:
--
--   * orthogonal-category locality / causality,
--   * AQFT isotony,
--   * time-slice localisation,
--   * stack/descent adequacy for the improved Haag-Kastler functors,
--   * the point reading of a locally covariant AQFT.
--
-- It deliberately does not construct a C*-algebra, Hilbert representation,
-- vacuum state, Born-rule adapter, interacting QFT, or GRQFT promotion.

data AQFTPromotionAuthorityToken : Set where

record AQFTNetReceipt : Setω where
  field
    source :
      String

    theoremPointReading :
      String

    theoremPointReading-v :
      theoremPointReading ≡
        "locally-covariant-AQFT-as-point-of-HK-2-functor"

    isotony :
      Bool

    isotony-v :
      isotony ≡ true

    causality :
      Bool

    causality-v :
      causality ≡ true

    timeSlice :
      Bool

    timeSlice-v :
      timeSlice ≡ true

    descentSatisfied :
      Bool

    descentSatisfied-v :
      descentSatisfied ≡ true

    improvedStackSurface :
      String

    improvedStackSurface-v :
      improvedStackSurface ≡
        "HK-rc-and-HK-rc-W-stack-descent-surface"

    exampleWitness :
      String

    exampleWitness-v :
      exampleWitness ≡
        "Klein-Gordon-field-point-Theorem-4.41"

    carrierConnection :
      String

    carrierConnection-v :
      carrierConnection ≡
        "local-algebra-is-carrier-fibre-isotony-is-transport-monotonicity"

    gnsVacuumAdapterStillOpen :
      Bool

    gnsVacuumAdapterStillOpen-v :
      gnsVacuumAdapterStillOpen ≡ true

    bornRuleAdapterStillOpen :
      Bool

    bornRuleAdapterStillOpen-v :
      bornRuleAdapterStillOpen ≡ true

    interactingQFTStillOpen :
      Bool

    interactingQFTStillOpen-v :
      interactingQFTStillOpen ≡ true

    noGRQFTPromotionFromThisReceipt :
      Bool

    noGRQFTPromotionFromThisReceipt-v :
      noGRQFTPromotionFromThisReceipt ≡ true

    noPromotionWithoutAuthority :
      AQFTPromotionAuthorityToken → ⊥

    governanceBoundary :
      List String

open AQFTNetReceipt public

canonicalAQFTNetReceipt :
  AQFTNetReceipt
canonicalAQFTNetReceipt =
  record
    { source =
        "arXiv:2404.14510v2 Haag-Kastler stacks"
    ; theoremPointReading =
        "locally-covariant-AQFT-as-point-of-HK-2-functor"
    ; theoremPointReading-v =
        refl
    ; isotony =
        true
    ; isotony-v =
        refl
    ; causality =
        true
    ; causality-v =
        refl
    ; timeSlice =
        true
    ; timeSlice-v =
        refl
    ; descentSatisfied =
        true
    ; descentSatisfied-v =
        refl
    ; improvedStackSurface =
        "HK-rc-and-HK-rc-W-stack-descent-surface"
    ; improvedStackSurface-v =
        refl
    ; exampleWitness =
        "Klein-Gordon-field-point-Theorem-4.41"
    ; exampleWitness-v =
        refl
    ; carrierConnection =
        "local-algebra-is-carrier-fibre-isotony-is-transport-monotonicity"
    ; carrierConnection-v =
        refl
    ; gnsVacuumAdapterStillOpen =
        true
    ; gnsVacuumAdapterStillOpen-v =
        refl
    ; bornRuleAdapterStillOpen =
        true
    ; bornRuleAdapterStillOpen-v =
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
    ; governanceBoundary =
        "AQFT net receipt records locality, isotony, time-slice, and descent contract surfaces"
        ∷ "locally covariant AQFT is staged as a point of the Haag-Kastler 2-functor"
        ∷ "Klein-Gordon example is cited as the first paper witness, not reconstructed here"
        ∷ "GNS/vacuum selection, Born rule, representation choice, and interacting QFT remain adapters or open obligations"
        ∷ "this receipt does not construct GRQFTClosurePromotionReceipt"
        ∷ []
    }
