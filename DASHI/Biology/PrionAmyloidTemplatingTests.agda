module DASHI.Biology.PrionAmyloidTemplatingTests where

open import DASHI.Core.Prelude
open import DASHI.Biology.PrionAmyloidTemplating

------------------------------------------------------------------------
-- Closed computation witnesses for the local conformational kernel
------------------------------------------------------------------------

native-native : template native native ≡ native
native-native = refl

native-amyloid : template native amyloid ≡ amyloid
native-amyloid = refl

amyloid-native : template amyloid native ≡ amyloid
amyloid-native = refl

amyloid-amyloid : template amyloid amyloid ≡ amyloid
amyloid-amyloid = refl

-- Repeated exposure to the same seed reaches a fixed point after one local
-- conversion.  This is a statement about the two-state model, not a claim
-- about biological timescales or organism-level disease.
localFixedPoint : (seed substrate : Conformation) →
  template seed (template seed substrate) ≡ template seed substrate
localFixedPoint = templateIdempotent

------------------------------------------------------------------------
-- The type boundary prevents invalid implication shortcuts
------------------------------------------------------------------------

-- Amyloid evidence alone contains no field producing Transmissible evidence.
-- Likewise, PrionSystem contains no theorem that a single exposure is lethal.
-- Those claims require independent witnesses in PrionSystem and
-- PathologyModel / SingleExposureNonLethal respectively.

amyloidIsNotDefinitionallyPrion : Set₁
amyloidIsNotDefinitionallyPrion =
  {Protein Host : Set} → AmyloidEvidence Protein → PrionSystem Protein Host → Set
