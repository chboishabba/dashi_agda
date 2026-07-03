module DASHI.Bridges.LogicTlureyCategoricalBridge where

open import Agda.Builtin.Equality using (_≡_; refl)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
open import Agda.Builtin.Sigma using (Σ; _,_)

import Base369 as B
import LogicTlurey as LT

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.GrammarGeneratedCategory as GGC

----------------------------------------------------------------------
-- Bridge: LogicTlurey as a grammar-generated projection category.
--
--   Gamma_369(g) = LT.Stage
--   Proj_369     = stageProjectionCategory
--
-- Objects: TriTruth
-- Morphisms: TriTruth (tone transitions via triXor)
-- Id: tri-low (zero)
-- Composition: triXor
--
-- stageTone : Stage -> TriTruth is the atomic projection.
-- Fibre(tri-low) = {seed, overflow}  <-- first concrete residual.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- 1. Stage generates a concrete ProjectionCategory
----------------------------------------------------------------------

triXor-identityʳ : ∀ (t : B.TriTruth) → B.triXor t B.tri-low ≡ t
triXor-identityʳ B.tri-low  = refl
triXor-identityʳ B.tri-mid  = refl
triXor-identityʳ B.tri-high = refl

stageProjectionCategory : (s : LT.Stage) -> PC.ProjectionCategory
stageProjectionCategory s = record
  { Obj             = B.TriTruth
  ; Hom             = λ _ _ -> B.TriTruth
  ; id              = B.tri-low
  ; _∘_             = λ f g -> B.triXor f g
  ; id-left         = λ f -> B.triXor-identityˡ f
  ; id-right        = λ f -> triXor-identityʳ f
  ; assoc           = λ f g h -> sym (B.triXor-assoc f g h)
  ; categoryReading = "Pi_369(Stage): TriTruth with triXor composition."
  }

----------------------------------------------------------------------
-- 2. GrammarGeneratedCategory instance
----------------------------------------------------------------------

stageGrammarGeneratedCategory : GGC.GrammarGeneratedCategory
stageGrammarGeneratedCategory = record
  { Grammar        = LT.Stage
  ; 𝓟              = stageProjectionCategory
  ; grammarReading = "Gamma_369 = Stage"
  }

----------------------------------------------------------------------
-- 3. The stageTone fibre
----------------------------------------------------------------------

fibreStageTone : (o : B.TriTruth) -> Set
fibreStageTone o = Σ LT.Stage λ s -> LT.stageTone s ≡ o

fibreTriLow : Set
fibreTriLow = fibreStageTone B.tri-low

seedInFibre : fibreTriLow
seedInFibre = (LT.seed , refl)

overflowInFibre : fibreTriLow
overflowInFibre = (LT.overflow , refl)

----------------------------------------------------------------------
-- 4. Seed/overflow residual
----------------------------------------------------------------------

seedOverflowResidualRelation : Set
seedOverflowResidualRelation =
  Σ (B.TriTruth) λ o -> Σ (LT.stageTone LT.seed ≡ o) λ _ -> LT.stageTone LT.overflow ≡ o

seedOverflowSameFibre : seedOverflowResidualRelation
seedOverflowSameFibre = (B.tri-low , (refl , refl))

----------------------------------------------------------------------
-- 5. Homology: stable points under Stage -> TriTruth quotient
----------------------------------------------------------------------

data StageQuotientStable : Set where
  stableCounter   : StageQuotientStable
  stableResonance : StageQuotientStable

stageToneInjectiveStable : StageQuotientStable -> B.TriTruth
stageToneInjectiveStable stableCounter   = B.tri-mid
stageToneInjectiveStable stableResonance = B.tri-high
