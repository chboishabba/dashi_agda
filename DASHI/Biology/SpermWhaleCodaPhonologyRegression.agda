module DASHI.Biology.SpermWhaleCodaPhonologyRegression where

-- Synthetic, finite Agda regression. No real corpus replicated here.
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.SpermWhaleCodaPhonologyExact as Whale

productFixture :
  Whale.source Whale.syntheticA ≡ Whale.source Whale.syntheticI
productFixture = Whale.sameSourceDifferentFilter

distinctQualities : Whale.aLike ≡ Whale.iLike → ⊥
distinctQualities = Whale.aAndIAreDifferentConstructors

analogyDoesNotTranslate :
  Whale.CrossSpeciesPhoneticAnalogy.semanticEquivalenceClaimed
    Whale.syntheticMandarinComparison ≡ false
analogyDoesNotTranslate =
  Whale.CrossSpeciesPhoneticAnalogy.noSemanticEquivalenceProof
    Whale.syntheticMandarinComparison

threeOriginalSourceRoots :
  Source.sourceCount (Source.AttributedSourceAtlas.sources Whale.originalSourceAtlas)
  ≡ suc (suc (suc zero))
threeOriginalSourceRoots = refl

semanticNonidentifiability :
  Query.AdequateFor Whale.acousticProjection Whale.syntheticSemantics
    Whale.putativeMeaning → ⊥
semanticNonidentifiability = Whale.soundAloneCannotDetermineMeaning
