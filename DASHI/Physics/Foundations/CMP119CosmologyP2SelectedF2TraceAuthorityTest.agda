{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2SelectedF2TraceAuthorityTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP2SelectedF2TraceAuthorityExact as S

independentLocalCF2ScalarRetired :
  S.independentLocalCF2ScalarIdentificationRequired ≡ false
independentLocalCF2ScalarRetired = refl

selectedF2AuthorityWeldRemains :
  S.selectedF2ToRenormalizedF2SameObjectRequired ≡ true
selectedF2AuthorityWeldRemains = refl
