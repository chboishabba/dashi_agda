{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedTraceF2AuthorityCompilerTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedTraceF2AuthorityCompilerExact as P2

noFreshWardProof :
  P2.renormalizedTraceAnomalyIdentityNeedsFreshProof ≡ false
noFreshWardProof = refl

sameObjectWeldRemains :
  P2.remainingS2WorkIsSameObjectTraceF2AuthorityWeld ≡ true
sameObjectWeldRemains = refl

transportCompiler : P2.s2EqualityTransportCompilerLevel ≡ machineChecked
transportCompiler = refl
