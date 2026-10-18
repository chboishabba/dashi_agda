{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsEvidenceLevelsTest where

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsEvidenceLevelsExact as Subject
import DASHI.Physics.YangMills.CompactLieProofLevel as Level

open import Agda.Builtin.Equality using (_≡_; refl)

a1Conditional : Subject.a1EvidenceLevel ≡ Level.conditional
a1Conditional = refl

a2Conditional : Subject.a2EvidenceLevel ≡ Level.conditional
a2Conditional = refl

b1Conditional : Subject.b1EvidenceLevel ≡ Level.conditional
b1Conditional = refl

b2Conditional : Subject.b2EvidenceLevel ≡ Level.conditional
b2Conditional = refl

cConditional : Subject.cEvidenceLevel ≡ Level.conditional
cConditional = refl
