{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsEvidenceLevelsTest where

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsEvidenceLevelsExact as Subject
import DASHI.Physics.YangMills.CompactLieProofLevel as Level

open import Agda.Builtin.Equality using (_≡_; refl)

allFiveRemainConditional :
  Subject.a1EvidenceLevel ≡ Level.conditional
  × Subject.a2EvidenceLevel ≡ Level.conditional
  × Subject.b1EvidenceLevel ≡ Level.conditional
  × Subject.b2EvidenceLevel ≡ Level.conditional
  × Subject.cEvidenceLevel ≡ Level.conditional
allFiveRemainConditional = refl , refl , refl , refl , refl
