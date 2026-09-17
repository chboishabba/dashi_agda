module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemExact as Owner

boundary : Owner.AdKChemicalSystemBoundary
boundary = Owner.canonicalAdKChemicalSystemBoundary

reactionRetained : Owner.adenylateKinaseReaction ≡ Owner.adenylateKinaseReaction
reactionRetained = refl

atpPubChemRetained : Owner.atpPubChemCID ≡ "5957"
atpPubChemRetained = refl

ampPubChemRetained : Owner.ampPubChemCID ≡ "6083"
ampPubChemRetained = refl

adpPubChemRetained : Owner.adpPubChemCID ≡ "6022"
adpPubChemRetained = refl

ap5aPubChemRetained : Owner.ap5aPubChemCID ≡ "53477724"
ap5aPubChemRetained = refl

magnesiumPubChemRetained : Owner.magnesiumPubChemCID ≡ "888"
magnesiumPubChemRetained = refl
