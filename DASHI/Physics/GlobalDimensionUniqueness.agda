module DASHI.Physics.GlobalDimensionUniqueness where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.DimensionBoundAssumptions as DBA

record TargetFingerprint (m : Nat) : Set where
  field
    profile : DBA.ShellOrbitProfile m
    orbitCount-3 : DBA.ShellOrbitProfile.orbitCount profile ≡ 3
    top1-24      : DBA.ShellOrbitProfile.top1 profile ≡ 24
    top2-6       : DBA.ShellOrbitProfile.top2 profile ≡ 6
    top3-2       : DBA.ShellOrbitProfile.top3 profile ≡ 2

record GlobalOrbitClassification : Set₁ where
  field
    fingerprint : (m : Nat) → DBA.ShellOrbitProfile m
    soundTarget : ∀ {m} (t : TargetFingerprint m) →
      TargetFingerprint.profile t ≡ fingerprint m
    targetUniqueDimension : ∀ {m} → TargetFingerprint m → m ≡ 4

record GlobalDimensionClosure : Set₁ where
  field
    classification : GlobalOrbitClassification
    signatureAt4 : Nat × Nat
    signatureAt4-is-1+3 : signatureAt4 ≡ (1 , 3)

  globalDimensionUnique : ∀ {m} → TargetFingerprint m → m ≡ 4
  globalDimensionUnique =
    GlobalOrbitClassification.targetUniqueDimension classification

open GlobalDimensionClosure public
