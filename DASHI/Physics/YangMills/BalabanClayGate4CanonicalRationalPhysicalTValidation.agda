module DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as Canonical

canonicalPhysicalTSumIsPinned :
  Canonical.canonicalRationalPhysicalTConstructionLevel ≡ machineChecked
canonicalPhysicalTSumIsPinned = refl

canonicalReferenceFoldArithmeticIsPinned :
  Canonical.canonicalRationalReferenceFoldArithmeticLevel ≡ machineChecked
canonicalReferenceFoldArithmeticIsPinned = refl

rationalConeMeaningRemainsSemantic :
  Canonical.rationalReferenceConeMeaningLevel ≡ conditional
rationalConeMeaningRemainsSemantic = refl
