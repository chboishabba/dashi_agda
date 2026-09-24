module DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalReferenceAlgebraValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalReferenceAlgebraExact as Algebra

canonicalReferenceAlgebraClosed :
  Algebra.canonicalReferenceAlgebraLevel ≡ machineChecked
canonicalReferenceAlgebraClosed = refl

canonicalPositiveFoldAlgebraClosed :
  Algebra.canonicalPositiveFoldAlgebraLevel ≡ machineChecked
canonicalPositiveFoldAlgebraClosed = refl

canonicalPositiveMassInterpretationClosed :
  Algebra.canonicalRationalPositiveMassInterpretationLevel ≡ machineChecked
canonicalPositiveMassInterpretationClosed = refl
