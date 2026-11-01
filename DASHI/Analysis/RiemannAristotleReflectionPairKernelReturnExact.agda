module DASHI.Analysis.RiemannAristotleReflectionPairKernelReturnExact where

------------------------------------------------------------------------
-- LEAN SOURCE RETURN: SIGNED OFF-ORDINATE REFLECTION-PAIR KERNEL
--
-- New Lean source owner:
--
--   LiteralWeilOffOrdinateReflectionPair.lean
--
-- It keeps functional-equation reflection pairs together before taking absolute
-- values.  For horizontal heights +/-a at the same ordinate gap delta it proves
-- the exact kernel identity
--
--   K(a,delta;u) + K(-a,delta;u)
--     = 4 g(u) cosh(a u) cos(delta u),
--
-- and the corresponding two-sample / projective-taper integral identities on
-- the literal zeta zero carrier, with the genuine common multiplicity.
--
-- This removes the odd-height sinh*sin term exactly and leaves an oscillatory
-- cosine kernel in the ordinate gap.  It is structurally stronger than the old
-- positive W(t) majorant, which took absolute values before exploiting this
-- reflection pairing.
--
-- The new Lean file is source-level in the current return: no pinned Lean
-- executable was available in the working container, so no new kernel receipt
-- is claimed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record ReflectionPairKernelReturn : Set where
  constructor reflection-pair-kernel-return
  field
    leanTheoremName : String
    sourceImplementedInLean : Bool
    sourceImplementedInLeanIsTrue : sourceImplementedInLean ≡ true
    machineCheckedInLeanForThisReturn : Bool
    machineCheckedInLeanForThisReturnIsFalse :
      machineCheckedInLeanForThisReturn ≡ false
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

    reflectionPairOddTermCancelledExactly : Bool
    reflectionPairOddTermCancelledExactlyIsTrue :
      reflectionPairOddTermCancelledExactly ≡ true
    remainingKernelOscillatoryInOrdinateGap : Bool
    remainingKernelOscillatoryInOrdinateGapIsTrue :
      remainingKernelOscillatoryInOrdinateGap ≡ true

    signedOrbitTailEstimateClosed : Bool
    signedOrbitTailEstimateClosedIsFalse : signedOrbitTailEstimateClosed ≡ false

    boundedReading : String

open ReflectionPairKernelReturn public

canonicalReflectionPairKernelReturn : ReflectionPairKernelReturn
canonicalReflectionPairKernelReturn =
  reflection-pair-kernel-return
    "LiteralWeilOffOrdinateReflectionPair.zeroConeValue_add_reflect_eq_integral"
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "The literal off-ordinate carrier can be paired by the functional-equation involution before majorization. The odd height component cancels exactly and the pair is a signed cosine transform in the ordinate gap. The remaining theorem is an orbit/shell estimate of the signed paired sum, not another absolute W(t) bound."
