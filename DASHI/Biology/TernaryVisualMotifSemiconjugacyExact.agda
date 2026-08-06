module DASHI.Biology.TernaryVisualMotifSemiconjugacyExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.VisualMotifTransitionOperator as Motif

------------------------------------------------------------------------
-- Exact bridge between the balanced-ternary phase carrier and the recurrent
-- visual-motif operator.  This is a semiconjugacy of finite transition
-- systems; it does not identify Yijing line values with visual content.

ternaryPhaseStep : Triadic.KernelTrit → Triadic.KernelTrit
ternaryPhaseStep Triadic.negativeTrit = Triadic.zeroTrit
ternaryPhaseStep Triadic.zeroTrit = Triadic.positiveTrit
ternaryPhaseStep Triadic.positiveTrit = Triadic.negativeTrit

motifOfTrit : Triadic.KernelTrit → Motif.MotifState
motifOfTrit Triadic.negativeTrit = Motif.latticeMotif
motifOfTrit Triadic.zeroTrit = Motif.tunnelMotif
motifOfTrit Triadic.positiveTrit = Motif.faceMotif

ternaryMotifSemiconjugacy :
  (t : Triadic.KernelTrit) →
  motifOfTrit (ternaryPhaseStep t)
  ≡
  Motif.motifStep Motif.reweightedMotifRegime (motifOfTrit t)
ternaryMotifSemiconjugacy Triadic.negativeTrit = refl
ternaryMotifSemiconjugacy Triadic.zeroTrit = refl
ternaryMotifSemiconjugacy Triadic.positiveTrit = refl

ternaryPhasePeriodThree :
  (t : Triadic.KernelTrit) →
  ternaryPhaseStep
    (ternaryPhaseStep
      (ternaryPhaseStep t))
  ≡
  t
ternaryPhasePeriodThree Triadic.negativeTrit = refl
ternaryPhasePeriodThree Triadic.zeroTrit = refl
ternaryPhasePeriodThree Triadic.positiveTrit = refl

motifPeriodInheritedFromTernary :
  (t : Triadic.KernelTrit) →
  Motif.motifStep Motif.reweightedMotifRegime
    (Motif.motifStep Motif.reweightedMotifRegime
      (Motif.motifStep Motif.reweightedMotifRegime (motifOfTrit t)))
  ≡
  motifOfTrit t
motifPeriodInheritedFromTernary Triadic.negativeTrit = refl
motifPeriodInheritedFromTernary Triadic.zeroTrit = refl
motifPeriodInheritedFromTernary Triadic.positiveTrit = refl

motifEncodingIsInjective :
  (x y : Triadic.KernelTrit) →
  motifOfTrit x ≡ motifOfTrit y →
  x ≡ y
motifEncodingIsInjective Triadic.negativeTrit Triadic.negativeTrit proof = refl
motifEncodingIsInjective Triadic.negativeTrit Triadic.zeroTrit ()
motifEncodingIsInjective Triadic.negativeTrit Triadic.positiveTrit ()
motifEncodingIsInjective Triadic.zeroTrit Triadic.negativeTrit ()
motifEncodingIsInjective Triadic.zeroTrit Triadic.zeroTrit proof = refl
motifEncodingIsInjective Triadic.zeroTrit Triadic.positiveTrit ()
motifEncodingIsInjective Triadic.positiveTrit Triadic.negativeTrit ()
motifEncodingIsInjective Triadic.positiveTrit Triadic.zeroTrit ()
motifEncodingIsInjective Triadic.positiveTrit Triadic.positiveTrit proof = refl

record TernaryVisualSemiconjugacyBoundary : Set where
  constructor ternaryVisualSemiconjugacyBoundary
  field
    ternaryPhaseIsVisualMeaning : Bool
    ternaryPhaseIsVisualMeaningIsFalse :
      ternaryPhaseIsVisualMeaning ≡ false

    sharedPeriodImpliesSharedMechanism : Bool
    sharedPeriodImpliesSharedMechanismIsFalse :
      sharedPeriodImpliesSharedMechanism ≡ false

canonicalTernaryVisualSemiconjugacyBoundary :
  TernaryVisualSemiconjugacyBoundary
canonicalTernaryVisualSemiconjugacyBoundary =
  ternaryVisualSemiconjugacyBoundary false refl false refl
