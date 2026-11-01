module DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentEnvelopeSplitRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact as Split

splitCompilerClosed :
  Split.r571PhysicalEnvelopeSplitCompilerClosed ≡ true
splitCompilerClosed = refl

radialEnvelopeStillAnalytic :
  Split.r571RadialTaylorEnvelopeConstructedHere ≡ false
radialEnvelopeStillAnalytic = refl

stateEnvelopeStillAnalytic :
  Split.r571StateDerivativeEnvelopeConstructedHere ≡ false
stateEnvelopeStillAnalytic = refl

noUniformProducerPromoted :
  Split.r571ScopedEnvelopeSplitClosesUniformProducer ≡ false
noUniformProducerPromoted = refl
