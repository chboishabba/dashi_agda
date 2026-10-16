module DASHI.Physics.CondensedMatter.MATBGTHFSourceFaithfulDiscretizationObligationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.CondensedMatter.MATBGTHFSourceFaithfulDiscretizationObligationExact as D

continuum-measure-is-source-paid : D.continuumNormalizationSourcePaid D.canonicalTHFContinuousMeasureReceipt ≡ true
continuum-measure-is-source-paid = refl

discrete-mesh-remains-open : D.reciprocalMeshSpecified D.currentTHFDiscreteProducerObligation ≡ false
discrete-mesh-remains-open = refl

cutoff-remains-open : D.ultravioletCutoffSpecified D.currentTHFDiscreteProducerObligation ≡ false
cutoff-remains-open = refl

v-y-identity-remains-open : D.sourceIdentityVEqualsYSpecified D.currentTHFDiscreteProducerObligation ≡ false
v-y-identity-remains-open = refl

continuous-measure-does-not-pick-mesh : D.continuumMeasureDoesNotSelectDiscreteMesh D.canonicalTHFDiscretizationBoundary ≡ true
continuous-measure-does-not-pick-mesh = refl
