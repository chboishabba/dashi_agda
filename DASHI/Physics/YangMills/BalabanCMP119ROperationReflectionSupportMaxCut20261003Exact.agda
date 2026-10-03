{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ROperationReflectionSupportMaxCut20261003Exact where

------------------------------------------------------------------------
-- CMP119/CMP122 R-OPERATION / OS-REFLECTION SUPPORT MAX-CUT
--
-- Equation1100RootedEntropyData retains the ACTUAL physical `Polymer` list in
-- every rooted shell, unlike the later scalar shell envelope.  Therefore the
-- OS support classification belongs here, before entropy/shell summation.
--
-- Important source boundary:
-- CMP122 Eq. (1.100) in the current formalization owns only rNorm and decay
-- bounds.  A norm bound cannot imply reflection positivity or a signed
-- reflected-action identity.  Hence this file separates:
--   (1) physical polymer support/reflection geometry;
--   (2) the still-missing actual localized R-value reflection/kernel theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation1100EntropyBudgetExact as R
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP119BoundaryReflectionSupportMaxCut20261003Exact as Support

record CMP119ROperationReflectionSupportDictionary
    {Scale Volume Root Polymer Boundary : Set}
    (dataSet : R.Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary) : Set₁ where
  field
    reflectedRoot : Root → Root
    reflectedPolymer : Scale → Volume → Polymer → Polymer
    supportClass : Scale → Volume → Polymer → Support.ReflectionSupportClass

    reflectedRootInvolutive : ∀ root →
      reflectedRoot (reflectedRoot root) ≡ root

    reflectedPolymerInvolutive : ∀ scale volume polymer →
      reflectedPolymer scale volume
        (reflectedPolymer scale volume polymer) ≡ polymer

    supportClassReflectionLaw : ∀ scale volume polymer →
      supportClass scale volume (reflectedPolymer scale volume polymer) ≡
        Support.reflectSupportClass (supportClass scale volume polymer)

    -- Reflection preserves the SAME rooted-shell depth.  This is the geometry
    -- needed to reuse the existing 2^{-depth} shell estimate without creating
    -- a second shell convention for OS reflection.
    reflectedPolymerStaysInSameDepthShell :
      ∀ scale volume root depth polymer →
      Shell._∈_ polymer
        (R.shellPolymers dataSet scale volume root depth) →
      Shell._∈_ (reflectedPolymer scale volume polymer)
        (R.shellPolymers dataSet scale volume (reflectedRoot root) depth)

    -- The source Polymer coordinate really denotes the physical support being
    -- classified, rather than a norm-only bookkeeping key.
    RPolymerUsesPhysicalSupport : Scale → Volume → Polymer → Set
    rPolymerUsesPhysicalSupport : ∀ scale volume polymer →
      RPolymerUsesPhysicalSupport scale volume polymer

open CMP119ROperationReflectionSupportDictionary public

rOperationPolymerNeedsCrossKernel :
  ∀ {Scale Volume Root Polymer Boundary}
    {dataSet : R.Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary} →
  CMP119ROperationReflectionSupportDictionary dataSet →
  Scale → Volume → Polymer → Bool
rOperationPolymerNeedsCrossKernel dictionary scale volume polymer =
  Support.requiresCrossPlaneKernel
    (supportClass dictionary scale volume polymer)

positiveROperationPolymerIsHalfSupported :
  ∀ {Scale Volume Root Polymer Boundary}
    {dataSet : R.Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary}
    (dictionary : CMP119ROperationReflectionSupportDictionary dataSet)
    scale volume polymer →
  supportClass dictionary scale volume polymer ≡ Support.positiveHalf →
  rOperationPolymerNeedsCrossKernel dictionary scale volume polymer ≡ false
positiveROperationPolymerIsHalfSupported dictionary scale volume polymer refl = refl

negativeROperationPolymerIsHalfSupported :
  ∀ {Scale Volume Root Polymer Boundary}
    {dataSet : R.Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary}
    (dictionary : CMP119ROperationReflectionSupportDictionary dataSet)
    scale volume polymer →
  supportClass dictionary scale volume polymer ≡ Support.negativeHalf →
  rOperationPolymerNeedsCrossKernel dictionary scale volume polymer ≡ false
negativeROperationPolymerIsHalfSupported dictionary scale volume polymer refl = refl

crossingROperationPolymerIsPhysicalRPLeaf :
  ∀ {Scale Volume Root Polymer Boundary}
    {dataSet : R.Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary}
    (dictionary : CMP119ROperationReflectionSupportDictionary dataSet)
    scale volume polymer →
  supportClass dictionary scale volume polymer ≡ Support.crossingPlane →
  rOperationPolymerNeedsCrossKernel dictionary scale volume polymer ≡ true
crossingROperationPolymerIsPhysicalRPLeaf dictionary scale volume polymer refl = refl

rOperationReflectionClassificationCompilerLevel : ProofLevel
rOperationReflectionClassificationCompilerLevel = machineChecked

-- Physical/source geometry on the literal CMP119/CMP122 polymer carrier.
cmp119ROperationPhysicalReflectionDictionaryLevel : ProofLevel
cmp119ROperationPhysicalReflectionDictionaryLevel = conditional

-- Eq. (1.100) is a NORM estimate.  The same-object localized R-value/action
-- reflection law needed to absorb one-sided terms is an independent theorem.
cmp119ROperationLocalizedValueReflectionLawLevel : ProofLevel
cmp119ROperationLocalizedValueReflectionLawLevel = conditional

-- Crossing R-polymers need a true cross-plane kernel certificate after the
-- actual localized value is attached; norm smallness is not such a certificate.
cmp119ROperationCrossingKernelCertificateLevel : ProofLevel
cmp119ROperationCrossingKernelCertificateLevel = conditional
