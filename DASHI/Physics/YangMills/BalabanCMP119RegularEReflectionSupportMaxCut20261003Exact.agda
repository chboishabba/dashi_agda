{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEReflectionSupportMaxCut20261003Exact where

------------------------------------------------------------------------
-- CMP119 E-SECTOR / OS-REFLECTION SUPPORT MAX-CUT
--
-- The existing Section-2 owner already proves
--
--   E_k(A) = sum_X E_k(X,A)
--
-- on its literal selected `Component` list.  Therefore no new localization
-- theorem is needed for reflection positivity.  What is missing is the OS
-- geometry of those SAME components and the reflection law of their localized
-- activities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as E
import DASHI.Physics.YangMills.BalabanCMP119BoundaryReflectionSupportMaxCut20261003Exact as Support

record CMP119RegularEReflectionSupportDictionary
    {Density Background Volume Component : Set}
    {scale : Agda.Builtin.Nat.Nat} {density : Density}
    (form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density) : Set₁ where
  field
    reflectBackground : Background → Background
    reflectedComponent : Volume → Component → Component
    supportClass : Volume → Component → Support.ReflectionSupportClass

    reflectBackgroundInvolutive : ∀ background →
      reflectBackground (reflectBackground background) ≡ background

    reflectedComponentInvolutive : ∀ volume component →
      reflectedComponent volume (reflectedComponent volume component) ≡ component

    supportClassReflectionLaw : ∀ volume component →
      supportClass volume (reflectedComponent volume component) ≡
        Support.reflectSupportClass (supportClass volume component)

    -- Actual same-object localized E reflection law.  This is what turns a
    -- positive/negative component pair into reflected half-action factors.
    localizedRegularActivityReflectionLaw : ∀ volume component background →
      E.localizedRegularActivity form volume
        (reflectedComponent volume component) background
      ≡ E.localizedRegularActivity form volume component
          (reflectBackground background)

    -- The `Component` index in the source list really denotes the physical
    -- localized support being classified here.
    ComponentUsesPhysicalSupport : Volume → Component → Set
    componentUsesPhysicalSupport : ∀ volume component →
      ComponentUsesPhysicalSupport volume component

open CMP119RegularEReflectionSupportDictionary public

regularEComponentNeedsCrossKernel :
  ∀ {Density Background Volume Component scale density}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density} →
  CMP119RegularEReflectionSupportDictionary form →
  Volume → Component → Bool
regularEComponentNeedsCrossKernel dictionary volume component =
  Support.requiresCrossPlaneKernel
    (supportClass dictionary volume component)

positiveRegularEComponentIsHalfSupported :
  ∀ {Density Background Volume Component scale density}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density}
    (dictionary : CMP119RegularEReflectionSupportDictionary form)
    volume component →
  supportClass dictionary volume component ≡ Support.positiveHalf →
  regularEComponentNeedsCrossKernel dictionary volume component ≡ false
positiveRegularEComponentIsHalfSupported dictionary volume component refl = refl

negativeRegularEComponentIsHalfSupported :
  ∀ {Density Background Volume Component scale density}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density}
    (dictionary : CMP119RegularEReflectionSupportDictionary form)
    volume component →
  supportClass dictionary volume component ≡ Support.negativeHalf →
  regularEComponentNeedsCrossKernel dictionary volume component ≡ false
negativeRegularEComponentIsHalfSupported dictionary volume component refl = refl

crossingRegularEComponentIsPhysicalRPLeaf :
  ∀ {Density Background Volume Component scale density}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density}
    (dictionary : CMP119RegularEReflectionSupportDictionary form)
    volume component →
  supportClass dictionary volume component ≡ Support.crossingPlane →
  regularEComponentNeedsCrossKernel dictionary volume component ≡ true
crossingRegularEComponentIsPhysicalRPLeaf dictionary volume component refl = refl

regularEReflectionClassificationCompilerLevel : ProofLevel
regularEReflectionClassificationCompilerLevel = machineChecked

-- Source/localization exists; the selected OS support/reflection dictionary does not.
cmp119RegularEPhysicalReflectionDictionaryLevel : ProofLevel
cmp119RegularEPhysicalReflectionDictionaryLevel = conditional

cmp119RegularECrossingKernelCertificateLevel : ProofLevel
cmp119RegularECrossingKernelCertificateLevel = conditional
