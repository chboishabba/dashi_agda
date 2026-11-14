module DASHI.Moonshine.OggSSPKernelHeisenbergAdditiveIntertwinerExact where

------------------------------------------------------------------------
-- EXISTING HEISENBERG TRANSLATIONS <-> NEW F3 KERNEL ADDITION
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as Bridge
import DASHI.Moonshine.OggSSPTriadicKernelF3LinearExact as Linear

open Codec using ([]ᵥ; _∷ᵥ_)

-- H.increment and Linear addition by +1 are distinct definitions with the same
-- finite table, so pay the bridge by cases rather than pretending it is refl on
-- an unknown coordinate.
heisenbergIncrementIsLinearPlusOne :
  (x : Trit) → H.increment x ≡ Linear._⊕₃_ pos x
heisenbergIncrementIsLinearPlusOne neg = refl
heisenbergIncrementIsLinearPlusOne zer = refl
heisenbergIncrementIsLinearPlusOne pos = refl

basis6 : H.Axis6 → Linear.Kernel6
basis6 H.axis0 = pos ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ
basis6 H.axis1 = zer ∷ᵥ pos ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ
basis6 H.axis2 = zer ∷ᵥ zer ∷ᵥ pos ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ
basis6 H.axis3 = zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ pos ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ
basis6 H.axis4 = zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ pos ∷ᵥ zer ∷ᵥ []ᵥ
basis6 H.axis5 = zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ pos ∷ᵥ []ᵥ

kernelTranslate6 : H.Axis6 → Linear.Kernel6 → Linear.Kernel6
kernelTranslate6 axis kernel = Linear.addKernel (basis6 axis) kernel

heisenbergTranslationIntertwinesKernelAddition :
  (axis : H.Axis6) →
  (x : H.X6) →
  Bridge.x6ToKernel6 (H.translate axis x)
  ≡ kernelTranslate6 axis (Bridge.x6ToKernel6 x)
heisenbergTranslationIntertwinesKernelAddition H.axis0 (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite heisenbergIncrementIsLinearPlusOne a0 = refl
heisenbergTranslationIntertwinesKernelAddition H.axis1 (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite heisenbergIncrementIsLinearPlusOne a1 = refl
heisenbergTranslationIntertwinesKernelAddition H.axis2 (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite heisenbergIncrementIsLinearPlusOne a2 = refl
heisenbergTranslationIntertwinesKernelAddition H.axis3 (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite heisenbergIncrementIsLinearPlusOne a3 = refl
heisenbergTranslationIntertwinesKernelAddition H.axis4 (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite heisenbergIncrementIsLinearPlusOne a4 = refl
heisenbergTranslationIntertwinesKernelAddition H.axis5 (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite heisenbergIncrementIsLinearPlusOne a5 = refl

-- A canonical four-coordinate slice of X6 reuses the first four Heisenberg
-- translation axes.  This is an additive-action embedding only.
data Axis4 : Set where
  axis0 axis1 axis2 axis3 : Axis4

axis4To6 : Axis4 → H.Axis6
axis4To6 axis0 = H.axis0
axis4To6 axis1 = H.axis1
axis4To6 axis2 = H.axis2
axis4To6 axis3 = H.axis3

basis4 : Axis4 → Linear.Kernel4
basis4 axis0 = pos ∷ᵥ zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ
basis4 axis1 = zer ∷ᵥ pos ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ
basis4 axis2 = zer ∷ᵥ zer ∷ᵥ pos ∷ᵥ zer ∷ᵥ []ᵥ
basis4 axis3 = zer ∷ᵥ zer ∷ᵥ zer ∷ᵥ pos ∷ᵥ []ᵥ

embedK4InK6 : Linear.Kernel4 → Linear.Kernel6
embedK4InK6 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ) =
  a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ zer ∷ᵥ zer ∷ᵥ []ᵥ

kernelTranslate4 : Axis4 → Linear.Kernel4 → Linear.Kernel4
kernelTranslate4 axis kernel = Linear.addKernel (basis4 axis) kernel

k4TranslationIsRestrictedExistingHeisenbergTranslation :
  (axis : Axis4) →
  (kernel : Linear.Kernel4) →
  Bridge.x6ToKernel6
    (H.translate (axis4To6 axis)
      (Bridge.kernel6ToX6 (embedK4InK6 kernel)))
  ≡ embedK4InK6 (kernelTranslate4 axis kernel)
k4TranslationIsRestrictedExistingHeisenbergTranslation axis0 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ)
  rewrite heisenbergIncrementIsLinearPlusOne a = refl
k4TranslationIsRestrictedExistingHeisenbergTranslation axis1 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ)
  rewrite heisenbergIncrementIsLinearPlusOne b = refl
k4TranslationIsRestrictedExistingHeisenbergTranslation axis2 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ)
  rewrite heisenbergIncrementIsLinearPlusOne c = refl
k4TranslationIsRestrictedExistingHeisenbergTranslation axis3 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ []ᵥ)
  rewrite heisenbergIncrementIsLinearPlusOne d = refl

record KernelHeisenbergAdditiveIntertwinerBoundary : Set where
  constructor kernel-heisenberg-additive-intertwiner-boundary
  field
    x6Kernel6ChartReused : Bool
    sixExistingHeisenbergTranslationsIntertwined : Bool
    k4FirstFourTranslationRestrictionIntertwined : Bool
    additiveF3StructureNowIndependentlyActionAnchored : Bool
    fieldMultiplicationRecoveredFromHeisenbergTranslations : Bool
    frobeniusRecoveredFromHeisenbergTranslations : Bool

canonicalKernelHeisenbergAdditiveIntertwinerBoundary :
  KernelHeisenbergAdditiveIntertwinerBoundary
canonicalKernelHeisenbergAdditiveIntertwinerBoundary =
  kernel-heisenberg-additive-intertwiner-boundary
    true true true true false false
