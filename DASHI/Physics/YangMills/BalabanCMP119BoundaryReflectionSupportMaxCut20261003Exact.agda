{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119BoundaryReflectionSupportMaxCut20261003Exact where

------------------------------------------------------------------------
-- CMP119 B-SECTOR / OS-REFLECTION SUPPORT MAX-CUT
--
-- Source owner:
--   BalabanCMP119CMP122BoundaryReinjectionSourceExact
--
-- The published/source-backed BoundaryTermClass owns, for every (scale,X):
--   * the localized boundary terms B_k(X),
--   * common-domain analyticity,
--   * gauge invariance,
--   * exponential localization.
--
-- It does NOT own a spacetime support map for Polymer, a selected Euclidean
-- time reflection, or a theorem saying whether X lies in the positive half,
-- negative half, or crosses the OS plane.  Hence those facts cannot be
-- manufactured from exponential localization.
--
-- This file adds exactly the missing dictionary.  Once instantiated on the
-- literal CMP119 polymer carrier, all one-sided B terms are removed from the
-- nontrivial RP cut and only `crossing` polymers require a cross-plane kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119CMP122BoundaryReinjectionSourceExact as B

------------------------------------------------------------------------
-- Exact geometric classification consumed by OS reflection.
------------------------------------------------------------------------

data ReflectionSupportClass : Set where
  positiveHalf negativeHalf crossingPlane : ReflectionSupportClass

requiresCrossPlaneKernel : ReflectionSupportClass → Bool
requiresCrossPlaneKernel positiveHalf = false
requiresCrossPlaneKernel negativeHalf = false
requiresCrossPlaneKernel crossingPlane = true

reflectSupportClass : ReflectionSupportClass → ReflectionSupportClass
reflectSupportClass positiveHalf = negativeHalf
reflectSupportClass negativeHalf = positiveHalf
reflectSupportClass crossingPlane = crossingPlane

reflectSupportClassInvolutive : ∀ side →
  reflectSupportClass (reflectSupportClass side) ≡ side
reflectSupportClassInvolutive positiveHalf = refl
reflectSupportClassInvolutive negativeHalf = refl
reflectSupportClassInvolutive crossingPlane = refl

record CMP119BoundaryReflectionSupportDictionary
    {Scale Polymer BoundaryTerm AnalyticDomain : Set}
    (sourceClass :
      B.CMP119BoundaryTermClass
        Scale Polymer BoundaryTerm AnalyticDomain) : Set₁ where
  field
    -- SAME published polymer carrier; no replacement support datatype.
    reflectedPolymer : Scale → Polymer → Polymer
    supportClass : Scale → Polymer → ReflectionSupportClass

    reflectedPolymerInvolutive : ∀ scale polymer →
      reflectedPolymer scale (reflectedPolymer scale polymer) ≡ polymer

    supportClassReflectionLaw : ∀ scale polymer →
      supportClass scale (reflectedPolymer scale polymer) ≡
        reflectSupportClass (supportClass scale polymer)

    -- The source's localized B_k(X) terms remain attached to that same X.
    -- This field is the literal source/repository dictionary obligation: the
    -- Polymer index used by boundaryTerms is the physical support polymer
    -- being classified, not merely an unrelated label.
    BoundaryTermsUsePhysicalPolymerSupport : Scale → Polymer → Set
    boundaryTermsUsePhysicalPolymerSupport : ∀ scale polymer →
      BoundaryTermsUsePhysicalPolymerSupport scale polymer

open CMP119BoundaryReflectionSupportDictionary public

------------------------------------------------------------------------
-- Compiler facts: only crossing polymers survive as nontrivial B-RP leaves.
------------------------------------------------------------------------

boundaryPolymerNeedsCrossKernel :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    {sourceClass : B.CMP119BoundaryTermClass
      Scale Polymer BoundaryTerm AnalyticDomain} →
  CMP119BoundaryReflectionSupportDictionary sourceClass →
  Scale → Polymer → Bool
boundaryPolymerNeedsCrossKernel dictionary scale polymer =
  requiresCrossPlaneKernel (supportClass dictionary scale polymer)

positiveBoundaryPolymerIsHalfSupported :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    {sourceClass : B.CMP119BoundaryTermClass
      Scale Polymer BoundaryTerm AnalyticDomain}
    (dictionary : CMP119BoundaryReflectionSupportDictionary sourceClass)
    scale polymer →
  supportClass dictionary scale polymer ≡ positiveHalf →
  boundaryPolymerNeedsCrossKernel dictionary scale polymer ≡ false
positiveBoundaryPolymerIsHalfSupported dictionary scale polymer refl = refl

negativeBoundaryPolymerIsHalfSupported :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    {sourceClass : B.CMP119BoundaryTermClass
      Scale Polymer BoundaryTerm AnalyticDomain}
    (dictionary : CMP119BoundaryReflectionSupportDictionary sourceClass)
    scale polymer →
  supportClass dictionary scale polymer ≡ negativeHalf →
  boundaryPolymerNeedsCrossKernel dictionary scale polymer ≡ false
negativeBoundaryPolymerIsHalfSupported dictionary scale polymer refl = refl

crossingBoundaryPolymerIsPhysicalRPLeaf :
  ∀ {Scale Polymer BoundaryTerm AnalyticDomain}
    {sourceClass : B.CMP119BoundaryTermClass
      Scale Polymer BoundaryTerm AnalyticDomain}
    (dictionary : CMP119BoundaryReflectionSupportDictionary sourceClass)
    scale polymer →
  supportClass dictionary scale polymer ≡ crossingPlane →
  boundaryPolymerNeedsCrossKernel dictionary scale polymer ≡ true
crossingBoundaryPolymerIsPhysicalRPLeaf dictionary scale polymer refl = refl

------------------------------------------------------------------------
-- Status firewall.
------------------------------------------------------------------------

cmp119BoundaryReflectionClassificationCompilerLevel : ProofLevel
cmp119BoundaryReflectionClassificationCompilerLevel = machineChecked

-- The source citation does not supply this OS-time support dictionary.
cmp119BoundaryPhysicalReflectionSupportDictionaryLevel : ProofLevel
cmp119BoundaryPhysicalReflectionSupportDictionaryLevel = conditional

-- Even after support classification, each crossing B polymer still needs an
-- actual reflected-half/PSD kernel theorem.  Analyticity/localization is not it.
cmp119BoundaryCrossingKernelCertificateLevel : ProofLevel
cmp119BoundaryCrossingKernelCertificateLevel = conditional

boundaryAnalyticityImpliesReflectionPositivity : Bool
boundaryAnalyticityImpliesReflectionPositivity = false

boundaryAnalyticityImpliesReflectionPositivityIsFalse :
  boundaryAnalyticityImpliesReflectionPositivity ≡ false
boundaryAnalyticityImpliesReflectionPositivityIsFalse = refl
