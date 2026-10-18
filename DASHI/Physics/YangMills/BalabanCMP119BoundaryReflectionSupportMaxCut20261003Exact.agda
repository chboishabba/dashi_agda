{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119BoundaryReflectionSupportMaxCut20261003Exact where

------------------------------------------------------------------------
-- CMP119 B-SECTOR / OS-REFLECTION SUPPORT MAX-CUT
--
-- Source owner:
--   BalabanCMP119CMP122BoundaryReinjectionSourceExact
--
-- The source-backed BoundaryTermClass owns localized B_k(X), analyticity,
-- gauge invariance and exponential localization.  It does NOT own spacetime
-- support relative to the selected OS plane or reflection pairing of the
-- localized boundary expressions.  Both are therefore explicit physical
-- dictionary leaves here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map)

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
    -- SAME published carriers; no replacement polymer/action datatype.
    reflectedPolymer : Scale → Polymer → Polymer
    reflectedBoundaryTerm : BoundaryTerm → BoundaryTerm
    supportClass : Scale → Polymer → ReflectionSupportClass

    reflectedPolymerInvolutive : ∀ scale polymer →
      reflectedPolymer scale (reflectedPolymer scale polymer) ≡ polymer

    reflectedBoundaryTermInvolutive : ∀ term →
      reflectedBoundaryTerm (reflectedBoundaryTerm term) ≡ term

    supportClassReflectionLaw : ∀ scale polymer →
      supportClass scale (reflectedPolymer scale polymer) ≡
        reflectSupportClass (supportClass scale polymer)

    -- The actual localized source list on reflected X is the reflected list of
    -- the source terms on X.  This is the reflection pairing needed before a
    -- one-sided polymer can be absorbed into the two half actions.
    boundaryTermsReflectionLaw : ∀ scale polymer →
      B.boundaryTerms sourceClass scale (reflectedPolymer scale polymer)
      ≡ map reflectedBoundaryTerm
          (B.boundaryTerms sourceClass scale polymer)

    -- The source's Polymer index is the physical support being classified,
    -- rather than an unrelated bookkeeping label.
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

-- CMP119/CMP122 source citation currently supplies neither the selected OS
-- support map nor this exact reflected-term list equality.
cmp119BoundaryPhysicalReflectionSupportDictionaryLevel : ProofLevel
cmp119BoundaryPhysicalReflectionSupportDictionaryLevel = conditional

cmp119BoundaryPhysicalTermReflectionPairingLevel : ProofLevel
cmp119BoundaryPhysicalTermReflectionPairingLevel = conditional

-- Crossing B polymers still need a genuine PSD/reflected-half certificate.
cmp119BoundaryCrossingKernelCertificateLevel : ProofLevel
cmp119BoundaryCrossingKernelCertificateLevel = conditional

boundaryAnalyticityImpliesReflectionPositivity : Bool
boundaryAnalyticityImpliesReflectionPositivity = false

boundaryAnalyticityImpliesReflectionPositivityIsFalse :
  boundaryAnalyticityImpliesReflectionPositivity ≡ false
boundaryAnalyticityImpliesReflectionPositivityIsFalse = refl
