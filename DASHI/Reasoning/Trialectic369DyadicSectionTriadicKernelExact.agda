module DASHI.Reasoning.Trialectic369DyadicSectionTriadicKernelExact where

------------------------------------------------------------------------
-- TRIALECTIC DYADIC LOCAL SECTIONS <-> CANONICAL TRIADIC KERNEL 4
--
-- DASHI CONTRIBUTION
--
-- The original trialectic descent owner already defines:
--
--   U_AB = (AA, AB, BA, BB)
--   U_BC = (BB, BC, CB, CC)
--   U_CA = (CC, CA, AC, AA)
--
-- Each local chart is therefore literally four SSP trits.  Reusing the
-- canonical SSPTrit <-> Trit bridge and TriadicPAdicCodec.Kernel 4 gives exact
-- two-sided recharts:
--
--   ABSection <-> Kernel 4
--   BCSection <-> Kernel 4
--   CASection <-> Kernel 4.
--
-- Hence the four-trit carrier isolated by the balanced-ternary arithmetic is
-- already a same-shape object in the pre-RH trialectic cover.  This file does
-- not claim that the RH coefficient is caused by these local sections.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as KernelBridge
import DASHI.Analysis.RiemannQuarticPuncturedKernel4EnumerationExact as Punctured
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- 1. ABSection <-> Kernel 4.
------------------------------------------------------------------------

abToKernel4 : Descent.ABSection -> KernelBridge.Kernel4
abToKernel4 section =
  SSP.toTrit (Descent.aaAB section) ∷ᵥ
  SSP.toTrit (Descent.ab section) ∷ᵥ
  SSP.toTrit (Descent.ba section) ∷ᵥ
  SSP.toTrit (Descent.bbAB section) ∷ᵥ
  []ᵥ

kernel4ToAB : KernelBridge.Kernel4 -> Descent.ABSection
kernel4ToAB
  (aa ∷ᵥ ab ∷ᵥ ba ∷ᵥ bb ∷ᵥ []ᵥ) =
  Descent.ab-section
    (SSP.fromTrit aa)
    (SSP.fromTrit ab)
    (SSP.fromTrit ba)
    (SSP.fromTrit bb)

abKernelRoundTrip :
  (section : Descent.ABSection) ->
  kernel4ToAB (abToKernel4 section) ≡ section
abKernelRoundTrip
  (Descent.ab-section aa ab ba bb)
  rewrite SSP.fromTrit-toTrit aa
        | SSP.fromTrit-toTrit ab
        | SSP.fromTrit-toTrit ba
        | SSP.fromTrit-toTrit bb = refl

kernelABRoundTrip :
  (kernel : KernelBridge.Kernel4) ->
  abToKernel4 (kernel4ToAB kernel) ≡ kernel
kernelABRoundTrip
  (aa ∷ᵥ ab ∷ᵥ ba ∷ᵥ bb ∷ᵥ []ᵥ)
  rewrite SSP.toTrit-fromTrit aa
        | SSP.toTrit-fromTrit ab
        | SSP.toTrit-fromTrit ba
        | SSP.toTrit-fromTrit bb = refl

------------------------------------------------------------------------
-- 2. BCSection <-> Kernel 4.
------------------------------------------------------------------------

bcToKernel4 : Descent.BCSection -> KernelBridge.Kernel4
bcToKernel4 section =
  SSP.toTrit (Descent.bbBC section) ∷ᵥ
  SSP.toTrit (Descent.bc section) ∷ᵥ
  SSP.toTrit (Descent.cb section) ∷ᵥ
  SSP.toTrit (Descent.ccBC section) ∷ᵥ
  []ᵥ

kernel4ToBC : KernelBridge.Kernel4 -> Descent.BCSection
kernel4ToBC
  (bb ∷ᵥ bc ∷ᵥ cb ∷ᵥ cc ∷ᵥ []ᵥ) =
  Descent.bc-section
    (SSP.fromTrit bb)
    (SSP.fromTrit bc)
    (SSP.fromTrit cb)
    (SSP.fromTrit cc)

bcKernelRoundTrip :
  (section : Descent.BCSection) ->
  kernel4ToBC (bcToKernel4 section) ≡ section
bcKernelRoundTrip
  (Descent.bc-section bb bc cb cc)
  rewrite SSP.fromTrit-toTrit bb
        | SSP.fromTrit-toTrit bc
        | SSP.fromTrit-toTrit cb
        | SSP.fromTrit-toTrit cc = refl

kernelBCRoundTrip :
  (kernel : KernelBridge.Kernel4) ->
  bcToKernel4 (kernel4ToBC kernel) ≡ kernel
kernelBCRoundTrip
  (bb ∷ᵥ bc ∷ᵥ cb ∷ᵥ cc ∷ᵥ []ᵥ)
  rewrite SSP.toTrit-fromTrit bb
        | SSP.toTrit-fromTrit bc
        | SSP.toTrit-fromTrit cb
        | SSP.toTrit-fromTrit cc = refl

------------------------------------------------------------------------
-- 3. CASection <-> Kernel 4.
------------------------------------------------------------------------

caToKernel4 : Descent.CASection -> KernelBridge.Kernel4
caToKernel4 section =
  SSP.toTrit (Descent.ccCA section) ∷ᵥ
  SSP.toTrit (Descent.ca section) ∷ᵥ
  SSP.toTrit (Descent.ac section) ∷ᵥ
  SSP.toTrit (Descent.aaCA section) ∷ᵥ
  []ᵥ

kernel4ToCA : KernelBridge.Kernel4 -> Descent.CASection
kernel4ToCA
  (cc ∷ᵥ ca ∷ᵥ ac ∷ᵥ aa ∷ᵥ []ᵥ) =
  Descent.ca-section
    (SSP.fromTrit cc)
    (SSP.fromTrit ca)
    (SSP.fromTrit ac)
    (SSP.fromTrit aa)

caKernelRoundTrip :
  (section : Descent.CASection) ->
  kernel4ToCA (caToKernel4 section) ≡ section
caKernelRoundTrip
  (Descent.ca-section cc ca ac aa)
  rewrite SSP.fromTrit-toTrit cc
        | SSP.fromTrit-toTrit ca
        | SSP.fromTrit-toTrit ac
        | SSP.fromTrit-toTrit aa = refl

kernelCARoundTrip :
  (kernel : KernelBridge.Kernel4) ->
  caToKernel4 (kernel4ToCA kernel) ≡ kernel
kernelCARoundTrip
  (cc ∷ᵥ ca ∷ᵥ ac ∷ᵥ aa ∷ᵥ []ᵥ)
  rewrite SSP.toTrit-fromTrit cc
        | SSP.toTrit-fromTrit ca
        | SSP.toTrit-fromTrit ac
        | SSP.toTrit-fromTrit aa = refl

------------------------------------------------------------------------
-- 4. Distinguished zero locals and support puncture.
------------------------------------------------------------------------

zeroAB : Descent.ABSection
zeroAB =
  kernel4ToAB KernelBridge.zeroKernel4

zeroBC : Descent.BCSection
zeroBC =
  kernel4ToBC KernelBridge.zeroKernel4

zeroCA : Descent.CASection
zeroCA =
  kernel4ToCA KernelBridge.zeroKernel4

abSupport : Descent.ABSection -> Bool
abSupport =
  KernelBridge.kernel4Support ∘ abToKernel4

bcSupport : Descent.BCSection -> Bool
bcSupport =
  KernelBridge.kernel4Support ∘ bcToKernel4

caSupport : Descent.CASection -> Bool
caSupport =
  KernelBridge.kernel4Support ∘ caToKernel4

zeroABHasNoSupport : abSupport zeroAB ≡ false
zeroABHasNoSupport = refl

zeroBCHasNoSupport : bcSupport zeroBC ≡ false
zeroBCHasNoSupport = refl

zeroCAHasNoSupport : caSupport zeroCA ≡ false
zeroCAHasNoSupport = refl

------------------------------------------------------------------------
-- 5. Concrete AB local enumeration inherited from Kernel 4.
--
-- BC and CA have exact two-sided Kernel-4 charts above, so the same finite
-- cardinality follows structurally.  We package AB explicitly as a concrete
-- local-section enumeration to make the 81/80 local-chart interpretation
-- executable rather than merely numeric.
------------------------------------------------------------------------

abEnumeration : List Descent.ABSection
abEnumeration =
  Data.List.Base.map kernel4ToAB Punctured.kernel4Enumeration

kernel4ToABInjective :
  {left right : KernelBridge.Kernel4} ->
  kernel4ToAB left ≡ kernel4ToAB right ->
  left ≡ right
kernel4ToABInjective {left} {right} equality =
  trans
    (sym (kernelABRoundTrip left))
    (trans
      (cong abToKernel4 equality)
      (kernelABRoundTrip right))

abEnumerationUnique : Unique abEnumeration
abEnumerationUnique =
  UniqueP.map⁺
    kernel4ToABInjective
    Punctured.kernel4EnumerationUnique

abEnumerationLengthIs81 :
  Reindex.listLength abEnumeration ≡ 81
abEnumerationLengthIs81 =
  trans
    (Card.mapLength kernel4ToAB Punctured.kernel4Enumeration)
    Punctured.kernel4EnumerationLengthIs81

puncturedABEnumeration : List Descent.ABSection
puncturedABEnumeration =
  Data.List.Base.map kernel4ToAB
    Punctured.puncturedKernel4Enumeration

puncturedABEnumerationUnique : Unique puncturedABEnumeration
puncturedABEnumerationUnique =
  UniqueP.map⁺
    kernel4ToABInjective
    Punctured.puncturedKernel4EnumerationUnique

puncturedABEnumerationLengthIs80 :
  Reindex.listLength puncturedABEnumeration ≡ 80
puncturedABEnumerationLengthIs80 =
  trans
    (Card.mapLength
      kernel4ToAB
      Punctured.puncturedKernel4Enumeration)
    Punctured.puncturedKernel4EnumerationLengthIs80

------------------------------------------------------------------------
-- 6. Firewall.
------------------------------------------------------------------------

data DyadicKernel4ChartCreatesRHMechanism : Set where
data EveryLocalPunctureIsForcedByGrothendieckDescent : Set where
data FourTritChartMakesAllThreeLocalsDefinitionallyIdentical : Set where

dyadicKernel4ChartDoesNotCreateRHMechanism :
  DyadicKernel4ChartCreatesRHMechanism -> ⊥
dyadicKernel4ChartDoesNotCreateRHMechanism ()

localPunctureNotForcedByDescentAlone :
  EveryLocalPunctureIsForcedByGrothendieckDescent -> ⊥
localPunctureNotForcedByDescentAlone ()

rechartDoesNotCollapseLocalRoles :
  FourTritChartMakesAllThreeLocalsDefinitionallyIdentical -> ⊥
rechartDoesNotCollapseLocalRoles ()

record Trialectic369DyadicSectionTriadicKernelBoundary : Set where
  constructor trialectic-369-dyadic-section-triadic-kernel-boundary
  field
    abSectionKernel4Exact : Bool
    bcSectionKernel4Exact : Bool
    caSectionKernel4Exact : Bool
    distinguishedZeroLocalsExplicit : Bool
    supportPunctureTransportedToLocals : Bool
    concreteABLocalCount81 : Bool
    concretePuncturedABLocalCount80 : Bool
    rhMechanismClaimed : Bool
    punctureForcedByDescentClaimed : Bool

canonicalTrialectic369DyadicSectionTriadicKernelBoundary :
  Trialectic369DyadicSectionTriadicKernelBoundary
canonicalTrialectic369DyadicSectionTriadicKernelBoundary =
  trialectic-369-dyadic-section-triadic-kernel-boundary
    true true true true true true true
    false false
