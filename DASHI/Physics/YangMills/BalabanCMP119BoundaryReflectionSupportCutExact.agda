{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119BoundaryReflectionSupportCutExact where

------------------------------------------------------------------------
-- CMP119 B-SECTOR / OS SUPPORT CUT
--
-- CMP119 Sect. 2 and the CMP122 reinjection step attach boundary activities
-- to an explicit source polymer X.  The repository now also has an executable
-- OS-time classification for the literal periodic block-polymer carrier.
--
-- This file composes those two facts at the type level: whenever the source
-- Polymer parameter is instantiated by the literal `PeriodicPolymer n`, every
-- listed B_k(X) term inherits the positive-only / negative-only / crossing
-- class of that SAME X.
--
-- What is *not* proved here is the physical representation theorem identifying
-- Balaban's published polymer X with this periodic carrier.  Nor is a crossing
-- activity declared PSD merely because it is localized/analytic/gauge
-- invariant.  Those remain explicit source leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP119CMP122BoundaryReinjectionSourceExact as Boundary
import DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact as Geometry

------------------------------------------------------------------------
-- Source-listed term on one literal periodic polymer.
------------------------------------------------------------------------

BoundaryTermOnPolymer :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain) →
  Scale → Periodic.PeriodicPolymer n → BoundaryTerm → Set
BoundaryTermOnPolymer sourceClass scale polymer term =
  term ∈ Boundary.boundaryTerms sourceClass scale polymer

BoundaryTermPositiveOnly :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain) →
  Nat → Scale → Periodic.PeriodicPolymer n → BoundaryTerm → Set
BoundaryTermPositiveOnly sourceClass cut scale polymer term =
  BoundaryTermOnPolymer sourceClass scale polymer term ×
  Geometry.polymerPositiveOnly cut polymer

BoundaryTermNegativeOnly :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain) →
  Nat → Scale → Periodic.PeriodicPolymer n → BoundaryTerm → Set
BoundaryTermNegativeOnly sourceClass cut scale polymer term =
  BoundaryTermOnPolymer sourceClass scale polymer term ×
  Geometry.polymerNegativeOnly cut polymer

BoundaryTermCrossing :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain) →
  Nat → Scale → Periodic.PeriodicPolymer n → BoundaryTerm → Set
BoundaryTermCrossing sourceClass cut scale polymer term =
  BoundaryTermOnPolymer sourceClass scale polymer term ×
  Geometry.polymerCrossesReflectionCut cut polymer

BoundaryTermEmptySupport :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain) →
  Nat → Scale → Periodic.PeriodicPolymer n → BoundaryTerm → Set
BoundaryTermEmptySupport sourceClass cut scale polymer term =
  BoundaryTermOnPolymer sourceClass scale polymer term ×
  Geometry.polymerEmptyAtReflectionCut cut polymer

------------------------------------------------------------------------
-- Every source-listed term has exactly the class of its own source polymer.
-- The result is exhaustive without introducing a second support carrier.
------------------------------------------------------------------------

boundaryTermSupportClassCases :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain)
    cut scale polymer term →
  BoundaryTermOnPolymer sourceClass scale polymer term →
  BoundaryTermPositiveOnly sourceClass cut scale polymer term
  ⊎ BoundaryTermNegativeOnly sourceClass cut scale polymer term
  ⊎ BoundaryTermCrossing sourceClass cut scale polymer term
  ⊎ BoundaryTermEmptySupport sourceClass cut scale polymer term
boundaryTermSupportClassCases sourceClass cut scale polymer term listed
  with Geometry.classifyPeriodicPolymerAtCut cut polymer
... | Geometry.positiveOnly = inj₁ (listed , refl)
... | Geometry.negativeOnly = inj₂ (inj₁ (listed , refl))
... | Geometry.crossingSupport = inj₂ (inj₂ (inj₁ (listed , refl)))
... | Geometry.emptySupport = inj₂ (inj₂ (inj₂ (listed , refl)))

------------------------------------------------------------------------
-- Source facts remain available on each geometrically classified term.
------------------------------------------------------------------------

boundaryCrossingTermAnalytic :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain)
    cut scale polymer term →
  BoundaryTermCrossing sourceClass cut scale polymer term →
  Boundary.AnalyticOn sourceClass term
    (Boundary.domain sourceClass scale polymer)
boundaryCrossingTermAnalytic sourceClass cut scale polymer term crossing =
  Boundary.analyticOnInductiveDomain sourceClass scale polymer term

boundaryCrossingTermGaugeInvariant :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain)
    cut scale polymer term →
  BoundaryTermCrossing sourceClass cut scale polymer term →
  Boundary.GaugeInvariant sourceClass term
boundaryCrossingTermGaugeInvariant sourceClass cut scale polymer term crossing =
  Boundary.gaugeInvariant sourceClass scale polymer term

boundaryCrossingTermExponentiallyLocalized :
  ∀ {n Scale BoundaryTerm AnalyticDomain}
    (sourceClass : Boundary.CMP119BoundaryTermClass
      Scale (Periodic.PeriodicPolymer n) BoundaryTerm AnalyticDomain)
    cut scale polymer term →
  BoundaryTermCrossing sourceClass cut scale polymer term →
  Boundary.ExponentiallyLocalized sourceClass scale polymer term
boundaryCrossingTermExponentiallyLocalized sourceClass cut scale polymer term crossing =
  Boundary.exponentiallyLocalized sourceClass scale polymer term

------------------------------------------------------------------------
-- Status firewall.
------------------------------------------------------------------------

boundaryReflectionSupportCutCompilerLevel : ProofLevel
boundaryReflectionSupportCutCompilerLevel = machineChecked

-- The published/source Polymer parameter still has to be identified with the
-- literal periodic block polymer used above.
cmp119BoundaryPublishedPolymerToPeriodicCarrierLevel : ProofLevel
cmp119BoundaryPublishedPolymerToPeriodicCarrierLevel = conditional

-- For positive/negative-only polymers, prove the selected source activity is
-- transported by the SAME OS reflection.  Geometry alone does not imply it.
cmp119BoundaryOneSidedActivityReflectionLevel : ProofLevel
cmp119BoundaryOneSidedActivityReflectionLevel = conditional

-- For crossing polymers, construct the actual cross-plane kernel and prove it
-- PSD (or produce a counterexample).  Analyticity/localization is insufficient.
cmp119BoundaryCrossingKernelRPLevel : ProofLevel
cmp119BoundaryCrossingKernelRPLevel = conditional
