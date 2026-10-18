module DASHI.Analysis.RiemannConstructiveRealPlattTrudgianWindowExact where

------------------------------------------------------------------------
-- STANDARD ℚ -> SELECTED CONSTRUCTIVE-REAL RATIONAL COORDINATE
--
-- RiemannPlattTrudgianLocatedHeightArithmeticExact proves the numerical window
-- in Agda's canonical normalized rationals.  ConstructiveCompleteRealPackage
-- intentionally leaves its rational carrier abstract.  This file exposes the
-- least-privilege same-object seam between those two rational presentations and
-- then compiles the exact PT window used by the located R3★ route.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base as Rational using (ℚ; _/_; _<_)

import DASHI.Analysis.ConstructiveCompleteRealPackageExact as Package
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannPlattTrudgianLocatedHeightArithmeticExact as Arithmetic
import DASHI.Analysis.RiemannAnalyticLocatedVerifiedHeightExact as Located

natAsStandardRational : Nat → ℚ
natAsStandardRational n = Int.+ n / 1

record StandardRationalCoordinate
    (realPackage : Package.ConstructiveCompleteRealPackage) : Set₁ where
  private
    rationals = Package.rationals realPackage
  field
    decode :
      ℚ → Capability.Q rationals

    decodeStrictOrder :
      ∀ {left right} →
      left < right →
      Capability._<Q_ rationals (decode left) (decode right)

open StandardRationalCoordinate public

compileCanonicalLocatedHeightWindow :
  ∀ {realPackage} →
  StandardRationalCoordinate realPackage →
  Located.RationalLocatedHeightWindow realPackage
compileCanonicalLocatedHeightWindow {realPackage} coordinate = record
  { Located.highStartRational =
      decode coordinate Arithmetic.candidateHalfHeight
  ; Located.publishedHeightRational =
      decode coordinate Arithmetic.publishedVerifiedHeightRational
  ; Located.highStartBelowPublishedHeightRational =
      decodeStrictOrder coordinate Arithmetic.candidateHalfBelowPublishedHeight
  ; Located.encodeNatAsRational =
      λ n → decode coordinate (natAsStandardRational n)
  ; Located.publishedHeightRationalIsPlattTrudgianHeight =
      refl
  }

record ConstructiveRealPlattTrudgianWindowBoundary : Set where
  constructor constructive-real-platt-trudgian-window-boundary
  field
    numericalThresholdProofOwnedInStandardRationals : Bool
    selectedRealMayUseAbstractRationalPresentation : Bool
    oneStandardRationalCoordinateRequired : Bool
    exactLocatedHeightWindowCompilesAfterCoordinate : Bool
    realCarrierAttachmentPaidHere : Bool
    publishedLowTheoremPaidHere : Bool
    rhDerivedHere : Bool

open ConstructiveRealPlattTrudgianWindowBoundary public

canonicalConstructiveRealPlattTrudgianWindowBoundary :
  ConstructiveRealPlattTrudgianWindowBoundary
canonicalConstructiveRealPlattTrudgianWindowBoundary =
  constructive-real-platt-trudgian-window-boundary
    true true true true false false false
