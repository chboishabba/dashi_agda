module DASHI.Foundations.Base369BinaryTernaryRefinement where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.String using (String)

open import Base369 using (TriTruth; HexTruth; NonaryTruth)
open import DASHI.Foundations.Base369CirclePhase using
  ( Phase18
  ; triToHex
  ; triToNonary
  ; hexTo18
  ; nonaryTo18
  ; tri-common-refinement-commutes
  )

------------------------------------------------------------------------
-- The 2^a 3^b resolution lattice.
--
-- A resolution is identified by independent binary and ternary depths.
-- The carrier count is 2^a * 3^b.  Keeping the two depths as coordinates
-- makes the binary/ternary refinement square commute definitionally.

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

record Resolution23 : Set where
  constructor resolution23
  field
    binaryDepth : Nat
    ternaryDepth : Nat

open Resolution23 public

sectorCount : Resolution23 → Nat
sectorCount r =
  pow 2 (binaryDepth r) * pow 3 (ternaryDepth r)

binaryRefine : Resolution23 → Resolution23
binaryRefine (resolution23 a b) = resolution23 (suc a) b

ternaryRefine : Resolution23 → Resolution23
ternaryRefine (resolution23 a b) = resolution23 a (suc b)

binary-ternary-refinement-commutes :
  (r : Resolution23) →
  binaryRefine (ternaryRefine r) ≡
  ternaryRefine (binaryRefine r)
binary-ternary-refinement-commutes (resolution23 a b) = refl

data RefinementAxis : Set where
  binaryAxis : RefinementAxis
  ternaryAxis : RefinementAxis

refineAlong : RefinementAxis → Resolution23 → Resolution23
refineAlong binaryAxis = binaryRefine
refineAlong ternaryAxis = ternaryRefine

refinementAxesCommute :
  (x y : RefinementAxis) →
  (r : Resolution23) →
  refineAlong x (refineAlong y r) ≡
  refineAlong y (refineAlong x r)
refinementAxesCommute binaryAxis binaryAxis r = refl
refinementAxesCommute binaryAxis ternaryAxis r =
  binary-ternary-refinement-commutes r
refinementAxesCommute ternaryAxis binaryAxis (resolution23 a b) =
  refl
refinementAxesCommute ternaryAxis ternaryAxis r = refl

------------------------------------------------------------------------
-- Canonical Base369 phase resolutions.

phase3Resolution : Resolution23
phase3Resolution = resolution23 0 1

phase6Resolution : Resolution23
phase6Resolution = resolution23 1 1

phase9Resolution : Resolution23
phase9Resolution = resolution23 0 2

phase18Resolution : Resolution23
phase18Resolution = resolution23 1 2

phase3-sector-count : sectorCount phase3Resolution ≡ 3
phase3-sector-count = refl

phase6-sector-count : sectorCount phase6Resolution ≡ 6
phase6-sector-count = refl

phase9-sector-count : sectorCount phase9Resolution ≡ 9
phase9-sector-count = refl

phase18-sector-count : sectorCount phase18Resolution ≡ 18
phase18-sector-count = refl

phase3-binary-refines-to-phase6 :
  binaryRefine phase3Resolution ≡ phase6Resolution
phase3-binary-refines-to-phase6 = refl

phase3-ternary-refines-to-phase9 :
  ternaryRefine phase3Resolution ≡ phase9Resolution
phase3-ternary-refines-to-phase9 = refl

phase6-ternary-refines-to-phase18 :
  ternaryRefine phase6Resolution ≡ phase18Resolution
phase6-ternary-refines-to-phase18 = refl

phase9-binary-refines-to-phase18 :
  binaryRefine phase9Resolution ≡ phase18Resolution
phase9-binary-refines-to-phase18 = refl

------------------------------------------------------------------------
-- Concrete carrier diamond already realised by Base369CirclePhase.

circlePhaseRefinementDiamond :
  (t : TriTruth) →
  hexTo18 (triToHex t) ≡
  nonaryTo18 (triToNonary t)
circlePhaseRefinementDiamond = tri-common-refinement-commutes

record BinaryTernaryRefinementReceipt : Set₁ where
  constructor mkBinaryTernaryRefinementReceipt
  field
    coarseCarrier : Set
    binaryCarrier : Set
    ternaryCarrier : Set
    commonCarrier : Set
    coarseResolution : Resolution23
    binaryResolution : Resolution23
    ternaryResolution : Resolution23
    commonResolution : Resolution23
    binaryThenTernaryAgrees :
      binaryRefine (ternaryRefine coarseResolution) ≡ commonResolution
    ternaryThenBinaryAgrees :
      ternaryRefine (binaryRefine coarseResolution) ≡ commonResolution
    interpretation : String
    universalPhysicalPrivilegePromoted : Bool
    universalPhysicalPrivilegePromotedIsFalse :
      universalPhysicalPrivilegePromoted ≡ false

base369BinaryTernaryRefinementReceipt :
  BinaryTernaryRefinementReceipt
base369BinaryTernaryRefinementReceipt =
  mkBinaryTernaryRefinementReceipt
    TriTruth
    HexTruth
    NonaryTruth
    Phase18
    phase3Resolution
    phase6Resolution
    phase9Resolution
    phase18Resolution
    refl
    refl
    "C3 is the common coarse phase grid; C6 is its binary/polarity refinement, C9 its ternary refinement, and C18 their common refinement"
    false
    refl
