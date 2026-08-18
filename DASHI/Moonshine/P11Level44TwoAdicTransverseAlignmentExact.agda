module DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact where

------------------------------------------------------------------------
-- TRANSVERSE FORM OF THE REMAINING LOCAL p=2 ALIGNMENT
--
-- Source context:
-- Ralf Schmidt, "Some remarks on local newforms for GL(2)",
-- J. Ramanujan Math. Soc. 17 (2002), 115--147.
--
-- P11Level44TwoAdicFixedSpaceIntersectionExact proves that the principal
-- full-level-2 and K_0(4) fixed spaces are distinct three-coordinate subspaces
-- of one compact induced model with a common TWO-coordinate subspace.
--
-- DASHI CONTRIBUTION
--
-- Split each three-coordinate model exactly as
--
--   common two coordinates + one transverse defect.
--
-- Principal model:
--   common = (x1,x4),   defect_P = x2-x1.
--
-- K_0(4) model:
--   common = (wide,left), defect_0 = right-left.
--
-- Both codecs are lossless over Z.  Consequently the unresolved comparison is
-- one-dimensional after the common plane is fixed.  Moreover TWO distinct
-- integral isomorphisms already preserve the common plane: identify the
-- transverse defects with the same sign or with opposite sign.
--
-- Therefore even "same local representation + same common intersection" does
-- not canonically choose the full alignment.  A genuine local operator,
-- Whittaker/test-vector normalization, or another source-native orientation
-- datum must choose the transverse line.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Int
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as K0
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection

------------------------------------------------------------------------
-- Common plane + one transverse integer.
------------------------------------------------------------------------

record Split3 : Set where
  constructor split3
  field
    common : Intersection.Common2
    defect : ℤ
open Split3 public

principalSplit : Principal.Old3 → Split3
principalSplit p = split3
  (Intersection.common2 (Principal.x1 p) (Principal.x4 p))
  (Int._-_ (Principal.x2 p) (Principal.x1 p))

principalJoin : Split3 → Principal.Old3
principalJoin s = Principal.old3
  (Intersection.first (common s))
  (Int._+_ (Intersection.first (common s)) (defect s))
  (Intersection.terminal (common s))

k0Split : K0.Bruhat3 → Split3
k0Split k = split3
  (Intersection.common2 (K0.wide k) (K0.left k))
  (Int._-_ (K0.right k) (K0.left k))

k0Join : Split3 → K0.Bruhat3
k0Join s = K0.bruhat3
  (Intersection.first (common s))
  (Intersection.terminal (common s))
  (Int._+_ (Intersection.terminal (common s)) (defect s))

------------------------------------------------------------------------
-- Small extensionality helpers.
------------------------------------------------------------------------

old3Ext :
  (u v : Principal.Old3) →
  Principal.x1 u ≡ Principal.x1 v →
  Principal.x2 u ≡ Principal.x2 v →
  Principal.x4 u ≡ Principal.x4 v →
  u ≡ v
old3Ext (Principal.old3 a b c) (Principal.old3 .a .b .c) refl refl refl = refl

bruhat3Ext :
  (u v : K0.Bruhat3) →
  K0.wide u ≡ K0.wide v →
  K0.left u ≡ K0.left v →
  K0.right u ≡ K0.right v →
  u ≡ v
bruhat3Ext (K0.bruhat3 a b c) (K0.bruhat3 .a .b .c) refl refl refl = refl

split3Ext :
  (u v : Split3) →
  common u ≡ common v → defect u ≡ defect v → u ≡ v
split3Ext (split3 a d) (split3 .a .d) refl refl = refl

------------------------------------------------------------------------
-- Both splittings are exact two-sided codecs.
------------------------------------------------------------------------

principalJoinAfterSplit : (p : Principal.Old3) → principalJoin (principalSplit p) ≡ p
principalJoinAfterSplit p =
  old3Ext _ _ refl
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ []))
    refl

principalSplitAfterJoin : (s : Split3) → principalSplit (principalJoin s) ≡ s
principalSplitAfterJoin (split3 (Intersection.common2 a b) d) =
  split3Ext _ _ refl (ℤRing.solve (a ∷ d ∷ []))

k0JoinAfterSplit : (k : K0.Bruhat3) → k0Join (k0Split k) ≡ k
k0JoinAfterSplit k =
  bruhat3Ext _ _ refl refl
    (ℤRing.solve (K0.left k ∷ K0.right k ∷ []))

k0SplitAfterJoin : (s : Split3) → k0Split (k0Join s) ≡ s
k0SplitAfterJoin (split3 (Intersection.common2 a b) d) =
  split3Ext _ _ refl (ℤRing.solve (b ∷ d ∷ []))

------------------------------------------------------------------------
-- Two distinct full alignments preserving the common plane.
------------------------------------------------------------------------

negateDefect : Split3 → Split3
negateDefect s = split3 (common s) (Int.-_ (defect s))

negateDefectTwice : (s : Split3) → negateDefect (negateDefect s) ≡ s
negateDefectTwice (split3 c d) =
  split3Ext _ _ refl (ℤRing.solve (d ∷ []))

plusPrincipalToK0 : Principal.Old3 → K0.Bruhat3
plusPrincipalToK0 = k0Join ∘ principalSplit

plusK0ToPrincipal : K0.Bruhat3 → Principal.Old3
plusK0ToPrincipal = principalJoin ∘ k0Split

minusPrincipalToK0 : Principal.Old3 → K0.Bruhat3
minusPrincipalToK0 p = k0Join (negateDefect (principalSplit p))

minusK0ToPrincipal : K0.Bruhat3 → Principal.Old3
minusK0ToPrincipal k = principalJoin (negateDefect (k0Split k))

plusRoundTripPrincipal :
  (p : Principal.Old3) → plusK0ToPrincipal (plusPrincipalToK0 p) ≡ p
plusRoundTripPrincipal p
  rewrite k0SplitAfterJoin (principalSplit p) = principalJoinAfterSplit p

plusRoundTripK0 :
  (k : K0.Bruhat3) → plusPrincipalToK0 (plusK0ToPrincipal k) ≡ k
plusRoundTripK0 k
  rewrite principalSplitAfterJoin (k0Split k) = k0JoinAfterSplit k

minusRoundTripPrincipal :
  (p : Principal.Old3) → minusK0ToPrincipal (minusPrincipalToK0 p) ≡ p
minusRoundTripPrincipal p
  rewrite k0SplitAfterJoin (negateDefect (principalSplit p))
  | negateDefectTwice (principalSplit p) = principalJoinAfterSplit p

minusRoundTripK0 :
  (k : K0.Bruhat3) → minusPrincipalToK0 (minusK0ToPrincipal k) ≡ k
minusRoundTripK0 k
  rewrite principalSplitAfterJoin (negateDefect (k0Split k))
  | negateDefectTwice (k0Split k) = k0JoinAfterSplit k

------------------------------------------------------------------------
-- They agree on the common plane but differ on the transverse line.
------------------------------------------------------------------------

plusOnCommon :
  (c : Intersection.Common2) →
  plusPrincipalToK0 (Intersection.principalCommon c) ≡ Intersection.k0Common c
plusOnCommon (Intersection.common2 a b) = refl

minusOnCommon :
  (c : Intersection.Common2) →
  minusPrincipalToK0 (Intersection.principalCommon c) ≡ Intersection.k0Common c
minusOnCommon (Intersection.common2 a b) = refl

plusBasis2 :
  plusPrincipalToK0 Principal.oldBasis2 ≡ K0.bruhat3 (+ 0) (+ 0) (+ 1)
plusBasis2 = refl

minusBasis2 :
  minusPrincipalToK0 Principal.oldBasis2 ≡ K0.bruhat3 (+ 0) (+ 0) (-[1+ 0 ])
minusBasis2 = refl

plusAndMinusDiffer :
  plusPrincipalToK0 Principal.oldBasis2 ≡ minusPrincipalToK0 Principal.oldBasis2 → ⊥
plusAndMinusDiffer ()

record P11Level44TwoAdicTransverseAlignmentBoundary : Set where
  field
    principalSplitLossless : Bool
    k0SplitLossless : Bool
    commonCoordinates : Nat
    transverseCoordinates : Nat
    plusAlignmentInvertible : Bool
    minusAlignmentInvertible : Bool
    alignmentsAgreeOnCommonPlane : Bool
    alignmentsDistinctTransversely : Bool
    commonPlaneDeterminesFullAlignment : Bool
    sourceNativeTransverseSelectorStillRequired : Bool

canonicalP11Level44TwoAdicTransverseAlignmentBoundary :
  P11Level44TwoAdicTransverseAlignmentBoundary
canonicalP11Level44TwoAdicTransverseAlignmentBoundary = record
  { principalSplitLossless = true
  ; k0SplitLossless = true
  ; commonCoordinates = 2
  ; transverseCoordinates = 1
  ; plusAlignmentInvertible = true
  ; minusAlignmentInvertible = true
  ; alignmentsAgreeOnCommonPlane = true
  ; alignmentsDistinctTransversely = true
  ; commonPlaneDeterminesFullAlignment = false
  ; sourceNativeTransverseSelectorStillRequired = true
  }
