module DASHI.Physics.Closure.NSTriadKNProfileCrossProductAnalyticAudit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_)

import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds
  as ForcedTailArithmetic
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates
  as ForcedTailProfiles
import DASHI.Physics.Closure.NSTriadKNResidualClosureDependency
  as ResidualClosure
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates
  as TransitionArithmetic

------------------------------------------------------------------------
-- Typed theorem-target inventory.
--
-- These records describe the propositions that the cross-product matrix
-- still needs.  They are target types, not closure receipts: in particular,
-- the cross-product estimate itself is deliberately not replaced by an
-- arithmetic witness here.

two : Nat
two = suc (suc zero)

data ProfileCrossProductExponentEntry : Set where
  ftFtEntry : ProfileCrossProductExponentEntry
  advFtEntry : ProfileCrossProductExponentEntry
  advAdvEntry : ProfileCrossProductExponentEntry
  advTransEntry : ProfileCrossProductExponentEntry
  advResEntry : ProfileCrossProductExponentEntry
  transFtEntry : ProfileCrossProductExponentEntry
  transAdvEntry : ProfileCrossProductExponentEntry
  transTransEntry : ProfileCrossProductExponentEntry
  transResEntry : ProfileCrossProductExponentEntry
  resFtEntry : ProfileCrossProductExponentEntry

record ProfileCrossProductExponentSumTarget
    (entry : ProfileCrossProductExponentEntry) : Set where
  constructor mkProfileCrossProductExponentSumTarget
  field
    rowDecayExponent : Nat
    columnDecayExponent : Nat
    exponentSumAtLeastTwo :
      two ≤ rowDecayExponent + columnDecayExponent

record ForcedTailAdversarialCrossProductTarget : Set₁ where
  field
    crossProductBound : Set

record ForcedTailTransitionCrossProductTarget : Set₁ where
  field
    crossProductBound : Set

-- The ten named exponent-sum entries are distinct target slots, even though
-- they share the same arithmetic shape.
ftFtExponentSumTarget : Set
ftFtExponentSumTarget =
  ProfileCrossProductExponentSumTarget ftFtEntry

advFtExponentSumTarget : Set
advFtExponentSumTarget =
  ProfileCrossProductExponentSumTarget advFtEntry

advAdvExponentSumTarget : Set
advAdvExponentSumTarget =
  ProfileCrossProductExponentSumTarget advAdvEntry

advTransExponentSumTarget : Set
advTransExponentSumTarget =
  ProfileCrossProductExponentSumTarget advTransEntry

advResExponentSumTarget : Set
advResExponentSumTarget =
  ProfileCrossProductExponentSumTarget advResEntry

transFtExponentSumTarget : Set
transFtExponentSumTarget =
  ProfileCrossProductExponentSumTarget transFtEntry

transAdvExponentSumTarget : Set
transAdvExponentSumTarget =
  ProfileCrossProductExponentSumTarget transAdvEntry

transTransExponentSumTarget : Set
transTransExponentSumTarget =
  ProfileCrossProductExponentSumTarget transTransEntry

transResExponentSumTarget : Set
transResExponentSumTarget =
  ProfileCrossProductExponentSumTarget transResEntry

resFtExponentSumTarget : Set
resFtExponentSumTarget =
  ProfileCrossProductExponentSumTarget resFtEntry

-- Residual reductions consume the typed parent targets and the already named
-- domination/special-entry premises.  The result remains an analytic Set
-- target because domination alone does not prove the required bound.
ftResReductionTarget : Set₁
ftResReductionTarget =
  ResidualClosure.ResidualKernelDominatedByClosedProfiles →
  ftFtExponentSumTarget →
  ForcedTailAdversarialCrossProductTarget →
  ForcedTailTransitionCrossProductTarget →
  Set

resAdvReductionTarget : Set₁
resAdvReductionTarget =
  ResidualClosure.ResidualKernelDominatedByClosedProfiles →
  advAdvExponentSumTarget →
  ForcedTailAdversarialCrossProductTarget →
  transAdvExponentSumTarget →
  Set

resTransReductionTarget : Set₁
resTransReductionTarget =
  ResidualClosure.ResidualKernelDominatedByClosedProfiles →
  advTransExponentSumTarget →
  ForcedTailTransitionCrossProductTarget →
  transTransExponentSumTarget →
  Set

resResReductionTarget : Set₁
resResReductionTarget =
  ResidualClosure.ResidualKernelDominatedByClosedProfiles → Set

------------------------------------------------------------------------
-- Constructive arithmetic reductions already supported upstream.

transitionExponentSumTarget :
  (c : TransitionArithmetic.TransitionClass) →
  ProfileCrossProductExponentSumTarget transTransEntry
transitionExponentSumTarget c =
  mkProfileCrossProductExponentSumTarget
    (TransitionArithmetic.transitionRowDecayExp c)
    (TransitionArithmetic.transitionColumnDecayExp c)
    (TransitionArithmetic.transitionClassExponentSumAtLeastTwo c)

-- This is a reusable arithmetic witness for any transition-class slot.  It
-- does not set a cross-product audit flag because the analytic row/column
-- estimates are separate premises.
transitionExponentSumArithmetic :
  (c : TransitionArithmetic.TransitionClass) →
  two ≤
    TransitionArithmetic.transitionRowDecayExp c +
    TransitionArithmetic.transitionColumnDecayExp c
transitionExponentSumArithmetic c =
  TransitionArithmetic.transitionClassExponentSumAtLeastTwo c

record ForcedTailScaledN2ArithmeticTarget : Set where
  constructor mkForcedTailScaledN2ArithmeticTarget
  field
    forcedTailClass : ForcedTailProfiles.ForcedTailClass
    scaledN2Bound :
      (N : Nat) →
      ForcedTailArithmetic.forcedTailN2ScaledLHS forcedTailClass N ≤
      ForcedTailArithmetic.forcedTailN2ScaledRHS forcedTailClass N

forcedTailScaledN2ArithmeticTarget :
  (c : ForcedTailProfiles.ForcedTailClass) →
  ForcedTailScaledN2ArithmeticTarget
forcedTailScaledN2ArithmeticTarget c =
  mkForcedTailScaledN2ArithmeticTarget
    c
    (ForcedTailArithmetic.forcedTailN2ScaledArithmetic c)

------------------------------------------------------------------------
-- Fail-closed inventory for the cross-product matrix.
--
-- The FT→adv and FT→transition special entries now have constructive
-- weight-separation witnesses. The ten exponent-sum entries and four
-- residual reductions still require the underlying analytic estimates.
-- This separates conditional receipt plumbing from Clay-grade closure.

record ProfileCrossProductAnalyticAudit : Set where
  constructor mkProfileCrossProductAnalyticAudit
  field
    ftFtExponentClosed : Bool
    advFtExponentClosed : Bool
    advAdvExponentClosed : Bool
    advTransExponentClosed : Bool
    advResExponentClosed : Bool
    transFtExponentClosed : Bool
    transAdvExponentClosed : Bool
    transTransExponentClosed : Bool
    transResExponentClosed : Bool
    resFtExponentClosed : Bool

    ftAdvSpecialClosed : Bool
    ftTransSpecialClosed : Bool

    ftResReductionClosed : Bool
    resAdvReductionClosed : Bool
    resTransReductionClosed : Bool
    resResReductionClosed : Bool

    analyticMatrixClosed : Bool
    analyticMatrixClosedIsFalse : analyticMatrixClosed ≡ false

open ProfileCrossProductAnalyticAudit public

canonicalProfileCrossProductAnalyticAudit :
  ProfileCrossProductAnalyticAudit
canonicalProfileCrossProductAnalyticAudit =
  mkProfileCrossProductAnalyticAudit
    false false false false false
    false false false false false
    true true
    false false false false
    false refl

canonicalProfileCrossProductAnalyticClosed : Bool
canonicalProfileCrossProductAnalyticClosed =
  analyticMatrixClosed canonicalProfileCrossProductAnalyticAudit

canonicalProfileCrossProductAnalyticClosedIsFalse :
  canonicalProfileCrossProductAnalyticClosed ≡ false
canonicalProfileCrossProductAnalyticClosedIsFalse =
  analyticMatrixClosedIsFalse canonicalProfileCrossProductAnalyticAudit
