module DASHI.Physics.Closure.NSTriadKNGramBaseGapBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNGramCoercivityTargetReceipt as GramReceipt
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap

------------------------------------------------------------------------
-- Gram-to-base-gap bridge.
--
-- The live analytic parent for Blocker 2C is not an abstract "base gap"
-- theorem.  It is the amplitude-weighted Gram coercivity theorem on the exact
-- high-high carrier:
--
--   <v, K_N(A) v> >= (c / N) * |v|_2^2.
--
-- This module packages the minimum theorem-facing content needed to feed that
-- route into BaseFormCoercivity / BaseGapN2Theorem without pretending the Gram
-- theorem is already proved.

record GramBaseFormCoercivityTarget
    (gapQuadraticForms : QGap.GapQuadraticFormsTarget)
    (strongNormSquared :
      QGap.GapQuadraticFormsTarget.Carrier gapQuadraticForms
        (QGap.GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat)
    : Setω where
  constructor mkGramBaseFormCoercivityTarget
  field
    sourceReceipt :
      GramReceipt.NSTriadKNGramCoercivityTargetReceipt

    gramTheoremCarrierRecorded :
      GramReceipt.failClosed sourceReceipt ≡ true

    gramBaseConstant : Nat
    gramBasePositive : Set
    gramBaseCoercive :
      QGap.baseGapN2Target
        gapQuadraticForms
        strongNormSquared
        gramBaseConstant

open GramBaseFormCoercivityTarget public

toBaseFormCoercivity :
  {gapQuadraticForms : QGap.GapQuadraticFormsTarget} →
  {strongNormSquared :
    QGap.GapQuadraticFormsTarget.Carrier gapQuadraticForms
      (QGap.GapQuadraticFormsTarget.shellIndex gapQuadraticForms) → Nat} →
  GramBaseFormCoercivityTarget gapQuadraticForms strongNormSquared →
  QGap.BaseFormCoercivity gapQuadraticForms strongNormSquared
toBaseFormCoercivity target =
  QGap.mkBaseFormCoercivity
    (gramBaseConstant target)
    (gramBasePositive target)
    (gramBaseCoercive target)
