{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact where

------------------------------------------------------------------------
-- ROUND148 A1 BIDI: REUSE THE EXISTING LEFT/RIGHT DEXP CALCULUS IN EQ. (119)
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Round147 constructs the physical R0/path geometry.  This file refuses to
-- invent fresh g/g^{-1}/adjoint operators for the remaining Lie-calculus part.
-- Instead the Eq. (119) point operators are projections of the already-owned
-- `LeftRightDexpCancellationData`:
--
--   g(-i ad Y)         -> dexpMinus
--   g^{-1}(-i ad Y_x) -> Jminus
--   R(exp iY_x)        -> adjointExp.
--
-- The opposite-trivialisation cancellation
--
--   Jplus (adjointExp v) = Jminus v
--
-- is therefore inherited from the existing inverse-uniqueness theorem rather
-- than supplied as another receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

record CMP98Equation119DexpConvention (Lie : Set) : Set₁ where
  field
    outer : Nat → LR.LeftRightDexpCancellationData Lie
    atPoint :
      Nat → Centered.CenteredBlockPoint4 6 →
      LR.LeftRightDexpCancellationData Lie

    -- These two equalities are the literal source convention seam.  They say
    -- that CMP98's printed Y/Y_x use the same minus trivialisation represented
    -- by the existing repository records.  No analytic inverse law is repeated.
    printedOuterGIsDexpMinus : Nat → Set
    printedPointInverseGIsJminus :
      Nat → Centered.CenteredBlockPoint4 6 → Set

open CMP98Equation119DexpConvention public

outerDexpMinus :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Dexp.Endomorphism Lie
outerDexpMinus convention step = LR.dexpMinus (outer convention step)

pointInverseDexpMinus :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Centered.CenteredBlockPoint4 6 → Dexp.Endomorphism Lie
pointInverseDexpMinus convention step point =
  LR.Jminus (atPoint convention step point)

pointAdjointExp :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Centered.CenteredBlockPoint4 6 → Dexp.Endomorphism Lie
pointAdjointExp convention step point =
  LR.adjointExp (atPoint convention step point)

outerAdjointExp :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Dexp.Endomorphism Lie
outerAdjointExp convention step = LR.adjointExp (outer convention step)

pointOppositeTrivialisationCancels :
  ∀ {Lie}
    (convention : CMP98Equation119DexpConvention Lie)
    step point vector →
  LR.Jplus (atPoint convention step point)
    (pointAdjointExp convention step point vector)
  ≡ pointInverseDexpMinus convention step point vector
pointOppositeTrivialisationCancels convention step point =
  LR.leftRightInverseDexpCancellation (atPoint convention step point)

outerOppositeTrivialisationCancels :
  ∀ {Lie}
    (convention : CMP98Equation119DexpConvention Lie)
    step vector →
  LR.Jplus (outer convention step)
    (outerAdjointExp convention step vector)
  ≡ LR.Jminus (outer convention step) vector
outerOppositeTrivialisationCancels convention step =
  LR.leftRightInverseDexpCancellation (outer convention step)

cmp98Equation119ExistingDexpReuseRound148Level : ProofLevel
cmp98Equation119ExistingDexpReuseRound148Level = machineChecked

cmp98Equation119OppositeTrivialisationCancellationRound148Level : ProofLevel
cmp98Equation119OppositeTrivialisationCancellationRound148Level = machineChecked

-- Only source sign/trivialisation identification remains.  The inverse and
-- cancellation algebra itself is already theorem-owned.
literalCMP98PrintedYConventionRound148Level : ProofLevel
literalCMP98PrintedYConventionRound148Level = conditional
