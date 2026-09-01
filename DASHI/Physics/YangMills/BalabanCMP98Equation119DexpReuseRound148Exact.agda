{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact where

------------------------------------------------------------------------
-- ROUND148 A1 BIDI: SOURCE-CORRECT LEFT/RIGHT DEXP REUSE FOR EQ. (119)
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Source audit correction.
-- CMP98 defines
--
--   g(z) = (e^{-z} - 1)/(-z)
--
-- and immediately records
--
--   g^{-1}(-z) e^z = g^{-1}(z).
--
-- In Eq. (119) the printed operators are therefore
--
--   g(-i ad Y)          = the PLUS/opposite-trivialisation dexp,
--   g^{-1}(-i ad Y_x)  = Jplus,
--   R(e^{iY_x})         = adjointExp,
--
-- when compared with the existing `LeftRightDexpCancellationData`, whose
-- defining relation is
--
--   dexpPlus = adjointExp o dexpMinus
--
-- and whose inverse-uniqueness theorem gives exactly the source identity
--
--   Jplus (adjointExp v) = Jminus v.
--
-- An earlier Round148 draft reversed the plus/minus labels.  The BIDI source
-- check caught that: the algebraic theorem was right, but the Eq. (119) role
-- assignment was backwards.  This file fixes the assignment without inventing
-- any fresh g/g^{-1}/adjoint receipt.
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

open CMP98Equation119DexpConvention public

-- Literal CMP98 Eq. (119) role: g(-i ad Y).
outerPrintedGMinus :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Dexp.Endomorphism Lie
outerPrintedGMinus convention step = LR.dexpPlus (outer convention step)

-- Literal CMP98 Eq. (119) role: g^{-1}(-i ad Y_x).
pointPrintedGInverseMinus :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Centered.CenteredBlockPoint4 6 → Dexp.Endomorphism Lie
pointPrintedGInverseMinus convention step point =
  LR.Jplus (atPoint convention step point)

pointAdjointExp :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Centered.CenteredBlockPoint4 6 → Dexp.Endomorphism Lie
pointAdjointExp convention step point =
  LR.adjointExp (atPoint convention step point)

outerAdjointExp :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Dexp.Endomorphism Lie
outerAdjointExp convention step = LR.adjointExp (outer convention step)

-- This is CMP98's printed scalar-function identity
-- g^{-1}(-z)e^z = g^{-1}(z), lifted to the existing operator family.
pointPrintedInverseTransport :
  ∀ {Lie}
    (convention : CMP98Equation119DexpConvention Lie)
    step point vector →
  pointPrintedGInverseMinus convention step point
    (pointAdjointExp convention step point vector)
  ≡ LR.Jminus (atPoint convention step point) vector
pointPrintedInverseTransport convention step point =
  LR.leftRightInverseDexpCancellation (atPoint convention step point)

outerPrintedInverseTransport :
  ∀ {Lie}
    (convention : CMP98Equation119DexpConvention Lie)
    step vector →
  LR.Jplus (outer convention step)
    (outerAdjointExp convention step vector)
  ≡ LR.Jminus (outer convention step) vector
outerPrintedInverseTransport convention step =
  LR.leftRightInverseDexpCancellation (outer convention step)

------------------------------------------------------------------------
-- Compatibility names retained for downstream files written before the source
-- orientation audit.  Their implementations are now source-correct: despite
-- the historical names, these denote the printed g(-z)/g^{-1}(-z) roles.
------------------------------------------------------------------------

outerDexpMinus :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Dexp.Endomorphism Lie
outerDexpMinus = outerPrintedGMinus

pointInverseDexpMinus :
  ∀ {Lie} → CMP98Equation119DexpConvention Lie →
  Nat → Centered.CenteredBlockPoint4 6 → Dexp.Endomorphism Lie
pointInverseDexpMinus = pointPrintedGInverseMinus

cmp98Equation119ExistingDexpReuseRound148Level : ProofLevel
cmp98Equation119ExistingDexpReuseRound148Level = machineChecked

cmp98Equation119PrintedInverseTransportRound148Level : ProofLevel
cmp98Equation119PrintedInverseTransportRound148Level = machineChecked

-- Compatibility status name retained for prior validation roots.
cmp98Equation119OppositeTrivialisationCancellationRound148Level : ProofLevel
cmp98Equation119OppositeTrivialisationCancellationRound148Level =
  cmp98Equation119PrintedInverseTransportRound148Level

-- What remains physical is now narrower and source-correct: identify the
-- actual printed Y/Y_x matrices with the already-owned LR family.  The sign and
-- direction of the g^{-1} transport identity are no longer ambiguous.
literalCMP98PrintedYConventionRound148Level : ProofLevel
literalCMP98PrintedYConventionRound148Level = conditional
