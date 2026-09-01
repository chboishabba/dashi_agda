{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PrintedSignRound153Exact where

------------------------------------------------------------------------
-- ROUND153 A1 BIDI: PIN THE PRINTED CMP98 g(-z) SIGN AT THE PUBLIC CONSUMER
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CMP98 Sect. A defines
--
--   g(z) = (e^{-z} - 1)/(-z)
--
-- and records the scalar-function identity
--
--   g^{-1}(-z) e^z = g^{-1}(z).
--
-- Eq. (119) then literally contains g(-i ad Y), g^{-1}(-i ad Y_x), and
-- R(e^{iY_x}); the paragraph immediately following Eq. (119) applies exactly
-- the displayed identity above.
--
-- BIDI consequence: relative to the existing LR record
--
--   dexpPlus = adjointExp o dexpMinus,
--
-- the printed Eq. (119) roles are forced to be
--
--   g(-i ad Y)         = dexpPlus,
--   g^{-1}(-i ad Y_x) = Jplus,
--   g^{-1}( i ad Y_x) = Jminus.
--
-- This file pins those roles at Round152's least-privilege public boundary.
-- No caller can silently swap plus/minus again while still inhabiting these
-- equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

leastPrivilegeOuterPrintedGMinusIsDexpPlus :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step vector →
  R147.dexpMinusOuter (R152.asLiteralPathData source convention) step vector
  ≡ LR.dexpPlus (R148.outer convention step) vector
leastPrivilegeOuterPrintedGMinusIsDexpPlus source convention step vector = refl

leastPrivilegePointPrintedGInverseMinusIsJplus :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.inverseDexpMinusAt
      (R152.asLiteralPathData source convention) step point vector
  ≡ LR.Jplus (R148.atPoint convention step point) vector
leastPrivilegePointPrintedGInverseMinusIsJplus source convention step point vector = refl

leastPrivilegePointAdjointIsPrintedRExp :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.adjointExpAt
      (R152.asLiteralPathData source convention) step point vector
  ≡ LR.adjointExp (R148.atPoint convention step point) vector
leastPrivilegePointAdjointIsPrintedRExp source convention step point vector = refl

-- Exact operator lift of CMP98's printed identity
-- g^{-1}(-z)e^z = g^{-1}(z).
leastPrivilegePrintedInverseTransport :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) vector →
  R147.inverseDexpMinusAt
      (R152.asLiteralPathData source convention) step point
      (R147.adjointExpAt
        (R152.asLiteralPathData source convention) step point vector)
  ≡ LR.Jminus (R148.atPoint convention step point) vector
leastPrivilegePrintedInverseTransport source convention step point =
  R148.pointPrintedInverseTransport convention step point

cmp98Equation119PrintedSignRound153Level : ProofLevel
cmp98Equation119PrintedSignRound153Level = machineChecked

cmp98Equation119PrintedInverseTransportRound153Level : ProofLevel
cmp98Equation119PrintedInverseTransportRound153Level = machineChecked

-- After this sign audit, the surviving dexp source leaf is NOT "which sign?".
-- It is only the physical same-object identification of CMP98's actual Y and
-- Y_x with the already-owned LR instances at the outer bond and block points.
literalCMP98PhysicalYFamilyIdentificationRound153Level : ProofLevel
literalCMP98PhysicalYFamilyIdentificationRound153Level = conditional
