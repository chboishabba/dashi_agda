module DASHI.Reasoning.WavePantsBundleGluingAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (+_; -[1+_])

import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Branch
import DASHI.Reasoning.TernarySynthesisTransportWeldExact as Transport

------------------------------------------------------------------------
-- WAVE/PANTS STATUS AGAINST THE CANONICAL BUNDLESHEAF PROMOTION BAR
--
-- The branch carrier has explicit boundary interfaces, InterfaceMatch,
-- BranchSubstitution and composeAt.  The synthesis owner also exposes both an
-- exact zero split/recombine residual and an exact nonzero phase-changed
-- residual.  This is stronger than analogy, but it is not yet an arbitrary
-- BundleSheaf local-family/glue/restrict-exact construction.
------------------------------------------------------------------------

record WavePantsBundleStatus : Set where
  constructor wavePantsBundleStatusRecord
  field
    explicitBoundaryInterfaces : Bool
    exactInterfaceMatchLocated : Bool
    branchSubstitutionLocated : Bool
    canonicalZeroResidualLocated : Bool
    phaseChangedNonzeroResidualLocated : Bool
    arbitraryCompatibleFamilyGlueLocated : Bool
    exactRestrictionBackLocated : Bool
    bundleSheafPromotionPaid : Bool

open WavePantsBundleStatus public

wavePantsBundleStatus : WavePantsBundleStatus
wavePantsBundleStatus =
  wavePantsBundleStatusRecord
    true true true true true false false false

canonicalInterfaceMatch :
  Branch.InterfaceMatch Branch.selectedChannel2 Branch.innerInputChannel2
canonicalInterfaceMatch = Branch.outerInnerMatch

canonicalZeroTransportResidual :
  Transport.transportDefect Transport.canonicalOneToThreeSynthesis
  ≡ Wave.mkDiscreteWave (+ 0) (+ 0)
canonicalZeroTransportResidual = Transport.canonicalSynthesisDefectIsZero

phaseChangedTransportResidual :
  Transport.transportDefect Transport.phaseChangedSynthesis
  ≡ Wave.mkDiscreteWave (-[1+ 0 ]) (+ 1)
phaseChangedTransportResidual = Transport.phaseChangedSynthesisDefectExact

bundlePromotionStillUnpaid :
  bundleSheafPromotionPaid wavePantsBundleStatus ≡ false
bundlePromotionStillUnpaid = refl
