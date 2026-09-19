{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedWilsonCompanionGradientBoundExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteBoundedCovarianceExact as FiniteCov
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact as Support
import DASHI.Physics.YangMills.BalabanSelectedWilsonPhysicalBasisFirstVariationBoundExact as Bound

wilsonCompanionGradient :
  Plaquette.Plaquette4 →
  Coordinates.PhysicalSU2Coordinate4 →
  FiniteCov.Observable Plaquette.RationalSU2Background4
wilsonCompanionGradient plaquette coordinate background =
  Support.plaquetteFirstVariationCovector background plaquette coordinate

four : ℚ
four = + 4 / 1

fourNonnegative : 0ℚ ≤ four
fourNonnegative = ℚP.nonNegative⁻¹ four

wilsonCompanionGradientPointwiseBelowFour :
  ∀ plaquette coordinate →
  FiniteCov.PointwiseBounded
    (wilsonCompanionGradient plaquette coordinate)
    four
wilsonCompanionGradientPointwiseBelowFour
    (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair site axes)
    coordinate
    background =
  Bound.plaquetteBasisFirstVariationAbsoluteBelowFour
    background site axes coordinate

selectedWilsonCompanionGradientBoundLevel : ProofLevel
selectedWilsonCompanionGradientBoundLevel = machineChecked
