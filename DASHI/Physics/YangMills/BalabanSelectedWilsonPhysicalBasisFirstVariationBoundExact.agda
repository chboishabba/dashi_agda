{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedWilsonPhysicalBasisFirstVariationBoundExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet
import DASHI.Physics.YangMills.BalabanFourUnitJetFirstVariationBoundExact as Four
import DASHI.Physics.YangMills.BalabanSelectedWilsonBasisLinkJetNormExact as LinkBound
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact as Support

basisField :
  Coordinates.PhysicalSU2Coordinate4 → Coordinates.PhysicalSU2BondField4
basisField = LinkBound.basisField

positiveJetBound :
  ∀ background target site axis →
  Four.UnitFirstJetBound
    (Plaquette.positiveLinkJet background (basisField target) site axis)
positiveJetBound background target site axis = record
  { Four.UnitFirstJetBound.valueNormSqIsOne =
      LinkBound.positiveValueNormSqExact
        background (basisField target) site axis
  ; Four.UnitFirstJetBound.firstNormSqBelowOne =
      LinkBound.positiveBasisFirstNormSqBelowOne
        background target site axis
  }

inverseJetBound :
  ∀ background target site axis →
  Four.UnitFirstJetBound
    (Plaquette.inverseLinkJet background (basisField target) site axis)
inverseJetBound background target site axis = record
  { Four.UnitFirstJetBound.valueNormSqIsOne =
      LinkBound.inverseValueNormSqExact
        background (basisField target) site axis
  ; Four.UnitFirstJetBound.firstNormSqBelowOne =
      LinkBound.inverseBasisFirstNormSqBelowOne
        background target site axis
  }

plaquetteBasisFirstVariationAbsoluteBelowFour :
  ∀ background site axes target →
  ∣ Support.plaquetteFirstVariationCovector
      background (pair site axes) target ∣
  ≤ (+ 4 / 1)
plaquetteBasisFirstVariationAbsoluteBelowFour
    background site axes target =
  let
    left = Plaquette.pairLeft axes
    right = Plaquette.pairRight axes
    field = basisField target

    j0 = Plaquette.positiveLinkJet background field site left
    j1 = Plaquette.positiveLinkJet background field
      (Hodge4.shiftForward left site) right
    j2 = Plaquette.inverseLinkJet background field
      (Hodge4.shiftForward right site) left
    j3 = Plaquette.inverseLinkJet background field site right
  in
  Four.fourUnitJetWilsonFirstVariationAbsoluteBelowFour
    j0 j1 j2 j3
    (positiveJetBound background target site left)
    (positiveJetBound background target
      (Hodge4.shiftForward left site) right)
    (inverseJetBound background target
      (Hodge4.shiftForward right site) left)
    (inverseJetBound background target site right)

selectedPhysicalWilsonFirstVariationUniformBoundLevel : ProofLevel
selectedPhysicalWilsonFirstVariationUniformBoundLevel = machineChecked
