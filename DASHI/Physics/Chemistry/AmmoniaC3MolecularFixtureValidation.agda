module DASHI.Physics.Chemistry.AmmoniaC3MolecularFixtureValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaC3MolecularFixtureExact as NH3

ammoniaHasThreeHydrogenCycle :
  NH3.rotateH (NH3.rotateH (NH3.rotateH NH3.h1)) ≡ NH3.h1
ammoniaHasThreeHydrogenCycle = refl

ammoniaPointGroupRecordedC3v :
  NH3.AmmoniaC3Fixture.pointGroup NH3.canonicalAmmoniaC3Fixture ≡ "C3v"
ammoniaPointGroupRecordedC3v = refl

ammoniaSymmetryNumberIsThree :
  NH3.AmmoniaC3Fixture.symmetryNumber NH3.canonicalAmmoniaC3Fixture ≡ 3
ammoniaSymmetryNumberIsThree = refl

geometryFixturePaid :
  NH3.AmmoniaC3Fixture.experimentalC3GeometryPaid NH3.canonicalAmmoniaC3Fixture ≡ true
geometryFixturePaid = refl

fullElectronicC3RepresentationUnpaid :
  NH3.AmmoniaC3Boundary.fullElectronicC3RepresentationPaid
    NH3.canonicalAmmoniaC3Boundary
  ≡ false
fullElectronicC3RepresentationUnpaid = refl

inversionIsNotChemicalReaction :
  NH3.AmmoniaC3Boundary.ammoniaInversionIsProductsByproductsReaction
    NH3.canonicalAmmoniaC3Boundary
  ≡ false
inversionIsNotChemicalReaction = refl
