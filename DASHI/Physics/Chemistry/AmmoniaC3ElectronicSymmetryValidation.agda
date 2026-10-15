module DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3E

neutralGroundStateIsSingletA1 :
  NH3E.NeutralElectronicReceipt.groundStateLabel
    NH3E.canonicalNeutralElectronicReceipt
  ≡ "1A1"
neutralGroundStateIsSingletA1 = refl

neutralGroundStatePointGroupIsC3v :
  NH3E.NeutralElectronicReceipt.pointGroup
    NH3E.canonicalNeutralElectronicReceipt
  ≡ "C3v"
neutralGroundStatePointGroupIsC3v = refl

occupiedElectronCountIsTen :
  NH3E.NeutralElectronicReceipt.totalElectrons
    NH3E.canonicalNeutralElectronicReceipt
  ≡ 10
occupiedElectronCountIsTen = refl

a1ElectronCountIsSix :
  NH3E.NeutralElectronicReceipt.a1Electrons
    NH3E.canonicalNeutralElectronicReceipt
  ≡ 6
a1ElectronCountIsSix = refl

eElectronCountIsFour :
  NH3E.NeutralElectronicReceipt.eElectrons
    NH3E.canonicalNeutralElectronicReceipt
  ≡ 4
eElectronCountIsFour = refl

eRestrictionCarriesConjugateC3Phases :
  NH3E.EPhasePair.phasePlus NH3E.canonicalEPhasePair ≡ NH3E.zeta
  × NH3E.EPhasePair.phaseMinus NH3E.canonicalEPhasePair ≡ NH3E.zetaSquared
eRestrictionCarriesConjugateC3Phases = refl , refl

orbitalSymmetryCoordinatesPaid :
  NH3E.ElectronicSymmetryBoundary.sourceBackedOrbitalSymmetryCoordinatesPaid
    NH3E.canonicalElectronicSymmetryBoundary
  ≡ true
orbitalSymmetryCoordinatesPaid = refl

fullWavefunctionStillUnpaid :
  NH3E.ElectronicSymmetryBoundary.fullAbInitioElectronicWavefunctionPaid
    NH3E.canonicalElectronicSymmetryBoundary
  ≡ false
fullWavefunctionStillUnpaid = refl

hamiltonianStillUnpaid :
  NH3E.ElectronicSymmetryBoundary.sameObjectHamiltonianPaid
    NH3E.canonicalElectronicSymmetryBoundary
  ≡ false
hamiltonianStillUnpaid = refl
