module DASHI.Physics.Chemistry.AmmoniaMonster3BC3QuotientLiftValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaMonster3BC3QuotientLiftExact as Q
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as M

phaseRoundTripNH3Paid :
  (p : NH3.ElectronicC3Phase) →
  Q.commonToNH3 (Q.nh3ToCommon p) ≡ p
phaseRoundTripNH3Paid = Q.nh3CommonRoundTrip

phaseRoundTripMonsterPaid :
  (p : M.CentralPhase3) →
  Q.commonToMonster (Q.monsterToCommon p) ≡ p
phaseRoundTripMonsterPaid = Q.monsterCommonRoundTrip

multiplicationIntertwinesPaid :
  (a b : NH3.ElectronicC3Phase) →
  Q.nh3ToMonster (Q.multiplyNH3 a b)
  ≡ Q.multiplyMonster (Q.nh3ToMonster a) (Q.nh3ToMonster b)
multiplicationIntertwinesPaid = Q.nh3MonsterMultiplicationIntertwines

inversionIntertwinesPaid :
  (p : NH3.ElectronicC3Phase) →
  Q.nh3ToMonster (Q.inverseNH3 p)
  ≡ M.invertPhase (Q.nh3ToMonster p)
inversionIntertwinesPaid = Q.nh3MonsterInversionIntertwines

fourierRowsIntertwinePaid :
  (p : NH3.ElectronicC3Phase) →
  Q.monsterFourierRow (Q.nh3ToMonster p) ≡ NH3.phaseFourierRow p
fourierRowsIntertwinePaid = Q.nh3MonsterFourierRowsIntertwine

actualStateLiftStillUnpaid :
  Q.C3QuotientLiftBoundary.actualNH3StateToMonsterSectorLiftPaid
    Q.canonicalC3QuotientLiftBoundary ≡ false
actualStateLiftStillUnpaid = refl

physicalMonsterActionStillUnpaid :
  Q.C3QuotientLiftBoundary.nontrivialPhysicalMonsterActionOnNH3Paid
    Q.canonicalC3QuotientLiftBoundary ≡ false
physicalMonsterActionStillUnpaid = refl
