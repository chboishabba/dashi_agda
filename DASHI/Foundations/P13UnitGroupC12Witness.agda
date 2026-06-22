module DASHI.Foundations.P13UnitGroupC12Witness where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.SSPPrimeLaneUnitAction using
  ( canonicalGeneratorStep
  ; normalizedUnitStep
  ; SSPPrimeLaneUnitActionProfile
  ; primeLaneUnitActionProfile
  )
open import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry using
  ( primeLaneSymmetryProfile
  ; unitOrder
  )
open import DASHI.Foundations.StageAtlasZeroToEleven using
  ( atlas-0
  ; atlas-1
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( primeLane369PhaseBridge )
open import DASHI.TrackedPrimes using (SSP; p13)

data P13UnitClass : Set where
  p13-unit0 : P13UnitClass
  p13-unit1 : P13UnitClass
  p13-unit2 : P13UnitClass
  p13-unit3 : P13UnitClass
  p13-unit4 : P13UnitClass
  p13-unit5 : P13UnitClass
  p13-unit6 : P13UnitClass
  p13-unit7 : P13UnitClass
  p13-unit8 : P13UnitClass
  p13-unit9 : P13UnitClass
  p13-unit10 : P13UnitClass
  p13-unit11 : P13UnitClass

p13UnitIdentity : P13UnitClass
p13UnitIdentity = p13-unit0

p13UnitGenerator : P13UnitClass
p13UnitGenerator = p13-unit1

p13UnitQuarterTurnElement : P13UnitClass
p13UnitQuarterTurnElement = p13-unit3

p13UnitThirdTurnElement : P13UnitClass
p13UnitThirdTurnElement = p13-unit4

p13UnitHalfTurnElement : P13UnitClass
p13UnitHalfTurnElement = p13-unit6

succP13UnitClass : P13UnitClass → P13UnitClass
succP13UnitClass p13-unit0 = p13-unit1
succP13UnitClass p13-unit1 = p13-unit2
succP13UnitClass p13-unit2 = p13-unit3
succP13UnitClass p13-unit3 = p13-unit4
succP13UnitClass p13-unit4 = p13-unit5
succP13UnitClass p13-unit5 = p13-unit6
succP13UnitClass p13-unit6 = p13-unit7
succP13UnitClass p13-unit7 = p13-unit8
succP13UnitClass p13-unit8 = p13-unit9
succP13UnitClass p13-unit9 = p13-unit10
succP13UnitClass p13-unit10 = p13-unit11
succP13UnitClass p13-unit11 = p13-unit0

toStep : P13UnitClass → Nat
toStep p13-unit0 = 0
toStep p13-unit1 = 1
toStep p13-unit2 = 2
toStep p13-unit3 = 3
toStep p13-unit4 = 4
toStep p13-unit5 = 5
toStep p13-unit6 = 6
toStep p13-unit7 = 7
toStep p13-unit8 = 8
toStep p13-unit9 = 9
toStep p13-unit10 = 10
toStep p13-unit11 = 11

composeP13UnitClass : P13UnitClass → P13UnitClass → P13UnitClass
composeP13UnitClass p13-unit0 x = x
composeP13UnitClass p13-unit1 x = succP13UnitClass x
composeP13UnitClass p13-unit2 x = succP13UnitClass (succP13UnitClass x)
composeP13UnitClass p13-unit3 x =
  succP13UnitClass (succP13UnitClass (succP13UnitClass x))
composeP13UnitClass p13-unit4 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass x)))
composeP13UnitClass p13-unit5 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass x))))
composeP13UnitClass p13-unit6 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass
            (succP13UnitClass x)))))
composeP13UnitClass p13-unit7 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass
            (succP13UnitClass
              (succP13UnitClass x))))))
composeP13UnitClass p13-unit8 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass
            (succP13UnitClass
              (succP13UnitClass
                (succP13UnitClass x)))))))
composeP13UnitClass p13-unit9 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass
            (succP13UnitClass
              (succP13UnitClass
                (succP13UnitClass
                  (succP13UnitClass x))))))))
composeP13UnitClass p13-unit10 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass
            (succP13UnitClass
              (succP13UnitClass
                (succP13UnitClass
                  (succP13UnitClass
                    (succP13UnitClass x)))))))))
composeP13UnitClass p13-unit11 x =
  succP13UnitClass
    (succP13UnitClass
      (succP13UnitClass
        (succP13UnitClass
          (succP13UnitClass
            (succP13UnitClass
              (succP13UnitClass
                (succP13UnitClass
                  (succP13UnitClass
                    (succP13UnitClass
                      (succP13UnitClass x))))))))))

inverseP13UnitClass : P13UnitClass → P13UnitClass
inverseP13UnitClass p13-unit0 = p13-unit0
inverseP13UnitClass p13-unit1 = p13-unit11
inverseP13UnitClass p13-unit2 = p13-unit10
inverseP13UnitClass p13-unit3 = p13-unit9
inverseP13UnitClass p13-unit4 = p13-unit8
inverseP13UnitClass p13-unit5 = p13-unit7
inverseP13UnitClass p13-unit6 = p13-unit6
inverseP13UnitClass p13-unit7 = p13-unit5
inverseP13UnitClass p13-unit8 = p13-unit4
inverseP13UnitClass p13-unit9 = p13-unit3
inverseP13UnitClass p13-unit10 = p13-unit2
inverseP13UnitClass p13-unit11 = p13-unit1

generatorPower2 :
  composeP13UnitClass p13UnitGenerator p13UnitGenerator ≡ p13-unit2
generatorPower2 = refl

generatorPower3 :
  composeP13UnitClass p13UnitGenerator p13-unit2 ≡ p13-unit3
generatorPower3 = refl

generatorPower4 :
  composeP13UnitClass p13UnitGenerator p13-unit3 ≡ p13UnitThirdTurnElement
generatorPower4 = refl

generatorPower6 :
  composeP13UnitClass p13UnitGenerator p13-unit5 ≡ p13UnitHalfTurnElement
generatorPower6 = refl

generatorPower12 :
  composeP13UnitClass p13UnitGenerator p13-unit11 ≡ p13UnitIdentity
generatorPower12 = refl

halfTurnSquaredIsIdentity :
  composeP13UnitClass p13UnitHalfTurnElement p13UnitHalfTurnElement
  ≡ p13UnitIdentity
halfTurnSquaredIsIdentity = refl

thirdTurnCubedIsIdentity :
  composeP13UnitClass p13UnitThirdTurnElement p13-unit8 ≡ p13UnitIdentity
thirdTurnCubedIsIdentity = refl

quarterTurnFourthIsIdentity :
  composeP13UnitClass p13UnitQuarterTurnElement p13-unit9 ≡ p13UnitIdentity
quarterTurnFourthIsIdentity = refl

leftIdentityP13UnitClass :
  (x : P13UnitClass) →
  composeP13UnitClass p13UnitIdentity x ≡ x
leftIdentityP13UnitClass p13-unit0 = refl
leftIdentityP13UnitClass p13-unit1 = refl
leftIdentityP13UnitClass p13-unit2 = refl
leftIdentityP13UnitClass p13-unit3 = refl
leftIdentityP13UnitClass p13-unit4 = refl
leftIdentityP13UnitClass p13-unit5 = refl
leftIdentityP13UnitClass p13-unit6 = refl
leftIdentityP13UnitClass p13-unit7 = refl
leftIdentityP13UnitClass p13-unit8 = refl
leftIdentityP13UnitClass p13-unit9 = refl
leftIdentityP13UnitClass p13-unit10 = refl
leftIdentityP13UnitClass p13-unit11 = refl

leftInverseP13UnitClass :
  (x : P13UnitClass) →
  composeP13UnitClass (inverseP13UnitClass x) x ≡ p13UnitIdentity
leftInverseP13UnitClass p13-unit0 = refl
leftInverseP13UnitClass p13-unit1 = refl
leftInverseP13UnitClass p13-unit2 = refl
leftInverseP13UnitClass p13-unit3 = refl
leftInverseP13UnitClass p13-unit4 = refl
leftInverseP13UnitClass p13-unit5 = refl
leftInverseP13UnitClass p13-unit6 = refl
leftInverseP13UnitClass p13-unit7 = refl
leftInverseP13UnitClass p13-unit8 = refl
leftInverseP13UnitClass p13-unit9 = refl
leftInverseP13UnitClass p13-unit10 = refl
leftInverseP13UnitClass p13-unit11 = refl

record P13CandidateOnlyAuthority : Set where
  constructor mkP13CandidateOnlyAuthority
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    coreAuthorityBit : Bool
    coreAuthorityBitIsTrue : coreAuthorityBit ≡ true
    coreReceiptBit : Bool
    coreReceiptBitIsTrue : coreReceiptBit ≡ true

open P13CandidateOnlyAuthority public

p13CandidateOnlyAuthority : P13CandidateOnlyAuthority
p13CandidateOnlyAuthority =
  mkP13CandidateOnlyAuthority
    true
    refl
    true
    refl
    true
    refl

p13PrimeLaneSymmetryProfile : Symmetry.PrimeLaneSymmetryProfile
p13PrimeLaneSymmetryProfile = primeLaneSymmetryProfile p13

p13SSPPrimeLane369PhaseBridge : Phase.SSPPrimeLane369PhaseBridge
p13SSPPrimeLane369PhaseBridge = Phase.primeLane369PhaseBridge p13

p13PrimeIdentityStageIsAtlas1 :
  Phase.primeIdentityStage p13SSPPrimeLane369PhaseBridge ≡ atlas-1
p13PrimeIdentityStageIsAtlas1 = refl

p13UnitOrderIs12 :
  Phase.unitOrder p13SSPPrimeLane369PhaseBridge ≡ 12
p13UnitOrderIs12 = refl

p13UnitOrderStageIsAtlas0 :
  Phase.unitOrderStage p13SSPPrimeLane369PhaseBridge ≡ atlas-0
p13UnitOrderStageIsAtlas0 = refl

record P13C12PrimeLaneQuotientCarrier : Set where
  constructor mkP13C12PrimeLaneQuotientCarrier
  field
    carrierLabel : String
    carrierOrder : Nat
    identityElement : Nat
    identityElementIsZero : identityElement ≡ 0
    stepProjection : Nat → Nat
    identityProjection : Nat
    identityProjectionIsProjection : identityProjection ≡ stepProjection identityElement
    canonicalGeneratorProjection : Nat
    canonicalGeneratorProjectionIsProjection :
      canonicalGeneratorProjection ≡ stepProjection canonicalGeneratorStep

open P13C12PrimeLaneQuotientCarrier public

p13C12PrimeLaneQuotientCarrier : P13C12PrimeLaneQuotientCarrier
p13C12PrimeLaneQuotientCarrier =
  mkP13C12PrimeLaneQuotientCarrier
    "p13/C12"
    12
    0
    refl
    (normalizedUnitStep p13)
    (normalizedUnitStep p13 0)
    refl
    (normalizedUnitStep p13 canonicalGeneratorStep)
    refl

p13PrimeLaneUnitActionProfile :
  SSPPrimeLaneUnitActionProfile
p13PrimeLaneUnitActionProfile =
  primeLaneUnitActionProfile p13 canonicalGeneratorStep

record P13UnitActionQuotientSurface : Set where
  constructor mkP13UnitActionQuotientSurface
  field
    primeIdentity : SSP
    carrier : P13C12PrimeLaneQuotientCarrier
    phaseBridge : Phase.SSPPrimeLane369PhaseBridge
    phaseBridgeIsCanonical : phaseBridge ≡ Phase.primeLane369PhaseBridge p13
    actionReceipt : SSPPrimeLaneUnitActionProfile
    actionReceiptIsCanonical :
      actionReceipt ≡ primeLaneUnitActionProfile p13 canonicalGeneratorStep
    candidateAuthority : P13CandidateOnlyAuthority
    carrierOrderMatchesPhaseBridge :
      carrierOrder carrier ≡ Phase.unitOrder phaseBridge

open P13UnitActionQuotientSurface public

canonicalP13UnitActionQuotient : P13UnitActionQuotientSurface
canonicalP13UnitActionQuotient =
  mkP13UnitActionQuotientSurface
    p13
    p13C12PrimeLaneQuotientCarrier
    p13SSPPrimeLane369PhaseBridge
    refl
    p13PrimeLaneUnitActionProfile
    refl
    p13CandidateOnlyAuthority
    refl

record P13UnitGroupC12Witness : Set where
  constructor mkP13UnitGroupC12Witness
  field
    phaseBridgeOrderIs12 :
      Phase.unitOrder p13SSPPrimeLane369PhaseBridge ≡ 12
    symmetryProfileOrderIs12 :
      Symmetry.unitOrder p13PrimeLaneSymmetryProfile ≡ 12
    primeIdentityStageIsAtlas1 :
      Phase.primeIdentityStage p13SSPPrimeLane369PhaseBridge ≡ atlas-1
    unitOrderStageIsAtlas0 :
      Phase.unitOrderStage p13SSPPrimeLane369PhaseBridge ≡ atlas-0
    candidateOnlyAuthority :
      P13CandidateOnlyAuthority
    generator : P13UnitClass
    identity : P13UnitClass
    quarterTurn : P13UnitClass
    thirdTurn : P13UnitClass
    halfTurn : P13UnitClass
    generatorOrderTwelve :
      composeP13UnitClass p13UnitGenerator p13-unit11 ≡ p13UnitIdentity
    generatorPowerThreeMatchesQuarterTurn :
      composeP13UnitClass p13UnitGenerator p13-unit2 ≡ p13UnitQuarterTurnElement
    generatorPowerFourMatchesThirdTurn :
      composeP13UnitClass p13UnitGenerator p13-unit3 ≡ p13UnitThirdTurnElement
    generatorPowerSixMatchesHalfTurn :
      composeP13UnitClass p13UnitGenerator p13-unit5 ≡ p13UnitHalfTurnElement
    halfTurnOrderTwo :
      composeP13UnitClass p13UnitHalfTurnElement p13UnitHalfTurnElement
      ≡ p13UnitIdentity
    thirdTurnOrderThree :
      composeP13UnitClass p13UnitThirdTurnElement p13-unit8 ≡ p13UnitIdentity
    quarterTurnOrderFour :
      composeP13UnitClass p13UnitQuarterTurnElement p13-unit9 ≡ p13UnitIdentity
    generatorInverseIsEleven :
      inverseP13UnitClass p13UnitGenerator ≡ p13-unit11
    generatorHasLeftInverse :
      composeP13UnitClass (inverseP13UnitClass p13UnitGenerator) p13UnitGenerator
      ≡ p13UnitIdentity

open P13UnitGroupC12Witness public

canonicalP13UnitGroupC12Witness : P13UnitGroupC12Witness
canonicalP13UnitGroupC12Witness =
  mkP13UnitGroupC12Witness
    p13UnitOrderIs12
    refl
    p13PrimeIdentityStageIsAtlas1
    p13UnitOrderStageIsAtlas0
    p13CandidateOnlyAuthority
    p13UnitGenerator
    p13UnitIdentity
    p13UnitQuarterTurnElement
    p13UnitThirdTurnElement
    p13UnitHalfTurnElement
    generatorPower12
    generatorPower3
    generatorPower4
    generatorPower6
    halfTurnSquaredIsIdentity
    thirdTurnCubedIsIdentity
    quarterTurnFourthIsIdentity
    refl
    (leftInverseP13UnitClass p13UnitGenerator)

p13IdentityStageIsStage1 :
  Phase.primeIdentityStage p13SSPPrimeLane369PhaseBridge ≡ atlas-1
p13IdentityStageIsStage1 = p13PrimeIdentityStageIsAtlas1

p13UnitStageIsStage0 :
  Phase.unitOrderStage p13SSPPrimeLane369PhaseBridge ≡ atlas-0
p13UnitStageIsStage0 = p13UnitOrderStageIsAtlas0

p13GeneratorSquaredIsTwo :
  composeP13UnitClass p13UnitGenerator p13UnitGenerator ≡ p13-unit2
p13GeneratorSquaredIsTwo = generatorPower2

p13GeneratorCubedIsThree :
  composeP13UnitClass p13UnitGenerator p13-unit2 ≡ p13-unit3
p13GeneratorCubedIsThree = generatorPower3
