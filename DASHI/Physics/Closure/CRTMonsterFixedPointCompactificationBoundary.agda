module DASHI.Physics.Closure.CRTMonsterFixedPointCompactificationBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import CRTJFixedPointBridge as RootCRTJ
import CRTPeriod as CRT
import DASHI.Algebra.MoonshineBridge as MoonshineBridge
import DASHI.Foundations.SurrealCompactificationIntake as SurrealIntake
import DASHI.Physics.CRTPeriodJFixedBridge as CRTJ
import DASHI.Physics.Closure.ExtremalFrobeniusMonsterAuthorityBoundary as MonsterBoundary
import DASHI.Physics.Closure.MonsterMoonshineSSPQuotientControlReceipt as MonsterQuotient
import DASHI.Physics.Closure.MonsterVOAFixedPointReceipt as MonsterFixed
import DASHI.Physics.Moonshine.DASHIMonsterVOAUniquenessReceipt as MonsterUnique
import JFixedPoint as J

------------------------------------------------------------------------
-- CRT / Monster fixed-point compactification boundary.
--
-- This is a checked finite boundary surface only.  It packages the current
-- CRT period arithmetic, the j fixed-point contraction numeral, and the
-- existing Monster receipt surfaces while keeping the promotion gates closed.

data CRTMonsterFixedPointCompactificationStatus : Set where
  finiteCRTJMonsterBoundaryNoPromotion :
    CRTMonsterFixedPointCompactificationStatus

data CRTMonsterFixedPointCompactificationBoundary : Set where
  boundaryCRTPeriodIs47Times59Times71 :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryJContractIsPeriodPlusOne :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryPeriodPlusOneIs196884 :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryMonsterReceiptsConsumedOnly :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryRationalCompactificationStatusConsumedOnly :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryRationalCompactificationConnects196884MonsterChain :
    CRTMonsterFixedPointCompactificationBoundary

  boundarySurrealIsomorphismNotConstructed :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryNoMonsterTheoremPromotion :
    CRTMonsterFixedPointCompactificationBoundary

  boundaryNoTerminalPromotion :
    CRTMonsterFixedPointCompactificationBoundary

canonicalCRTMonsterFixedPointCompactificationBoundaries :
  List CRTMonsterFixedPointCompactificationBoundary
canonicalCRTMonsterFixedPointCompactificationBoundaries =
  boundaryCRTPeriodIs47Times59Times71
  ∷ boundaryJContractIsPeriodPlusOne
  ∷ boundaryPeriodPlusOneIs196884
  ∷ boundaryMonsterReceiptsConsumedOnly
  ∷ boundaryRationalCompactificationStatusConsumedOnly
  ∷ boundaryRationalCompactificationConnects196884MonsterChain
  ∷ boundarySurrealIsomorphismNotConstructed
  ∷ boundaryNoMonsterTheoremPromotion
  ∷ boundaryNoTerminalPromotion
  ∷ []

data MonsterTheoremPromotionToken : Set where

data SurrealIsomorphismPromotionToken : Set where

data TerminalPromotionToken : Set where

noMonsterTheoremPromotionTokenHere :
  MonsterTheoremPromotionToken →
  ⊥
noMonsterTheoremPromotionTokenHere ()

noSurrealIsomorphismPromotionTokenHere :
  SurrealIsomorphismPromotionToken →
  ⊥
noSurrealIsomorphismPromotionTokenHere ()

noTerminalPromotionTokenHere :
  TerminalPromotionToken →
  ⊥
noTerminalPromotionTokenHere ()

crtPeriod :
  Nat
crtPeriod =
  CRT.period

crtPeriodIs47Times59Times71 :
  crtPeriod ≡ 47 * 59 * 71
crtPeriodIs47Times59Times71 =
  CRTJ.crt-period-prime-product

crtPeriodPlusOneIs196884 :
  CRT.period + 1 ≡ 196884
crtPeriodPlusOneIs196884 =
  RootCRTJ.period-plus-one

jUnitContractIsPeriodPlusOne :
  J.contract J.unit-obs ≡ CRT.period + 1
jUnitContractIsPeriodPlusOne =
  RootCRTJ.unit-contract-period-plus-one

jUnitContractIs196884 :
  J.contract J.unit-obs ≡ 196884
jUnitContractIs196884 =
  J.unit-converges

------------------------------------------------------------------------
-- Exact closure-chain links.

record Arithmetic196884EqualityLink : Set where
  field
    arithmeticCRTPeriod :
      Nat

    arithmeticCRTPeriodIsImported :
      arithmeticCRTPeriod ≡ CRT.period

    arithmeticCRTPeriodIsPrimeProduct :
      arithmeticCRTPeriod ≡ 47 * 59 * 71

    arithmeticScalar :
      Nat

    arithmeticScalarIsPeriodPlusOne :
      arithmeticScalar ≡ arithmeticCRTPeriod + 1

    arithmeticScalarIsMoonshineCoefficient :
      arithmeticScalar ≡ MoonshineBridge.moonshineCoefficient

    arithmeticScalarIs196884 :
      arithmeticScalar ≡ 196884

open Arithmetic196884EqualityLink public

canonicalArithmetic196884EqualityLink :
  Arithmetic196884EqualityLink
canonicalArithmetic196884EqualityLink =
  record
    { arithmeticCRTPeriod =
        CRT.period
    ; arithmeticCRTPeriodIsImported =
        refl
    ; arithmeticCRTPeriodIsPrimeProduct =
        CRTJ.crt-period-prime-product
    ; arithmeticScalar =
        CRT.period + 1
    ; arithmeticScalarIsPeriodPlusOne =
        refl
    ; arithmeticScalarIsMoonshineCoefficient =
        MoonshineBridge.crtPeriodPlusOne
    ; arithmeticScalarIs196884 =
        RootCRTJ.period-plus-one
    }

record JContractionEqualityLink : Set where
  field
    jObservation :
      J.Observation

    jObservationIsUnit :
      jObservation ≡ J.unit-obs

    jContractionScalar :
      Nat

    jContractionScalarIsContract :
      jContractionScalar ≡ J.contract jObservation

    jContractionScalarIsPeriodPlusOne :
      jContractionScalar ≡ CRT.period + 1

    jContractionScalarIsMoonshineCoefficient :
      jContractionScalar ≡ MoonshineBridge.moonshineCoefficient

    jContractionScalarIs196884 :
      jContractionScalar ≡ 196884

open JContractionEqualityLink public

canonicalJContractionEqualityLink :
  JContractionEqualityLink
canonicalJContractionEqualityLink =
  record
    { jObservation =
        J.unit-obs
    ; jObservationIsUnit =
        refl
    ; jContractionScalar =
        J.contract J.unit-obs
    ; jContractionScalarIsContract =
        refl
    ; jContractionScalarIsPeriodPlusOne =
        RootCRTJ.unit-contract-period-plus-one
    ; jContractionScalarIsMoonshineCoefficient =
        MoonshineBridge.jUnitContract
    ; jContractionScalarIs196884 =
        J.unit-converges
    }

record MonsterCoefficientReceiptLink : Setω where
  field
    monsterCoefficientFixedPointReceipt :
      MonsterFixed.MonsterVOAFixedPointReceipt

    monsterCoefficientJReceipt :
      MonsterFixed.JInvariantFixedPointZeroResidualReceipt

    monsterCoefficientJReceiptIsImported :
      monsterCoefficientJReceipt
      ≡
      MonsterFixed.jInvariantInterpretation
        monsterCoefficientFixedPointReceipt

    monsterCoefficientScalar :
      Nat

    monsterCoefficientScalarIsReceiptJCoefficient :
      monsterCoefficientScalar
      ≡
      MonsterFixed.jCoefficient monsterCoefficientJReceipt

    monsterCoefficientScalarIsMoonshineCoefficient :
      monsterCoefficientScalar ≡ MoonshineBridge.moonshineCoefficient

    monsterCoefficientScalarIs196884 :
      monsterCoefficientScalar ≡ 196884

    monsterCoefficientPhysicalPromotion :
      Bool

    monsterCoefficientPhysicalPromotionIsFalse :
      monsterCoefficientPhysicalPromotion ≡ false

open MonsterCoefficientReceiptLink public

canonicalMonsterCoefficientReceiptLink :
  MonsterCoefficientReceiptLink
canonicalMonsterCoefficientReceiptLink =
  record
    { monsterCoefficientFixedPointReceipt =
        MonsterFixed.canonicalMonsterVOAFixedPointReceipt
    ; monsterCoefficientJReceipt =
        MonsterFixed.jInvariantInterpretation
          MonsterFixed.canonicalMonsterVOAFixedPointReceipt
    ; monsterCoefficientJReceiptIsImported =
        refl
    ; monsterCoefficientScalar =
        MonsterFixed.jCoefficient
          (MonsterFixed.jInvariantInterpretation
            MonsterFixed.canonicalMonsterVOAFixedPointReceipt)
    ; monsterCoefficientScalarIsReceiptJCoefficient =
        refl
    ; monsterCoefficientScalarIsMoonshineCoefficient =
        refl
    ; monsterCoefficientScalarIs196884 =
        refl
    ; monsterCoefficientPhysicalPromotion =
        MonsterFixed.physicalPromotion
          MonsterFixed.canonicalMonsterVOAFixedPointReceipt
    ; monsterCoefficientPhysicalPromotionIsFalse =
        refl
    }

record MissingMoonshineIsomorphismAuthorityLink : Setω where
  field
    missingAuthorityMonsterBoundary :
      MonsterBoundary.ExternalGradedModuleIsomorphismAuthorityBoundary

    missingAuthorityState :
      MonsterBoundary.ExtremalFrobeniusGradedIsomorphismAuthorityState

    missingAuthorityStateIsImported :
      missingAuthorityState
      ≡
      MonsterBoundary.gradedIsomorphismAuthorityState
        missingAuthorityMonsterBoundary

    missingAuthorityStateIsMissing :
      missingAuthorityState
      ≡
      MonsterBoundary.missingExternalGradedModuleIsomorphismAuthority

    missingAuthorityQuotientReceipt :
      MonsterQuotient.MonsterMoonshineSSPQuotientControlReceipt

    moonshineQuotientTargetRecorded :
      Bool

    moonshineQuotientTargetRecordedIsTrue :
      moonshineQuotientTargetRecorded ≡ true

    moonshineQuotientTheoremProvedHere :
      Bool

    moonshineQuotientTheoremProvedHereIsImported :
      moonshineQuotientTheoremProvedHere
      ≡
      MonsterQuotient.quotientEntropyBoundProvedHere
        missingAuthorityQuotientReceipt

    moonshineQuotientTheoremProvedHereIsFalse :
      moonshineQuotientTheoremProvedHere ≡ false

    monsterAuthorityTheoremPromoted :
      Bool

    monsterAuthorityTheoremPromotedIsFalse :
      monsterAuthorityTheoremPromoted ≡ false

    monsterAuthorityTerminalPromoted :
      Bool

    monsterAuthorityTerminalPromotedIsFalse :
      monsterAuthorityTerminalPromoted ≡ false

open MissingMoonshineIsomorphismAuthorityLink public

canonicalMissingMoonshineIsomorphismAuthorityLink :
  MissingMoonshineIsomorphismAuthorityLink
canonicalMissingMoonshineIsomorphismAuthorityLink =
  record
    { missingAuthorityMonsterBoundary =
        MonsterBoundary.canonicalExternalGradedModuleIsomorphismAuthorityBoundary
    ; missingAuthorityState =
        MonsterBoundary.gradedIsomorphismAuthorityState
          MonsterBoundary.canonicalExternalGradedModuleIsomorphismAuthorityBoundary
    ; missingAuthorityStateIsImported =
        refl
    ; missingAuthorityStateIsMissing =
        refl
    ; missingAuthorityQuotientReceipt =
        MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; moonshineQuotientTargetRecorded =
        MonsterQuotient.moonshineSSPActsAsQuotient
          MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; moonshineQuotientTargetRecordedIsTrue =
        refl
    ; moonshineQuotientTheoremProvedHere =
        MonsterQuotient.quotientEntropyBoundProvedHere
          MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; moonshineQuotientTheoremProvedHereIsImported =
        refl
    ; moonshineQuotientTheoremProvedHereIsFalse =
        refl
    ; monsterAuthorityTheoremPromoted =
        MonsterBoundary.theoremPromoted
          MonsterBoundary.canonicalExternalGradedModuleIsomorphismAuthorityBoundary
    ; monsterAuthorityTheoremPromotedIsFalse =
        refl
    ; monsterAuthorityTerminalPromoted =
        MonsterBoundary.terminalClaimPromoted
          MonsterBoundary.canonicalExternalGradedModuleIsomorphismAuthorityBoundary
    ; monsterAuthorityTerminalPromotedIsFalse =
        refl
    }

record CRTMonsterExactClosureChain : Setω where
  field
    arithmeticEqualityLink :
      Arithmetic196884EqualityLink

    jContractionEqualityLink :
      JContractionEqualityLink

    monsterCoefficientLink :
      MonsterCoefficientReceiptLink

    missingAuthorityLink :
      MissingMoonshineIsomorphismAuthorityLink

    arithmeticScalarMatchesJContraction :
      arithmeticScalar arithmeticEqualityLink
      ≡
      jContractionScalar jContractionEqualityLink

    arithmeticScalarMatchesMonsterCoefficient :
      arithmeticScalar arithmeticEqualityLink
      ≡
      monsterCoefficientScalar monsterCoefficientLink

    jContractionMatchesMonsterCoefficient :
      jContractionScalar jContractionEqualityLink
      ≡
      monsterCoefficientScalar monsterCoefficientLink

    exactChainMonsterTheoremPromoted :
      Bool

    exactChainMonsterTheoremPromotedIsFalse :
      exactChainMonsterTheoremPromoted ≡ false

    exactChainSurrealIsomorphismConstructed :
      Bool

    exactChainSurrealIsomorphismConstructedIsFalse :
      exactChainSurrealIsomorphismConstructed ≡ false

    exactChainTerminalPromoted :
      Bool

    exactChainTerminalPromotedIsFalse :
      exactChainTerminalPromoted ≡ false

open CRTMonsterExactClosureChain public

canonicalCRTMonsterExactClosureChain :
  CRTMonsterExactClosureChain
canonicalCRTMonsterExactClosureChain =
  record
    { arithmeticEqualityLink =
        canonicalArithmetic196884EqualityLink
    ; jContractionEqualityLink =
        canonicalJContractionEqualityLink
    ; monsterCoefficientLink =
        canonicalMonsterCoefficientReceiptLink
    ; missingAuthorityLink =
        canonicalMissingMoonshineIsomorphismAuthorityLink
    ; arithmeticScalarMatchesJContraction =
        refl
    ; arithmeticScalarMatchesMonsterCoefficient =
        refl
    ; jContractionMatchesMonsterCoefficient =
        refl
    ; exactChainMonsterTheoremPromoted =
        false
    ; exactChainMonsterTheoremPromotedIsFalse =
        refl
    ; exactChainSurrealIsomorphismConstructed =
        false
    ; exactChainSurrealIsomorphismConstructedIsFalse =
        refl
    ; exactChainTerminalPromoted =
        false
    ; exactChainTerminalPromotedIsFalse =
        refl
    }

record RationalCompactification196884MonsterReceiptRow : Setω where
  field
    rationalCompactificationIntake :
      SurrealIntake.SurrealCompactificationIntakeContract

    rationalCompactificationIntakeIsCanonical :
      rationalCompactificationIntake
      ≡
      SurrealIntake.canonicalSurrealCompactificationIntakeContract

    rationalNoQQCarrierIntake :
      SurrealIntake.NoQQCarrierBridgeIntake

    rationalNoQQCarrierIntakeIsImported :
      rationalNoQQCarrierIntake
      ≡
      SurrealIntake.carrierIntake rationalCompactificationIntake

    rationalQQCarrierGate :
      SurrealIntake.CarrierAuthorityGate

    rationalQQCarrierGateIsImported :
      rationalQQCarrierGate
      ≡
      SurrealIntake.qqGate rationalNoQQCarrierIntake

    rationalQQCarrierExternalAuthorityRequired :
      SurrealIntake.externalAuthorityRequired rationalQQCarrierGate ≡ true

    rationalQQCarrierConstructedHereIsFalse :
      SurrealIntake.constructedHere rationalQQCarrierGate ≡ false

    rationalQQCarrierPromotedHereIsFalse :
      SurrealIntake.promotedHere rationalQQCarrierGate ≡ false

    rationalGaugeIntakeAtPeriod :
      SurrealIntake.SymbolicThreeMinusNGaugeIntake CRT.period

    rationalGaugeIntakeAtPeriodIsImported :
      rationalGaugeIntakeAtPeriod
      ≡
      SurrealIntake.gaugeIntake rationalCompactificationIntake CRT.period

    rationalGaugeRequiresQQValue :
      SurrealIntake.rationalValueRequired rationalGaugeIntakeAtPeriod ≡ true

    rationalGaugeQQValueConstructedHereIsFalse :
      SurrealIntake.rationalValueConstructedHere rationalGaugeIntakeAtPeriod
      ≡
      false

    rationalPromotionFlags :
      SurrealIntake.NoPromotionFlags

    rationalPromotionFlagsAreImported :
      rationalPromotionFlags
      ≡
      SurrealIntake.promotionFlags rationalCompactificationIntake

    rationalCompactificationPromotedIsFalse :
      SurrealIntake.compactificationPromoted rationalPromotionFlags ≡ false

    exactClosureChainForRationalStatus :
      CRTMonsterExactClosureChain

    rationalStatusScalar :
      Nat

    rationalStatusScalarIsArithmetic196884 :
      rationalStatusScalar
      ≡
      arithmeticScalar
        (arithmeticEqualityLink exactClosureChainForRationalStatus)

    rationalStatusScalarIsMonsterCoefficient :
      rationalStatusScalar
      ≡
      monsterCoefficientScalar
        (monsterCoefficientLink exactClosureChainForRationalStatus)

    rationalStatusScalarIs196884 :
      rationalStatusScalar ≡ 196884

    rationalStatusMonsterTheoremPromoted :
      exactChainMonsterTheoremPromoted exactClosureChainForRationalStatus
      ≡
      false

    rationalStatusSurrealIsomorphismConstructed :
      exactChainSurrealIsomorphismConstructed exactClosureChainForRationalStatus
      ≡
      false

open RationalCompactification196884MonsterReceiptRow public

canonicalRationalCompactification196884MonsterReceiptRow :
  RationalCompactification196884MonsterReceiptRow
canonicalRationalCompactification196884MonsterReceiptRow =
  record
    { rationalCompactificationIntake =
        SurrealIntake.canonicalSurrealCompactificationIntakeContract
    ; rationalCompactificationIntakeIsCanonical =
        refl
    ; rationalNoQQCarrierIntake =
        SurrealIntake.carrierIntake
          SurrealIntake.canonicalSurrealCompactificationIntakeContract
    ; rationalNoQQCarrierIntakeIsImported =
        refl
    ; rationalQQCarrierGate =
        SurrealIntake.qqGate
          (SurrealIntake.carrierIntake
            SurrealIntake.canonicalSurrealCompactificationIntakeContract)
    ; rationalQQCarrierGateIsImported =
        refl
    ; rationalQQCarrierExternalAuthorityRequired =
        refl
    ; rationalQQCarrierConstructedHereIsFalse =
        refl
    ; rationalQQCarrierPromotedHereIsFalse =
        refl
    ; rationalGaugeIntakeAtPeriod =
        SurrealIntake.gaugeIntake
          SurrealIntake.canonicalSurrealCompactificationIntakeContract
          CRT.period
    ; rationalGaugeIntakeAtPeriodIsImported =
        refl
    ; rationalGaugeRequiresQQValue =
        refl
    ; rationalGaugeQQValueConstructedHereIsFalse =
        refl
    ; rationalPromotionFlags =
        SurrealIntake.promotionFlags
          SurrealIntake.canonicalSurrealCompactificationIntakeContract
    ; rationalPromotionFlagsAreImported =
        refl
    ; rationalCompactificationPromotedIsFalse =
        refl
    ; exactClosureChainForRationalStatus =
        canonicalCRTMonsterExactClosureChain
    ; rationalStatusScalar =
        arithmeticScalar
          (arithmeticEqualityLink canonicalCRTMonsterExactClosureChain)
    ; rationalStatusScalarIsArithmetic196884 =
        refl
    ; rationalStatusScalarIsMonsterCoefficient =
        refl
    ; rationalStatusScalarIs196884 =
        refl
    ; rationalStatusMonsterTheoremPromoted =
        refl
    ; rationalStatusSurrealIsomorphismConstructed =
        refl
    }

record CRTMonsterFixedPointCompactificationBoundaryReceipt : Setω where
  field
    status :
      CRTMonsterFixedPointCompactificationStatus

    crtJBridge :
      CRTJ.SSPMoonshineCoupling

    rootCRTJBridge :
      RootCRTJ.CRTJFixedPointBridge

    monsterVOAFixedPointReceipt :
      MonsterFixed.MonsterVOAFixedPointReceipt

    monsterQuotientReceipt :
      MonsterQuotient.MonsterMoonshineSSPQuotientControlReceipt

    monsterUniquenessReceipt :
      MonsterUnique.DASHIMonsterVOAUniquenessReceipt

    monsterAuthorityBoundary :
      MonsterBoundary.ExternalGradedModuleIsomorphismAuthorityBoundary

    exactClosureChain :
      CRTMonsterExactClosureChain

    arithmetic196884Link :
      Arithmetic196884EqualityLink

    arithmetic196884LinkIsExactChainLink :
      arithmetic196884Link
      ≡
      arithmeticEqualityLink exactClosureChain

    jContract196884Link :
      JContractionEqualityLink

    jContract196884LinkIsExactChainLink :
      jContract196884Link
      ≡
      jContractionEqualityLink exactClosureChain

    monsterCoefficientReceiptLink :
      MonsterCoefficientReceiptLink

    monsterCoefficientReceiptScalarMatchesExactChain :
      monsterCoefficientScalar monsterCoefficientReceiptLink
      ≡
      monsterCoefficientScalar (monsterCoefficientLink exactClosureChain)

    missingMoonshineIsomorphismAuthorityLink :
      MissingMoonshineIsomorphismAuthorityLink

    missingMoonshineIsomorphismAuthorityStateMatchesExactChain :
      missingAuthorityState missingMoonshineIsomorphismAuthorityLink
      ≡
      missingAuthorityState (missingAuthorityLink exactClosureChain)

    missingMoonshineQuotientTheoremFlagMatchesExactChain :
      moonshineQuotientTheoremProvedHere
        missingMoonshineIsomorphismAuthorityLink
      ≡
      moonshineQuotientTheoremProvedHere
        (missingAuthorityLink exactClosureChain)

    rationalCompactification196884MonsterRow :
      RationalCompactification196884MonsterReceiptRow

    rationalCompactificationScalarMatchesExactChain :
      rationalStatusScalar rationalCompactification196884MonsterRow
      ≡
      arithmeticScalar (arithmeticEqualityLink exactClosureChain)

    rationalCompactificationScalarMatchesMonsterCoefficient :
      rationalStatusScalar rationalCompactification196884MonsterRow
      ≡
      monsterCoefficientScalar (monsterCoefficientLink exactClosureChain)

    rationalCompactificationPromotedIsFalse :
      SurrealIntake.compactificationPromoted
        (rationalPromotionFlags rationalCompactification196884MonsterRow)
      ≡
      false

    rationalCompactificationPreservesMonsterTheoremFalse :
      exactChainMonsterTheoremPromoted
        (exactClosureChainForRationalStatus
          rationalCompactification196884MonsterRow)
      ≡
      false

    rationalCompactificationPreservesSurrealIsomorphismFalse :
      exactChainSurrealIsomorphismConstructed
        (exactClosureChainForRationalStatus
          rationalCompactification196884MonsterRow)
      ≡
      false

    period :
      Nat

    periodIsImportedCRTPeriod :
      period ≡ CRT.period

    periodIs47Times59Times71 :
      period ≡ 47 * 59 * 71

    periodPlusOneIs196884 :
      period + 1 ≡ 196884

    unitContract :
      Nat

    unitContractIsJUnitContract :
      unitContract ≡ J.contract J.unit-obs

    unitContractIsPeriodPlusOne :
      unitContract ≡ period + 1

    unitContractIs196884 :
      unitContract ≡ 196884

    c1Monster :
      Nat

    c1MonsterIs196884 :
      c1Monster ≡ MonsterQuotient.c1Monster

    c1MonsterMatchesContract :
      c1Monster ≡ unitContract

    monsterFixedPointPhysicalPromotion :
      Bool

    monsterFixedPointPhysicalPromotionIsFalse :
      monsterFixedPointPhysicalPromotion ≡ false

    monsterQuotientTerminalPromotion :
      Bool

    monsterQuotientTerminalPromotionIsFalse :
      monsterQuotientTerminalPromotion ≡ false

    importedMonsterUniquenessTheoremPromoted :
      Bool

    importedMonsterUniquenessTheoremPromotedIsFalse :
      importedMonsterUniquenessTheoremPromoted ≡ false

    importedMonsterBoundaryTheoremPromoted :
      Bool

    importedMonsterBoundaryTheoremPromotedIsFalse :
      importedMonsterBoundaryTheoremPromoted ≡ false

    monsterTheoremPromoted :
      Bool

    monsterTheoremPromotedIsFalse :
      monsterTheoremPromoted ≡ false

    surrealIsomorphismConstructed :
      Bool

    surrealIsomorphismConstructedIsFalse :
      surrealIsomorphismConstructed ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    boundaries :
      List CRTMonsterFixedPointCompactificationBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalCRTMonsterFixedPointCompactificationBoundaries

    noMonsterTheoremPromotion :
      MonsterTheoremPromotionToken →
      ⊥

    noSurrealIsomorphismPromotion :
      SurrealIsomorphismPromotionToken →
      ⊥

    noTerminalPromotion :
      TerminalPromotionToken →
      ⊥

    receiptBoundary :
      List String

open CRTMonsterFixedPointCompactificationBoundaryReceipt public

canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt :
  CRTMonsterFixedPointCompactificationBoundaryReceipt
canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt =
  record
    { status =
        finiteCRTJMonsterBoundaryNoPromotion
    ; crtJBridge =
        CRTJ.sspMoonshineCouplingSurface
    ; rootCRTJBridge =
        RootCRTJ.crtJFixedPointBridgeSurface
    ; monsterVOAFixedPointReceipt =
        MonsterFixed.canonicalMonsterVOAFixedPointReceipt
    ; monsterQuotientReceipt =
        MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; monsterUniquenessReceipt =
        MonsterUnique.canonicalDASHIMonsterVOAUniquenessReceipt
    ; monsterAuthorityBoundary =
        MonsterBoundary.canonicalExternalGradedModuleIsomorphismAuthorityBoundary
    ; exactClosureChain =
        canonicalCRTMonsterExactClosureChain
    ; arithmetic196884Link =
        canonicalArithmetic196884EqualityLink
    ; arithmetic196884LinkIsExactChainLink =
        refl
    ; jContract196884Link =
        canonicalJContractionEqualityLink
    ; jContract196884LinkIsExactChainLink =
        refl
    ; monsterCoefficientReceiptLink =
        canonicalMonsterCoefficientReceiptLink
    ; monsterCoefficientReceiptScalarMatchesExactChain =
        refl
    ; missingMoonshineIsomorphismAuthorityLink =
        canonicalMissingMoonshineIsomorphismAuthorityLink
    ; missingMoonshineIsomorphismAuthorityStateMatchesExactChain =
        refl
    ; missingMoonshineQuotientTheoremFlagMatchesExactChain =
        refl
    ; rationalCompactification196884MonsterRow =
        canonicalRationalCompactification196884MonsterReceiptRow
    ; rationalCompactificationScalarMatchesExactChain =
        refl
    ; rationalCompactificationScalarMatchesMonsterCoefficient =
        refl
    ; rationalCompactificationPromotedIsFalse =
        refl
    ; rationalCompactificationPreservesMonsterTheoremFalse =
        refl
    ; rationalCompactificationPreservesSurrealIsomorphismFalse =
        refl
    ; period =
        CRT.period
    ; periodIsImportedCRTPeriod =
        refl
    ; periodIs47Times59Times71 =
        CRTJ.crt-period-prime-product
    ; periodPlusOneIs196884 =
        RootCRTJ.period-plus-one
    ; unitContract =
        J.contract J.unit-obs
    ; unitContractIsJUnitContract =
        refl
    ; unitContractIsPeriodPlusOne =
        RootCRTJ.unit-contract-period-plus-one
    ; unitContractIs196884 =
        J.unit-converges
    ; c1Monster =
        MonsterQuotient.c1Monster
    ; c1MonsterIs196884 =
        refl
    ; c1MonsterMatchesContract =
        refl
    ; monsterFixedPointPhysicalPromotion =
        MonsterFixed.physicalPromotion
          MonsterFixed.canonicalMonsterVOAFixedPointReceipt
    ; monsterFixedPointPhysicalPromotionIsFalse =
        refl
    ; monsterQuotientTerminalPromotion =
        MonsterQuotient.terminalPromoted
          MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; monsterQuotientTerminalPromotionIsFalse =
        refl
    ; importedMonsterUniquenessTheoremPromoted =
        MonsterUnique.monsterVOAUniquenessTheoremPromoted
    ; importedMonsterUniquenessTheoremPromotedIsFalse =
        MonsterUnique.monsterVOAUniquenessTheoremPromotedIsFalse
    ; importedMonsterBoundaryTheoremPromoted =
        MonsterBoundary.extremalFrobeniusMonsterTheoremPromoted
    ; importedMonsterBoundaryTheoremPromotedIsFalse =
        MonsterBoundary.extremalFrobeniusMonsterTheoremPromotedIsFalse
    ; monsterTheoremPromoted =
        false
    ; monsterTheoremPromotedIsFalse =
        refl
    ; surrealIsomorphismConstructed =
        false
    ; surrealIsomorphismConstructedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; boundaries =
        canonicalCRTMonsterFixedPointCompactificationBoundaries
    ; boundariesAreCanonical =
        refl
    ; noMonsterTheoremPromotion =
        noMonsterTheoremPromotionTokenHere
    ; noSurrealIsomorphismPromotion =
        noSurrealIsomorphismPromotionTokenHere
    ; noTerminalPromotion =
        noTerminalPromotionTokenHere
    ; receiptBoundary =
        "CRT.period is imported and checked as 47*59*71." ∷
        "CRT.period+1, J.contract unit-obs, and Monster c1 are checked at 196884." ∷
        "Monster fixed-point, quotient, uniqueness, and graded-isomorphism boundary receipts are consumed only as receipts." ∷
        "Rational compactification intake is connected to the 196884/Monster exact closure chain without accepting QQ/No authority." ∷
        "Monster theorem promotion, surreal-isomorphism construction, and terminal promotion are false." ∷
        []
    }

canonicalCRTMonsterPeriodIs47Times59Times71 :
  period canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
  ≡
  47 * 59 * 71
canonicalCRTMonsterPeriodIs47Times59Times71 =
  refl

canonicalCRTMonsterContractIs196884 :
  unitContract canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
  ≡
  196884
canonicalCRTMonsterContractIs196884 =
  refl

canonicalCRTMonsterTheoremPromotionFalse :
  monsterTheoremPromoted
    canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
  ≡
  false
canonicalCRTMonsterTheoremPromotionFalse =
  refl

canonicalCRTMonsterSurrealIsomorphismFalse :
  surrealIsomorphismConstructed
    canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
  ≡
  false
canonicalCRTMonsterSurrealIsomorphismFalse =
  refl

canonicalCRTMonsterTerminalPromotionFalse :
  terminalPromotionPromoted
    canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt
  ≡
  false
canonicalCRTMonsterTerminalPromotionFalse =
  refl
