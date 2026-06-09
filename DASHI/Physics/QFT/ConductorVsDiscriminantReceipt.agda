module DASHI.Physics.QFT.ConductorVsDiscriminantReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Conductor versus discriminant receipt.
--
-- This receipt separates four often-conflated integers:
--
--   * field discriminant d_K of the imaginary quadratic field K,
--   * order conductor f for the order Z + f O_K,
--   * primitive quadratic Dirichlet-character conductor,
--   * modular/order-discriminant level recorded by this table.
--
-- In particular, D=-8 is a maximal order row: its order conductor is 1
-- because the field discriminant is already -8.  Its primitive Dirichlet
-- character conductor and modular level are 8, not 4.

data ConductorDiscriminantStatus : Set where
  conductorDiscriminantBookkeepingOnly :
    ConductorDiscriminantStatus

data OrderDiscriminant : Set where
  D-3 :
    OrderDiscriminant

  D-4 :
    OrderDiscriminant

  D-7 :
    OrderDiscriminant

  D-8 :
    OrderDiscriminant

  D-11 :
    OrderDiscriminant

  D-12 :
    OrderDiscriminant

data FieldDiscriminant : Set where
  fieldD-3 :
    FieldDiscriminant

  fieldD-4 :
    FieldDiscriminant

  fieldD-7 :
    FieldDiscriminant

  fieldD-8 :
    FieldDiscriminant

  fieldD-11 :
    FieldDiscriminant

fieldDiscriminantOf :
  OrderDiscriminant →
  FieldDiscriminant
fieldDiscriminantOf D-3 =
  fieldD-3
fieldDiscriminantOf D-4 =
  fieldD-4
fieldDiscriminantOf D-7 =
  fieldD-7
fieldDiscriminantOf D-8 =
  fieldD-8
fieldDiscriminantOf D-11 =
  fieldD-11
fieldDiscriminantOf D-12 =
  fieldD-3

orderConductorOf :
  OrderDiscriminant →
  Nat
orderConductorOf D-3 =
  1
orderConductorOf D-4 =
  1
orderConductorOf D-7 =
  1
orderConductorOf D-8 =
  1
orderConductorOf D-11 =
  1
orderConductorOf D-12 =
  2

primitiveDirichletCharacterConductorOf :
  OrderDiscriminant →
  Nat
primitiveDirichletCharacterConductorOf D-3 =
  3
primitiveDirichletCharacterConductorOf D-4 =
  4
primitiveDirichletCharacterConductorOf D-7 =
  7
primitiveDirichletCharacterConductorOf D-8 =
  8
primitiveDirichletCharacterConductorOf D-11 =
  11
primitiveDirichletCharacterConductorOf D-12 =
  3

modularOrderLevelOf :
  OrderDiscriminant →
  Nat
modularOrderLevelOf D-3 =
  3
modularOrderLevelOf D-4 =
  4
modularOrderLevelOf D-7 =
  7
modularOrderLevelOf D-8 =
  8
modularOrderLevelOf D-11 =
  11
modularOrderLevelOf D-12 =
  12

orderDiscriminantAbs :
  OrderDiscriminant →
  Nat
orderDiscriminantAbs D-3 =
  3
orderDiscriminantAbs D-4 =
  4
orderDiscriminantAbs D-7 =
  7
orderDiscriminantAbs D-8 =
  8
orderDiscriminantAbs D-11 =
  11
orderDiscriminantAbs D-12 =
  12

orderFormulaLabel : String
orderFormulaLabel =
  "Order discriminant D = f^2 * d_K, where d_K is the field discriminant and f is the order conductor"

dMinusEightCorrectionLabel : String
dMinusEightCorrectionLabel =
  "D=-8 is maximal: d_K=-8 and f=1; primitive Dirichlet-character conductor and modular level are 8, not 4"

dMinusTwelveClarificationLabel : String
dMinusTwelveClarificationLabel =
  "D=-12 has d_K=-3 and order conductor f=2; primitive quadratic Dirichlet-character conductor is 3 while modular/order level is 12"

record ConductorDiscriminantRow : Set where
  field
    orderDiscriminant :
      OrderDiscriminant

    fieldDiscriminant :
      FieldDiscriminant

    fieldDiscriminantMatchesOrder :
      fieldDiscriminant ≡ fieldDiscriminantOf orderDiscriminant

    orderConductor :
      Nat

    orderConductorMatchesOrder :
      orderConductor ≡ orderConductorOf orderDiscriminant

    dirichletCharacterConductor :
      Nat

    dirichletCharacterConductorMatchesPrimitive :
      dirichletCharacterConductor
      ≡
      primitiveDirichletCharacterConductorOf orderDiscriminant

    modularLevel :
      Nat

    modularLevelMatchesOrderLevel :
      modularLevel ≡ modularOrderLevelOf orderDiscriminant

    orderDiscriminantAbsoluteValue :
      Nat

    orderDiscriminantAbsoluteValueMatches :
      orderDiscriminantAbsoluteValue ≡ orderDiscriminantAbs orderDiscriminant

    rowLabel :
      String

open ConductorDiscriminantRow public

dMinus3Row :
  ConductorDiscriminantRow
dMinus3Row =
  record
    { orderDiscriminant =
        D-3
    ; fieldDiscriminant =
        fieldD-3
    ; fieldDiscriminantMatchesOrder =
        refl
    ; orderConductor =
        1
    ; orderConductorMatchesOrder =
        refl
    ; dirichletCharacterConductor =
        3
    ; dirichletCharacterConductorMatchesPrimitive =
        refl
    ; modularLevel =
        3
    ; modularLevelMatchesOrderLevel =
        refl
    ; orderDiscriminantAbsoluteValue =
        3
    ; orderDiscriminantAbsoluteValueMatches =
        refl
    ; rowLabel =
        "D=-3: d_K=-3, f=1, primitive character conductor=3, modular level=3"
    }

dMinus4Row :
  ConductorDiscriminantRow
dMinus4Row =
  record
    { orderDiscriminant =
        D-4
    ; fieldDiscriminant =
        fieldD-4
    ; fieldDiscriminantMatchesOrder =
        refl
    ; orderConductor =
        1
    ; orderConductorMatchesOrder =
        refl
    ; dirichletCharacterConductor =
        4
    ; dirichletCharacterConductorMatchesPrimitive =
        refl
    ; modularLevel =
        4
    ; modularLevelMatchesOrderLevel =
        refl
    ; orderDiscriminantAbsoluteValue =
        4
    ; orderDiscriminantAbsoluteValueMatches =
        refl
    ; rowLabel =
        "D=-4: d_K=-4, f=1, primitive character conductor=4, modular level=4"
    }

dMinus7Row :
  ConductorDiscriminantRow
dMinus7Row =
  record
    { orderDiscriminant =
        D-7
    ; fieldDiscriminant =
        fieldD-7
    ; fieldDiscriminantMatchesOrder =
        refl
    ; orderConductor =
        1
    ; orderConductorMatchesOrder =
        refl
    ; dirichletCharacterConductor =
        7
    ; dirichletCharacterConductorMatchesPrimitive =
        refl
    ; modularLevel =
        7
    ; modularLevelMatchesOrderLevel =
        refl
    ; orderDiscriminantAbsoluteValue =
        7
    ; orderDiscriminantAbsoluteValueMatches =
        refl
    ; rowLabel =
        "D=-7: d_K=-7, f=1, primitive character conductor=7, modular level=7"
    }

dMinus8Row :
  ConductorDiscriminantRow
dMinus8Row =
  record
    { orderDiscriminant =
        D-8
    ; fieldDiscriminant =
        fieldD-8
    ; fieldDiscriminantMatchesOrder =
        refl
    ; orderConductor =
        1
    ; orderConductorMatchesOrder =
        refl
    ; dirichletCharacterConductor =
        8
    ; dirichletCharacterConductorMatchesPrimitive =
        refl
    ; modularLevel =
        8
    ; modularLevelMatchesOrderLevel =
        refl
    ; orderDiscriminantAbsoluteValue =
        8
    ; orderDiscriminantAbsoluteValueMatches =
        refl
    ; rowLabel =
        "D=-8: d_K=-8, f=1, primitive character conductor=8, modular level=8"
    }

dMinus11Row :
  ConductorDiscriminantRow
dMinus11Row =
  record
    { orderDiscriminant =
        D-11
    ; fieldDiscriminant =
        fieldD-11
    ; fieldDiscriminantMatchesOrder =
        refl
    ; orderConductor =
        1
    ; orderConductorMatchesOrder =
        refl
    ; dirichletCharacterConductor =
        11
    ; dirichletCharacterConductorMatchesPrimitive =
        refl
    ; modularLevel =
        11
    ; modularLevelMatchesOrderLevel =
        refl
    ; orderDiscriminantAbsoluteValue =
        11
    ; orderDiscriminantAbsoluteValueMatches =
        refl
    ; rowLabel =
        "D=-11: d_K=-11, f=1, primitive character conductor=11, modular level=11"
    }

dMinus12Row :
  ConductorDiscriminantRow
dMinus12Row =
  record
    { orderDiscriminant =
        D-12
    ; fieldDiscriminant =
        fieldD-3
    ; fieldDiscriminantMatchesOrder =
        refl
    ; orderConductor =
        2
    ; orderConductorMatchesOrder =
        refl
    ; dirichletCharacterConductor =
        3
    ; dirichletCharacterConductorMatchesPrimitive =
        refl
    ; modularLevel =
        12
    ; modularLevelMatchesOrderLevel =
        refl
    ; orderDiscriminantAbsoluteValue =
        12
    ; orderDiscriminantAbsoluteValueMatches =
        refl
    ; rowLabel =
        "D=-12: d_K=-3, f=2, primitive character conductor=3, modular/order level=12"
    }

canonicalConductorDiscriminantRows :
  List ConductorDiscriminantRow
canonicalConductorDiscriminantRows =
  dMinus3Row
  ∷ dMinus4Row
  ∷ dMinus7Row
  ∷ dMinus8Row
  ∷ dMinus11Row
  ∷ dMinus12Row
  ∷ []

record ConductorVsDiscriminantReceipt : Set where
  field
    status :
      ConductorDiscriminantStatus

    rows :
      List ConductorDiscriminantRow

    rowsAreCanonical :
      rows ≡ canonicalConductorDiscriminantRows

    dMinus3 :
      ConductorDiscriminantRow

    dMinus3IsCanonical :
      dMinus3 ≡ dMinus3Row

    dMinus4 :
      ConductorDiscriminantRow

    dMinus4IsCanonical :
      dMinus4 ≡ dMinus4Row

    dMinus7 :
      ConductorDiscriminantRow

    dMinus7IsCanonical :
      dMinus7 ≡ dMinus7Row

    dMinus8 :
      ConductorDiscriminantRow

    dMinus8IsCanonical :
      dMinus8 ≡ dMinus8Row

    dMinus8OrderConductorIsOne :
      orderConductor dMinus8 ≡ 1

    dMinus8DirichletCharacterConductorIsEight :
      dirichletCharacterConductor dMinus8 ≡ 8

    dMinus8ModularLevelIsEight :
      modularLevel dMinus8 ≡ 8

    dMinus11 :
      ConductorDiscriminantRow

    dMinus11IsCanonical :
      dMinus11 ≡ dMinus11Row

    dMinus12 :
      ConductorDiscriminantRow

    dMinus12IsCanonical :
      dMinus12 ≡ dMinus12Row

    dMinus12FieldDiscriminantIsMinus3 :
      fieldDiscriminant dMinus12 ≡ fieldD-3

    dMinus12OrderConductorIsTwo :
      orderConductor dMinus12 ≡ 2

    dMinus12DirichletCharacterConductorIsThree :
      dirichletCharacterConductor dMinus12 ≡ 3

    dMinus12ModularLevelIsTwelve :
      modularLevel dMinus12 ≡ 12

    formulaStatement :
      String

    formulaStatementIsCanonical :
      formulaStatement ≡ orderFormulaLabel

    dMinusEightCorrection :
      String

    dMinusEightCorrectionIsCanonical :
      dMinusEightCorrection ≡ dMinusEightCorrectionLabel

    dMinusTwelveClarification :
      String

    dMinusTwelveClarificationIsCanonical :
      dMinusTwelveClarification ≡ dMinusTwelveClarificationLabel

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    terminalCompositionPromotion :
      Bool

    terminalCompositionPromotionIsFalse :
      terminalCompositionPromotion ≡ false

    receiptBoundary :
      List String

open ConductorVsDiscriminantReceipt public

canonicalConductorVsDiscriminantReceipt :
  ConductorVsDiscriminantReceipt
canonicalConductorVsDiscriminantReceipt =
  record
    { status =
        conductorDiscriminantBookkeepingOnly
    ; rows =
        canonicalConductorDiscriminantRows
    ; rowsAreCanonical =
        refl
    ; dMinus3 =
        dMinus3Row
    ; dMinus3IsCanonical =
        refl
    ; dMinus4 =
        dMinus4Row
    ; dMinus4IsCanonical =
        refl
    ; dMinus7 =
        dMinus7Row
    ; dMinus7IsCanonical =
        refl
    ; dMinus8 =
        dMinus8Row
    ; dMinus8IsCanonical =
        refl
    ; dMinus8OrderConductorIsOne =
        refl
    ; dMinus8DirichletCharacterConductorIsEight =
        refl
    ; dMinus8ModularLevelIsEight =
        refl
    ; dMinus11 =
        dMinus11Row
    ; dMinus11IsCanonical =
        refl
    ; dMinus12 =
        dMinus12Row
    ; dMinus12IsCanonical =
        refl
    ; dMinus12FieldDiscriminantIsMinus3 =
        refl
    ; dMinus12OrderConductorIsTwo =
        refl
    ; dMinus12DirichletCharacterConductorIsThree =
        refl
    ; dMinus12ModularLevelIsTwelve =
        refl
    ; formulaStatement =
        orderFormulaLabel
    ; formulaStatementIsCanonical =
        refl
    ; dMinusEightCorrection =
        dMinusEightCorrectionLabel
    ; dMinusEightCorrectionIsCanonical =
        refl
    ; dMinusTwelveClarification =
        dMinusTwelveClarificationLabel
    ; dMinusTwelveClarificationIsCanonical =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; terminalCompositionPromotion =
        false
    ; terminalCompositionPromotionIsFalse =
        refl
    ; receiptBoundary =
        orderFormulaLabel
        ∷ dMinusEightCorrectionLabel
        ∷ dMinusTwelveClarificationLabel
        ∷ "This is bookkeeping only; all exact SM, G_DHR ~= G_SM, and terminal promotions remain false"
        ∷ []
    }

dMinusEightOrderConductorCorrected :
  orderConductor dMinus8Row ≡ 1
dMinusEightOrderConductorCorrected =
  refl

dMinusEightDirichletConductorNotFour :
  dirichletCharacterConductor dMinus8Row ≡ 8
dMinusEightDirichletConductorNotFour =
  refl

dMinusEightModularLevelNotFour :
  modularLevel dMinus8Row ≡ 8
dMinusEightModularLevelNotFour =
  refl

dMinusTwelveSeparatesFieldAndOrderConductors :
  fieldDiscriminant dMinus12Row ≡ fieldD-3
dMinusTwelveSeparatesFieldAndOrderConductors =
  refl

conductorVsDiscriminantNoExactSMPromotion :
  exactStandardModelPromotion canonicalConductorVsDiscriminantReceipt
  ≡
  false
conductorVsDiscriminantNoExactSMPromotion =
  refl

conductorVsDiscriminantNoExactGDHRGSMPromotion :
  exactGDHREqualsGSMPromotion canonicalConductorVsDiscriminantReceipt
  ≡
  false
conductorVsDiscriminantNoExactGDHRGSMPromotion =
  refl

conductorVsDiscriminantNoTerminalClaimPromotion :
  terminalClaimPromoted canonicalConductorVsDiscriminantReceipt
  ≡
  false
conductorVsDiscriminantNoTerminalClaimPromotion =
  refl

conductorVsDiscriminantNoTerminalCompositionPromotion :
  terminalCompositionPromotion canonicalConductorVsDiscriminantReceipt
  ≡
  false
conductorVsDiscriminantNoTerminalCompositionPromotion =
  refl
