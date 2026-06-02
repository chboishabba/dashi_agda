module DASHI.Physics.Closure.PressureDepthLengthTripleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Pressure/depth/length triple.
--
-- This receipt separates three quantities that were previously conflated:
--
--   Length   L = sum_p v_p log p = log n
--   Depth    D = sum_p v_p       = Omega(n)
--   Pressure P = sum_p v_p * (1 - absorbed_p)
--
-- Forward carrier steps make length/depth monotone bookkeeping quantities.
-- Pressure is deliberately non-monotone: new unresolved carry can increase it,
-- while absorption decreases it.  Absorption conserves the carry budget by
-- transporting pressure into depth:
--
--   DeltaP = -absorbed_carry, DeltaD = +absorbed_carry, DeltaL = 0.
--
-- The NS and YM clauses below are interpretation guards.  They prevent the LP
-- pressure identity from being read as a depth identity and prevent Balaban/KP
-- pressure control from being promoted directly to a Clay theorem.

data TripleStatus : Set where
  pressureDepthLengthSeparated_noPhysicsPromotion :
    TripleStatus

data CarrierQuantity : Set where
  length :
    CarrierQuantity

  depth :
    CarrierQuantity

  pressure :
    CarrierQuantity

canonicalCarrierQuantities :
  List CarrierQuantity
canonicalCarrierQuantities =
  length
  ∷ depth
  ∷ pressure
  ∷ []

data QuantityFormula : Set where
  lengthIsSumVpLogPAndLogN :
    QuantityFormula

  depthIsSumVpAndOmegaN :
    QuantityFormula

  pressureIsUnabsorbedCarry :
    QuantityFormula

canonicalQuantityFormulas :
  List QuantityFormula
canonicalQuantityFormulas =
  lengthIsSumVpLogPAndLogN
  ∷ depthIsSumVpAndOmegaN
  ∷ pressureIsUnabsorbedCarry
  ∷ []

data ForwardCarrierStepLaw : Set where
  lengthMonotoneUnderForwardCarrierSteps :
    ForwardCarrierStepLaw

  depthMonotoneUnderForwardCarrierSteps :
    ForwardCarrierStepLaw

  pressureNonMonotoneUnderForwardCarrierSteps :
    ForwardCarrierStepLaw

canonicalForwardCarrierStepLaws :
  List ForwardCarrierStepLaw
canonicalForwardCarrierStepLaws =
  lengthMonotoneUnderForwardCarrierSteps
  ∷ depthMonotoneUnderForwardCarrierSteps
  ∷ pressureNonMonotoneUnderForwardCarrierSteps
  ∷ []

data PressureDirection : Set where
  pressureCanIncreaseByNewUnresolvedCarry :
    PressureDirection

  pressureCanDecreaseByAbsorption :
    PressureDirection

canonicalPressureDirections :
  List PressureDirection
canonicalPressureDirections =
  pressureCanIncreaseByNewUnresolvedCarry
  ∷ pressureCanDecreaseByAbsorption
  ∷ []

data SignedCarrierDelta : Set where
  minusAbsorbedCarry :
    SignedCarrierDelta

  plusAbsorbedCarry :
    SignedCarrierDelta

  zeroAbsorptionDelta :
    SignedCarrierDelta

record AbsorptionConservation : Set where
  field
    deltaP :
      SignedCarrierDelta

    deltaPIsMinusAbsorbedCarry :
      deltaP ≡ minusAbsorbedCarry

    deltaD :
      SignedCarrierDelta

    deltaDIsPlusAbsorbedCarry :
      deltaD ≡ plusAbsorbedCarry

    deltaL :
      SignedCarrierDelta

    deltaLIsZero :
      deltaL ≡ zeroAbsorptionDelta

open AbsorptionConservation public

canonicalAbsorptionConservation :
  AbsorptionConservation
canonicalAbsorptionConservation =
  record
    { deltaP =
        minusAbsorbedCarry
    ; deltaPIsMinusAbsorbedCarry =
        refl
    ; deltaD =
        plusAbsorbedCarry
    ; deltaDIsPlusAbsorbedCarry =
        refl
    ; deltaL =
        zeroAbsorptionDelta
    ; deltaLIsZero =
        refl
    }

data NSInstantiationClause : Set where
  eGreaterThanKStarMeasuresDepth :
    NSInstantiationClause

  thetaMeasuresPressureDynamics :
    NSInstantiationClause

  lpIdentityIsPressureIdentity :
    NSInstantiationClause

  lpIdentityIsNotDepthIdentity :
    NSInstantiationClause

canonicalNSInstantiationClauses :
  List NSInstantiationClause
canonicalNSInstantiationClauses =
  eGreaterThanKStarMeasuresDepth
  ∷ thetaMeasuresPressureDynamics
  ∷ lpIdentityIsPressureIdentity
  ∷ lpIdentityIsNotDepthIdentity
  ∷ []

data YMInstantiationClause : Set where
  zGammaIsPolymerPressure :
    YMInstantiationClause

  kpIsPressureSummability :
    YMInstantiationClause

  balabanRGIsPressureToDepthConversion :
    YMInstantiationClause

canonicalYMInstantiationClauses :
  List YMInstantiationClause
canonicalYMInstantiationClauses =
  zGammaIsPolymerPressure
  ∷ kpIsPressureSummability
  ∷ balabanRGIsPressureToDepthConversion
  ∷ []

data NonPromotionBoundary : Set where
  noNavierStokesClayPromotion :
    NonPromotionBoundary

  noYangMillsClayPromotion :
    NonPromotionBoundary

  noGate3ClosurePromotion :
    NonPromotionBoundary

  noLPDepthIdentityPromotion :
    NonPromotionBoundary

canonicalNonPromotionBoundaries :
  List NonPromotionBoundary
canonicalNonPromotionBoundaries =
  noNavierStokesClayPromotion
  ∷ noYangMillsClayPromotion
  ∷ noGate3ClosurePromotion
  ∷ noLPDepthIdentityPromotion
  ∷ []

data TriplePromotion : Set where

triplePromotionImpossibleHere :
  TriplePromotion →
  ⊥
triplePromotionImpossibleHere ()

lengthFormula :
  String
lengthFormula =
  "Length L = sum_p v_p log p = log n."

depthFormula :
  String
depthFormula =
  "Depth D = sum_p v_p = Omega(n)."

pressureFormula :
  String
pressureFormula =
  "Pressure P = sum_p v_p*(1-absorbed_p)."

forwardStepFormula :
  String
forwardStepFormula =
  "Under forward carrier steps, L and D are monotone bookkeeping quantities; P is non-monotone."

absorptionFormula :
  String
absorptionFormula =
  "Absorption conservation: DeltaP=-absorbed_carry, DeltaD=+absorbed_carry, DeltaL=0."

nsInstantiationFormula :
  String
nsInstantiationFormula =
  "NS: E_{>K*} measures depth, theta measures pressure dynamics, and the LP identity is a pressure identity, not a depth identity."

ymInstantiationFormula :
  String
ymInstantiationFormula =
  "YM: z(Gamma) is polymer pressure, KP is pressure summability, and Balaban RG is pressure-to-depth conversion."

boundaryFormula :
  String
boundaryFormula =
  "This receipt is correction grammar only: no NS Clay promotion, no YM Clay promotion, and no Gate3 closure."

record PressureDepthLengthTripleReceipt : Setω where
  field
    status :
      TripleStatus

    statusIsCanonical :
      status ≡ pressureDepthLengthSeparated_noPhysicsPromotion

    quantities :
      List CarrierQuantity

    quantitiesAreCanonical :
      quantities ≡ canonicalCarrierQuantities

    formulas :
      List QuantityFormula

    formulasAreCanonical :
      formulas ≡ canonicalQuantityFormulas

    forwardCarrierStepLaws :
      List ForwardCarrierStepLaw

    forwardCarrierStepLawsAreCanonical :
      forwardCarrierStepLaws ≡ canonicalForwardCarrierStepLaws

    pressureDirections :
      List PressureDirection

    pressureDirectionsAreCanonical :
      pressureDirections ≡ canonicalPressureDirections

    absorptionConservation :
      AbsorptionConservation

    absorptionConservationIsCanonical :
      absorptionConservation ≡ canonicalAbsorptionConservation

    nsInstantiation :
      List NSInstantiationClause

    nsInstantiationIsCanonical :
      nsInstantiation ≡ canonicalNSInstantiationClauses

    ymInstantiation :
      List YMInstantiationClause

    ymInstantiationIsCanonical :
      ymInstantiation ≡ canonicalYMInstantiationClauses

    nonPromotionBoundaries :
      List NonPromotionBoundary

    nonPromotionBoundariesAreCanonical :
      nonPromotionBoundaries ≡ canonicalNonPromotionBoundaries

    lengthStatement :
      String

    lengthStatementIsCanonical :
      lengthStatement ≡ lengthFormula

    depthStatement :
      String

    depthStatementIsCanonical :
      depthStatement ≡ depthFormula

    pressureStatement :
      String

    pressureStatementIsCanonical :
      pressureStatement ≡ pressureFormula

    forwardStepStatement :
      String

    forwardStepStatementIsCanonical :
      forwardStepStatement ≡ forwardStepFormula

    absorptionStatement :
      String

    absorptionStatementIsCanonical :
      absorptionStatement ≡ absorptionFormula

    nsInstantiationStatement :
      String

    nsInstantiationStatementIsCanonical :
      nsInstantiationStatement ≡ nsInstantiationFormula

    ymInstantiationStatement :
      String

    ymInstantiationStatementIsCanonical :
      ymInstantiationStatement ≡ ymInstantiationFormula

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ boundaryFormula

    lengthDepthPressureDistinguished :
      Bool

    lengthDepthPressureDistinguishedIsTrue :
      lengthDepthPressureDistinguished ≡ true

    lengthForwardCarrierStepsMonotone :
      Bool

    lengthForwardCarrierStepsMonotoneIsTrue :
      lengthForwardCarrierStepsMonotone ≡ true

    depthForwardCarrierStepsMonotone :
      Bool

    depthForwardCarrierStepsMonotoneIsTrue :
      depthForwardCarrierStepsMonotone ≡ true

    pressureNonMonotone :
      Bool

    pressureNonMonotoneIsTrue :
      pressureNonMonotone ≡ true

    absorptionDeltaPIsMinusAbsorbedCarry :
      deltaP absorptionConservation ≡ minusAbsorbedCarry

    absorptionDeltaDIsPlusAbsorbedCarry :
      deltaD absorptionConservation ≡ plusAbsorbedCarry

    absorptionDeltaLIsZero :
      deltaL absorptionConservation ≡ zeroAbsorptionDelta

    nsEGreaterThanKStarMeasuresDepth :
      Bool

    nsEGreaterThanKStarMeasuresDepthIsTrue :
      nsEGreaterThanKStarMeasuresDepth ≡ true

    nsThetaMeasuresPressureDynamics :
      Bool

    nsThetaMeasuresPressureDynamicsIsTrue :
      nsThetaMeasuresPressureDynamics ≡ true

    nsLPIdentityIsPressureIdentity :
      Bool

    nsLPIdentityIsPressureIdentityIsTrue :
      nsLPIdentityIsPressureIdentity ≡ true

    nsLPIdentityIsDepthIdentity :
      Bool

    nsLPIdentityIsDepthIdentityIsFalse :
      nsLPIdentityIsDepthIdentity ≡ false

    ymZGammaIsPolymerPressure :
      Bool

    ymZGammaIsPolymerPressureIsTrue :
      ymZGammaIsPolymerPressure ≡ true

    ymKPIsPressureSummability :
      Bool

    ymKPIsPressureSummabilityIsTrue :
      ymKPIsPressureSummability ≡ true

    ymBalabanRGIsPressureToDepthConversion :
      Bool

    ymBalabanRGIsPressureToDepthConversionIsTrue :
      ymBalabanRGIsPressureToDepthConversion ≡ true

    dangerShellMaxPrincipleIsPressureTheorem :
      Bool

    dangerShellMaxPrincipleIsPressureTheoremIsTrue :
      dangerShellMaxPrincipleIsPressureTheorem ≡ true

    nsPressureEquationProved :
      Bool

    nsPressureEquationProvedIsFalse :
      nsPressureEquationProved ≡ false

    ymAreaLawProved :
      Bool

    ymAreaLawProvedIsFalse :
      ymAreaLawProved ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    promotions :
      List TriplePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      TriplePromotion →
      ⊥

open PressureDepthLengthTripleReceipt public

canonicalPressureDepthLengthTripleReceipt :
  PressureDepthLengthTripleReceipt
canonicalPressureDepthLengthTripleReceipt =
  record
    { status =
        pressureDepthLengthSeparated_noPhysicsPromotion
    ; statusIsCanonical =
        refl
    ; quantities =
        canonicalCarrierQuantities
    ; quantitiesAreCanonical =
        refl
    ; formulas =
        canonicalQuantityFormulas
    ; formulasAreCanonical =
        refl
    ; forwardCarrierStepLaws =
        canonicalForwardCarrierStepLaws
    ; forwardCarrierStepLawsAreCanonical =
        refl
    ; pressureDirections =
        canonicalPressureDirections
    ; pressureDirectionsAreCanonical =
        refl
    ; absorptionConservation =
        canonicalAbsorptionConservation
    ; absorptionConservationIsCanonical =
        refl
    ; nsInstantiation =
        canonicalNSInstantiationClauses
    ; nsInstantiationIsCanonical =
        refl
    ; ymInstantiation =
        canonicalYMInstantiationClauses
    ; ymInstantiationIsCanonical =
        refl
    ; nonPromotionBoundaries =
        canonicalNonPromotionBoundaries
    ; nonPromotionBoundariesAreCanonical =
        refl
    ; lengthStatement =
        lengthFormula
    ; lengthStatementIsCanonical =
        refl
    ; depthStatement =
        depthFormula
    ; depthStatementIsCanonical =
        refl
    ; pressureStatement =
        pressureFormula
    ; pressureStatementIsCanonical =
        refl
    ; forwardStepStatement =
        forwardStepFormula
    ; forwardStepStatementIsCanonical =
        refl
    ; absorptionStatement =
        absorptionFormula
    ; absorptionStatementIsCanonical =
        refl
    ; nsInstantiationStatement =
        nsInstantiationFormula
    ; nsInstantiationStatementIsCanonical =
        refl
    ; ymInstantiationStatement =
        ymInstantiationFormula
    ; ymInstantiationStatementIsCanonical =
        refl
    ; boundaryStatement =
        boundaryFormula
    ; boundaryStatementIsCanonical =
        refl
    ; lengthDepthPressureDistinguished =
        true
    ; lengthDepthPressureDistinguishedIsTrue =
        refl
    ; lengthForwardCarrierStepsMonotone =
        true
    ; lengthForwardCarrierStepsMonotoneIsTrue =
        refl
    ; depthForwardCarrierStepsMonotone =
        true
    ; depthForwardCarrierStepsMonotoneIsTrue =
        refl
    ; pressureNonMonotone =
        true
    ; pressureNonMonotoneIsTrue =
        refl
    ; absorptionDeltaPIsMinusAbsorbedCarry =
        refl
    ; absorptionDeltaDIsPlusAbsorbedCarry =
        refl
    ; absorptionDeltaLIsZero =
        refl
    ; nsEGreaterThanKStarMeasuresDepth =
        true
    ; nsEGreaterThanKStarMeasuresDepthIsTrue =
        refl
    ; nsThetaMeasuresPressureDynamics =
        true
    ; nsThetaMeasuresPressureDynamicsIsTrue =
        refl
    ; nsLPIdentityIsPressureIdentity =
        true
    ; nsLPIdentityIsPressureIdentityIsTrue =
        refl
    ; nsLPIdentityIsDepthIdentity =
        false
    ; nsLPIdentityIsDepthIdentityIsFalse =
        refl
    ; ymZGammaIsPolymerPressure =
        true
    ; ymZGammaIsPolymerPressureIsTrue =
        refl
    ; ymKPIsPressureSummability =
        true
    ; ymKPIsPressureSummabilityIsTrue =
        refl
    ; ymBalabanRGIsPressureToDepthConversion =
        true
    ; ymBalabanRGIsPressureToDepthConversionIsTrue =
        refl
    ; dangerShellMaxPrincipleIsPressureTheorem =
        true
    ; dangerShellMaxPrincipleIsPressureTheoremIsTrue =
        refl
    ; nsPressureEquationProved =
        false
    ; nsPressureEquationProvedIsFalse =
        refl
    ; ymAreaLawProved =
        false
    ; ymAreaLawProvedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        triplePromotionImpossibleHere
    }

canonicalTripleNoClayPromotion :
  clayPromotion canonicalPressureDepthLengthTripleReceipt ≡ false
canonicalTripleNoClayPromotion =
  refl

canonicalTripleDangerShellPressureTheorem :
  dangerShellMaxPrincipleIsPressureTheorem
    canonicalPressureDepthLengthTripleReceipt
  ≡ true
canonicalTripleDangerShellPressureTheorem =
  refl

canonicalTripleLPIdentityNotDepthIdentity :
  nsLPIdentityIsDepthIdentity canonicalPressureDepthLengthTripleReceipt
  ≡ false
canonicalTripleLPIdentityNotDepthIdentity =
  refl
