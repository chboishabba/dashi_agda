module DASHI.Physics.Plasma.LoureiroTearingCrossoverCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record RationalExponent : Set where
  constructor rational-exponent
  field numerator denominator : Nat
open RationalExponent public

minusFourSevenths : RationalExponent
minusFourSevenths = rational-exponent 4 7

minusFiveHalves : RationalExponent
minusFiveHalves = rational-exponent 5 2

minusElevenFifths : RationalExponent
minusElevenFifths = rational-exponent 11 5

record TearingCrossoverScaling : Set where
  constructor tearing-crossover-scaling
  field
    crossoverScaleLaw : String
    spectralLaw : String
    crossoverExponentMagnitude : RationalExponent
    spectralExponentMagnitude : RationalExponent
    sourceReference : String

open TearingCrossoverScaling public

loureiroBoldyrev2017 : TearingCrossoverScaling
loureiroBoldyrev2017 = tearing-crossover-scaling
  "lambda_c / L ~ S_L^(-4/7)"
  "E(k_perp) ~ k_perp^(-5/2) in the reconnection interval"
  minusFourSevenths
  minusFiveHalves
  "Loureiro & Boldyrev 2017, collision of nonlinear and tearing times"

boldyrevLoureiroBetaZero : TearingCrossoverScaling
boldyrevLoureiroBetaZero = tearing-crossover-scaling
  "lambda_* ~ L_0 S_0^(-3/4)"
  "E(k_perp) ~ k_perp^(-11/5) for beta = 0"
  (rational-exponent 3 4)
  minusElevenFifths
  "Boldyrev & Loureiro tearing-mediated turbulence model"

record TearingCompetitionReceipt : Set where
  constructor tearing-competition-receipt
  field
    nonlinearRate : String
    tearingRate : String
    crossoverCondition : String
    currentSheetGeometrySpecified : Bool
    currentSheetGeometrySpecifiedIsTrue : currentSheetGeometrySpecified ≡ true
    dissipationModelSpecified : Bool
    dissipationModelSpecifiedIsTrue : dissipationModelSpecified ≡ true

open TearingCompetitionReceipt public

record TearingCrossoverBoundary : Set where
  constructor tearing-crossover-boundary
  field
    sheetLikeEddyIsAlreadyReconnected : Bool
    sheetLikeEddyIsAlreadyReconnectedIsFalse : sheetLikeEddyIsAlreadyReconnected ≡ false
    oneSpectralExponentUniversalAcrossDissipationModels : Bool
    oneSpectralExponentUniversalAcrossDissipationModelsIsFalse :
      oneSpectralExponentUniversalAcrossDissipationModels ≡ false
    observedMinusFiveHalvesAloneProvesTearingMediation : Bool
    observedMinusFiveHalvesAloneProvesTearingMediationIsFalse :
      observedMinusFiveHalvesAloneProvesTearingMediation ≡ false
    crossoverNeedsRateCompetitionReceipt : Bool
    crossoverNeedsRateCompetitionReceiptIsTrue : crossoverNeedsRateCompetitionReceipt ≡ true

canonicalTearingCrossoverBoundary : TearingCrossoverBoundary
canonicalTearingCrossoverBoundary = tearing-crossover-boundary false refl false refl false refl true refl
