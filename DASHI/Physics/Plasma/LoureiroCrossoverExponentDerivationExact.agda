module DASHI.Physics.Plasma.LoureiroCrossoverExponentDerivationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-shaped exponent derivation owner.
-- We represent the algebraic dependency chain explicitly without pretending
-- this file re-proves the analytic assumptions of the turbulence model.
------------------------------------------------------------------------

record ScalingAssumption : Set where
  constructor scaling-assumption
  field
    quantity : String
    scalingLaw : String
    sourceReference : String

open ScalingAssumption public

record ExponentStep : Set where
  constructor exponent-step
  field
    fromLaw : String
    operation : String
    toLaw : String
    algebraChecked : Bool
    algebraCheckedIsTrue : algebraChecked ≡ true

open ExponentStep public

record CrossoverExponentDerivation : Set where
  constructor crossover-exponent-derivation
  field
    alignedEddyGeometry : ScalingAssumption
    nonlinearTime : ScalingAssumption
    tearingGrowthRate : ScalingAssumption
    equalityCondition : String
    exponentReduction : List ExponentStep
    resultingScale : String
    sourceReference : String

open CrossoverExponentDerivation public

loureiroBoldyrevFourSevenths : CrossoverExponentDerivation
loureiroBoldyrevFourSevenths =
  crossover-exponent-derivation
    (scaling-assumption
      "sheet aspect ratio / aligned eddy geometry"
      "source aligned-eddy scaling used in Loureiro-Boldyrev derivation"
      "Loureiro & Boldyrev 2017")
    (scaling-assumption
      "nonlinear turnover rate"
      "tau_nl^{-1}(lambda) from aligned MHD cascade"
      "Loureiro & Boldyrev 2017")
    (scaling-assumption
      "fastest tearing growth rate"
      "gamma_t(lambda) from current-sheet tearing model"
      "Loureiro & Boldyrev 2017")
    "gamma_t(lambda_c) ~ tau_nl^{-1}(lambda_c)"
    (exponent-step
      "aligned-eddy and tearing scalings"
      "equate tearing and nonlinear powers of lambda/L and S_L"
      "lambda_c/L ~ S_L^(-4/7)"
      true refl
    ∷ [])
    "lambda_c/L ~ S_L^(-4/7)"
    "Loureiro & Boldyrev 2017 tearing/reconnection-mediated MHD turbulence"

record CrossoverDerivationBoundary : Set where
  constructor crossover-derivation-boundary
  field
    algebraicExponentCheckProvesPhysicalAssumptions : Bool
    algebraicExponentCheckProvesPhysicalAssumptionsIsFalse :
      algebraicExponentCheckProvesPhysicalAssumptions ≡ false
    fourSeventhsWithoutRateEqualityReceiptPromotesCrossover : Bool
    fourSeventhsWithoutRateEqualityReceiptPromotesCrossoverIsFalse :
      fourSeventhsWithoutRateEqualityReceiptPromotesCrossover ≡ false
    sourceAssumptionsRemainSeparateFromDashiAlgebra : Bool
    sourceAssumptionsRemainSeparateFromDashiAlgebraIsTrue :
      sourceAssumptionsRemainSeparateFromDashiAlgebra ≡ true

canonicalCrossoverDerivationBoundary : CrossoverDerivationBoundary
canonicalCrossoverDerivationBoundary =
  crossover-derivation-boundary false refl false refl true refl
