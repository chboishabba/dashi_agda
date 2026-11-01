module DASHI.Physics.Closure.YMSprint92MasterWC3AdjointCorrectionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; _*_; _^_; _<ᵇ_)

import DASHI.Physics.Closure.YMSprint91WC3NewMathReceipt as Sprint91

------------------------------------------------------------------------
-- Sprint 92 master-WC3 adjoint-scaling correction.
--
-- The row-sum condition is 18*C_local < exp(-4).  The SU(3) adjoint penalty
-- must be applied to C_local before that row sum is formed.  With the naive
-- SU(2) base C_local(k) <= 1/(2*2^k), this gives
--
--   SU(2), k=9:  C = 1/(2*512),        18*C < exp(-4), passes.
--   SU(3), k=9:  C = 2.25/(2*512),     18*C < exp(-4), fails.
--   SU(3), k=10: C = 2.25/(2*1024),    18*C < exp(-4), fails.
--   SU(3), k=11: C = 2.25/(2*2048),    18*C < exp(-4), passes.
--
-- This module deliberately keeps the analytic CMP98/CMP116 witnesses
-- uninhabited.  It closes only the corrected arithmetic boundary.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

su2K9RowSumArithmeticPasses : Bool
su2K9RowSumArithmeticPasses = true

su3K9RowSumArithmeticFails : Bool
su3K9RowSumArithmeticFails = true

su3K10RowSumArithmeticFails : Bool
su3K10RowSumArithmeticFails = true

su3K11RowSumArithmeticPasses : Bool
su3K11RowSumArithmeticPasses = true

adjointScalingCorrectionRecordedInRepo : Bool
adjointScalingCorrectionRecordedInRepo = true

balabanQhpLocalConstantBoundDerivedInRepo : Bool
balabanQhpLocalConstantBoundDerivedInRepo = false

balabanCMP116PolymerMassBoundDerivedInRepo : Bool
balabanCMP116PolymerMassBoundDerivedInRepo = false

adjointRepresentationSharperBoundDerivedInRepo : Bool
adjointRepresentationSharperBoundDerivedInRepo = false

blockingDepthK11PhysicallyValidatedInRepo : Bool
blockingDepthK11PhysicallyValidatedInRepo = false

weakCouplingWindowSU3DerivedInRepo : Bool
weakCouplingWindowSU3DerivedInRepo = false

masterWC3ConditionSU2AtK9DerivedInRepo : Bool
masterWC3ConditionSU2AtK9DerivedInRepo = false

masterWC3ConditionSU3DerivedInRepo : Bool
masterWC3ConditionSU3DerivedInRepo = false

wc3UniformClusterSummabilitySU3DerivedInRepo : Bool
wc3UniformClusterSummabilitySU3DerivedInRepo = false

noSpectralPollutionUnconditionalDerivedInRepo : Bool
noSpectralPollutionUnconditionalDerivedInRepo = false

twoToNine : ℕ
twoToNine = 2 ^ 9

twoToTen : ℕ
twoToTen = 2 ^ 10

twoToEleven : ℕ
twoToEleven = 2 ^ 11

decimalDenominator : ℕ
decimalDenominator = 1000000000

-- Decimal enclosure for exp(-4):
--
--   0.018315638 < exp(-4) < 0.018315639

expMinus4LowerNumerator : ℕ
expMinus4LowerNumerator = 18315638

expMinus4UpperNumerator : ℕ
expMinus4UpperNumerator = 18315639

-- Row-sum numerators/denominators for 18*C_local.

su2K9RowNumerator : ℕ
su2K9RowNumerator = 18

su2K9RowDenominator : ℕ
su2K9RowDenominator = 2 * twoToNine

su3RowNumerator : ℕ
su3RowNumerator = 162

su3K9RowDenominator : ℕ
su3K9RowDenominator = 8 * twoToNine

su3K10RowDenominator : ℕ
su3K10RowDenominator = 8 * twoToTen

su3K11RowDenominator : ℕ
su3K11RowDenominator = 8 * twoToEleven

-- Passing checks use the lower decimal bound for exp(-4).

su2K9PassLeft : ℕ
su2K9PassLeft = su2K9RowNumerator * decimalDenominator

su2K9PassRight : ℕ
su2K9PassRight = expMinus4LowerNumerator * su2K9RowDenominator

su3K11PassLeft : ℕ
su3K11PassLeft = su3RowNumerator * decimalDenominator

su3K11PassRight : ℕ
su3K11PassRight = expMinus4LowerNumerator * su3K11RowDenominator

-- Failing checks use the upper decimal bound for exp(-4) and show
-- exp(-4)'s upper enclosure is already below the row sum.

su3K9FailLeft : ℕ
su3K9FailLeft = expMinus4UpperNumerator * su3K9RowDenominator

su3K9FailRight : ℕ
su3K9FailRight = su3RowNumerator * decimalDenominator

su3K10FailLeft : ℕ
su3K10FailLeft = expMinus4UpperNumerator * su3K10RowDenominator

su3K10FailRight : ℕ
su3K10FailRight = su3RowNumerator * decimalDenominator

su2K9IntegerInequalityCheck :
  (su2K9PassLeft <ᵇ su2K9PassRight) ≡ true
su2K9IntegerInequalityCheck = refl

su3K9IntegerFailureCheck :
  (su3K9FailLeft <ᵇ su3K9FailRight) ≡ true
su3K9IntegerFailureCheck = refl

su3K10IntegerFailureCheck :
  (su3K10FailLeft <ᵇ su3K10FailRight) ≡ true
su3K10IntegerFailureCheck = refl

su3K11IntegerInequalityCheck :
  (su3K11PassLeft <ᵇ su3K11PassRight) ≡ true
su3K11IntegerInequalityCheck = refl

Sprint92AdjointCorrectionFormula : String
Sprint92AdjointCorrectionFormula =
  "The SU3 adjoint factor is applied before the row sum: C_local_SU3(k)=2.25/(2*2^k). Thus k=10 gives 18*C=0.019775390625 > exp(-4), so it fails; k=11 gives 18*C=0.0098876953125 < exp(-4), so the arithmetic passes."

Sprint92SU2MarginFormula : String
Sprint92SU2MarginFormula =
  "SU2 k=9 has 18/(2*512)=0.017578125 < exp(-4)=0.018315638888..., equivalently m0=-log(row)=4.0407..., a tight positive margin above 4."

Sprint92OpenAnalyticWitnessFormula : String
Sprint92OpenAnalyticWitnessFormula =
  "The open analytic witnesses are BalabanQhpLocalConstantBound, BalabanCMP116PolymerMassBound, and either AdjointRepresentationSharperBound or BlockingDepthK11PhysicalValidation plus WeakCouplingWindowSU3."

data BalabanQhpLocalConstantBoundWitness : Set where

balabanQhpLocalConstantBoundWitnessImpossibleHere :
  BalabanQhpLocalConstantBoundWitness →
  ⊥
balabanQhpLocalConstantBoundWitnessImpossibleHere ()

data BalabanCMP116PolymerMassBoundWitness : Set where

balabanCMP116PolymerMassBoundWitnessImpossibleHere :
  BalabanCMP116PolymerMassBoundWitness →
  ⊥
balabanCMP116PolymerMassBoundWitnessImpossibleHere ()

data AdjointRepresentationSharperBoundWitness : Set where

adjointRepresentationSharperBoundWitnessImpossibleHere :
  AdjointRepresentationSharperBoundWitness →
  ⊥
adjointRepresentationSharperBoundWitnessImpossibleHere ()

data BlockingDepthK11PhysicalValidationWitness : Set where

blockingDepthK11PhysicalValidationWitnessImpossibleHere :
  BlockingDepthK11PhysicalValidationWitness →
  ⊥
blockingDepthK11PhysicalValidationWitnessImpossibleHere ()

data WeakCouplingWindowSU3Witness : Set where

weakCouplingWindowSU3WitnessImpossibleHere :
  WeakCouplingWindowSU3Witness →
  ⊥
weakCouplingWindowSU3WitnessImpossibleHere ()

data WC3UniformClusterSummabilitySU3Witness : Set where
  wc3SU3FromSharperAdjoint :
    BalabanQhpLocalConstantBoundWitness →
    BalabanCMP116PolymerMassBoundWitness →
    AdjointRepresentationSharperBoundWitness →
    WeakCouplingWindowSU3Witness →
    WC3UniformClusterSummabilitySU3Witness
  wc3SU3FromK11Blocking :
    BalabanQhpLocalConstantBoundWitness →
    BalabanCMP116PolymerMassBoundWitness →
    BlockingDepthK11PhysicalValidationWitness →
    WeakCouplingWindowSU3Witness →
    WC3UniformClusterSummabilitySU3Witness

wc3UniformClusterSummabilitySU3WitnessNotExported :
  WC3UniformClusterSummabilitySU3Witness →
  ⊥
wc3UniformClusterSummabilitySU3WitnessNotExported
  (wc3SU3FromSharperAdjoint qhp _ _ _) =
  balabanQhpLocalConstantBoundWitnessImpossibleHere qhp
wc3UniformClusterSummabilitySU3WitnessNotExported
  (wc3SU3FromK11Blocking qhp _ _ _) =
  balabanQhpLocalConstantBoundWitnessImpossibleHere qhp

record CorrectedRowSumArithmetic : Set where
  constructor mkCorrectedRowSumArithmetic
  field
    sprint91ArchitectureAvailable :
      Sprint91.cauchySchwarzLinearDobrushinStepClosedInRepo ≡ true
    adjointCorrectionRecorded :
      adjointScalingCorrectionRecordedInRepo ≡ true
    su2K9Passes :
      su2K9RowSumArithmeticPasses ≡ true
    su3K9Fails :
      su3K9RowSumArithmeticFails ≡ true
    su3K10Fails :
      su3K10RowSumArithmeticFails ≡ true
    su3K11Passes :
      su3K11RowSumArithmeticPasses ≡ true
    su2K9IntegerCheck :
      (su2K9PassLeft <ᵇ su2K9PassRight) ≡ true
    su3K9IntegerFailure :
      (su3K9FailLeft <ᵇ su3K9FailRight) ≡ true
    su3K10IntegerFailure :
      (su3K10FailLeft <ᵇ su3K10FailRight) ≡ true
    su3K11IntegerCheck :
      (su3K11PassLeft <ᵇ su3K11PassRight) ≡ true
    correctionFormula :
      Sprint92AdjointCorrectionFormula ≡
      "The SU3 adjoint factor is applied before the row sum: C_local_SU3(k)=2.25/(2*2^k). Thus k=10 gives 18*C=0.019775390625 > exp(-4), so it fails; k=11 gives 18*C=0.0098876953125 < exp(-4), so the arithmetic passes."

canonicalCorrectedRowSumArithmetic : CorrectedRowSumArithmetic
canonicalCorrectedRowSumArithmetic =
  mkCorrectedRowSumArithmetic
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

data Sprint92ClayPromotion : Set where

sprint92ClayPromotionImpossibleHere :
  Sprint92ClayPromotion →
  ⊥
sprint92ClayPromotionImpossibleHere ()

canonicalSprint92OpenLemmas : List String
canonicalSprint92OpenLemmas =
  "BalabanQhpLocalConstantBound"
  ∷ "BalabanCMP116PolymerMassBound"
  ∷ "AdjointRepresentationSharperBound-or-BlockingDepthK11PhysicalValidation"
  ∷ "WeakCouplingWindowSU3"
  ∷ []

sprint92Boundary : String
sprint92Boundary =
  "Sprint 92 corrects the adjoint scaling: SU3 k=10 fails, SU3 k=11 passes arithmetically. It does not derive the CMP98 Qhp constant, CMP116 polymer mass, sharper adjoint or k=11 physical-validation witness, or weak-coupling-window witness; therefore WC3 and Clay remain fail-closed."

record YMSprint92MasterWC3AdjointCorrectionReceipt : Set₁ where
  field
    sprint91Receipt :
      Sprint91.YMSprint91WC3NewMathReceipt
    arithmetic :
      CorrectedRowSumArithmetic
    qhpConstantStillOpen :
      balabanQhpLocalConstantBoundDerivedInRepo ≡ false
    polymerMassStillOpen :
      balabanCMP116PolymerMassBoundDerivedInRepo ≡ false
    sharperAdjointStillOpen :
      adjointRepresentationSharperBoundDerivedInRepo ≡ false
    k11PhysicalValidationStillOpen :
      blockingDepthK11PhysicallyValidatedInRepo ≡ false
    weakCouplingWindowStillOpen :
      weakCouplingWindowSU3DerivedInRepo ≡ false
    masterSU2StillOpen :
      masterWC3ConditionSU2AtK9DerivedInRepo ≡ false
    masterSU3StillOpen :
      masterWC3ConditionSU3DerivedInRepo ≡ false
    wc3StillOpen :
      wc3UniformClusterSummabilitySU3DerivedInRepo ≡ false
    noSpectralPollutionStillOpen :
      noSpectralPollutionUnconditionalDerivedInRepo ≡ false
    qhpWitnessNotExported :
      BalabanQhpLocalConstantBoundWitness → ⊥
    polymerMassWitnessNotExported :
      BalabanCMP116PolymerMassBoundWitness → ⊥
    sharperAdjointWitnessNotExported :
      AdjointRepresentationSharperBoundWitness → ⊥
    k11PhysicalWitnessNotExported :
      BlockingDepthK11PhysicalValidationWitness → ⊥
    weakCouplingWindowWitnessNotExported :
      WeakCouplingWindowSU3Witness → ⊥
    wc3WitnessNotExported :
      WC3UniformClusterSummabilitySU3Witness → ⊥
    openLemmas :
      List String
    openLemmasAreCanonical :
      openLemmas ≡ canonicalSprint92OpenLemmas
    boundary :
      sprint92Boundary ≡
      "Sprint 92 corrects the adjoint scaling: SU3 k=10 fails, SU3 k=11 passes arithmetically. It does not derive the CMP98 Qhp constant, CMP116 polymer mass, sharper adjoint or k=11 physical-validation witness, or weak-coupling-window witness; therefore WC3 and Clay remain fail-closed."
    clayPromotions :
      List Sprint92ClayPromotion
    clayPromotionsAreEmpty :
      clayPromotions ≡ []
    noClayPromotionPossibleHere :
      Sprint92ClayPromotion → ⊥
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint92MasterWC3AdjointCorrectionReceipt :
  YMSprint92MasterWC3AdjointCorrectionReceipt
canonicalYMSprint92MasterWC3AdjointCorrectionReceipt =
  record
    { sprint91Receipt =
        Sprint91.canonicalYMSprint91WC3NewMathReceipt
    ; arithmetic =
        canonicalCorrectedRowSumArithmetic
    ; qhpConstantStillOpen =
        refl
    ; polymerMassStillOpen =
        refl
    ; sharperAdjointStillOpen =
        refl
    ; k11PhysicalValidationStillOpen =
        refl
    ; weakCouplingWindowStillOpen =
        refl
    ; masterSU2StillOpen =
        refl
    ; masterSU3StillOpen =
        refl
    ; wc3StillOpen =
        refl
    ; noSpectralPollutionStillOpen =
        refl
    ; qhpWitnessNotExported =
        balabanQhpLocalConstantBoundWitnessImpossibleHere
    ; polymerMassWitnessNotExported =
        balabanCMP116PolymerMassBoundWitnessImpossibleHere
    ; sharperAdjointWitnessNotExported =
        adjointRepresentationSharperBoundWitnessImpossibleHere
    ; k11PhysicalWitnessNotExported =
        blockingDepthK11PhysicalValidationWitnessImpossibleHere
    ; weakCouplingWindowWitnessNotExported =
        weakCouplingWindowSU3WitnessImpossibleHere
    ; wc3WitnessNotExported =
        wc3UniformClusterSummabilitySU3WitnessNotExported
    ; openLemmas =
        canonicalSprint92OpenLemmas
    ; openLemmasAreCanonical =
        refl
    ; boundary =
        refl
    ; clayPromotions =
        []
    ; clayPromotionsAreEmpty =
        refl
    ; noClayPromotionPossibleHere =
        sprint92ClayPromotionImpossibleHere
    ; noClayPromotion =
        refl
    }
