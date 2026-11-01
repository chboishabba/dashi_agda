module DASHI.Promotion.ChemistryFiniteComputationSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.ChemistryAuthorityBinding as Authority
import DASHI.Promotion.ChemistryFiniteRuleTargets as Finite

------------------------------------------------------------------------
-- Finite chemistry computation surface.
--
-- This module upgrades the chemistry lane from symbolic target rows to
-- executable finite computations.  It is intentionally bounded to the first
-- eighteen neutral atoms, exact Rydberg rational factors, and integer Gibbs
-- arithmetic examples.  Authority-loaded spectra, thermochemistry, bonding
-- interpretation, physical chemistry, and wet-lab validation remain gated by
-- ChemistryAuthorityBinding.

_&&_ : Bool → Bool → Bool
true && true = true
true && false = false
false && true = false
false && false = false

infixr 6 _&&_

leq : Nat → Nat → Bool
leq zero n = true
leq (suc m) zero = false
leq (suc m) (suc n) = leq m n

count : {A : Set} → List A → Nat
count [] = zero
count (_ ∷ xs) = suc (count xs)

data Element18 : Set where
  hydrogen : Element18
  helium : Element18
  lithium : Element18
  beryllium : Element18
  boron : Element18
  carbon : Element18
  nitrogen : Element18
  oxygen : Element18
  fluorine : Element18
  neon : Element18
  sodium : Element18
  magnesium : Element18
  aluminium : Element18
  silicon : Element18
  phosphorus : Element18
  sulfur : Element18
  chlorine : Element18
  argon : Element18

atomicNumber18 : Element18 → Nat
atomicNumber18 hydrogen = 1
atomicNumber18 helium = 2
atomicNumber18 lithium = 3
atomicNumber18 beryllium = 4
atomicNumber18 boron = 5
atomicNumber18 carbon = 6
atomicNumber18 nitrogen = 7
atomicNumber18 oxygen = 8
atomicNumber18 fluorine = 9
atomicNumber18 neon = 10
atomicNumber18 sodium = 11
atomicNumber18 magnesium = 12
atomicNumber18 aluminium = 13
atomicNumber18 silicon = 14
atomicNumber18 phosphorus = 15
atomicNumber18 sulfur = 16
atomicNumber18 chlorine = 17
atomicNumber18 argon = 18

elementSymbol18 : Element18 → String
elementSymbol18 hydrogen = "H"
elementSymbol18 helium = "He"
elementSymbol18 lithium = "Li"
elementSymbol18 beryllium = "Be"
elementSymbol18 boron = "B"
elementSymbol18 carbon = "C"
elementSymbol18 nitrogen = "N"
elementSymbol18 oxygen = "O"
elementSymbol18 fluorine = "F"
elementSymbol18 neon = "Ne"
elementSymbol18 sodium = "Na"
elementSymbol18 magnesium = "Mg"
elementSymbol18 aluminium = "Al"
elementSymbol18 silicon = "Si"
elementSymbol18 phosphorus = "P"
elementSymbol18 sulfur = "S"
elementSymbol18 chlorine = "Cl"
elementSymbol18 argon = "Ar"

record ShellOccupation18 : Set where
  constructor shell18
  field
    oneS : Nat
    twoS : Nat
    twoPX : Nat
    twoPY : Nat
    twoPZ : Nat
    threeS : Nat
    threePX : Nat
    threePY : Nat
    threePZ : Nat

open ShellOccupation18 public

occupationElectronCount18 : ShellOccupation18 → Nat
occupationElectronCount18 occ =
  oneS occ
  + twoS occ
  + twoPX occ
  + twoPY occ
  + twoPZ occ
  + threeS occ
  + threePX occ
  + threePY occ
  + threePZ occ

finiteAufbau18Occupation : Element18 → ShellOccupation18
finiteAufbau18Occupation hydrogen =
  shell18 1 0 0 0 0 0 0 0 0
finiteAufbau18Occupation helium =
  shell18 2 0 0 0 0 0 0 0 0
finiteAufbau18Occupation lithium =
  shell18 2 1 0 0 0 0 0 0 0
finiteAufbau18Occupation beryllium =
  shell18 2 2 0 0 0 0 0 0 0
finiteAufbau18Occupation boron =
  shell18 2 2 1 0 0 0 0 0 0
finiteAufbau18Occupation carbon =
  shell18 2 2 1 1 0 0 0 0 0
finiteAufbau18Occupation nitrogen =
  shell18 2 2 1 1 1 0 0 0 0
finiteAufbau18Occupation oxygen =
  shell18 2 2 2 1 1 0 0 0 0
finiteAufbau18Occupation fluorine =
  shell18 2 2 2 2 1 0 0 0 0
finiteAufbau18Occupation neon =
  shell18 2 2 2 2 2 0 0 0 0
finiteAufbau18Occupation sodium =
  shell18 2 2 2 2 2 1 0 0 0
finiteAufbau18Occupation magnesium =
  shell18 2 2 2 2 2 2 0 0 0
finiteAufbau18Occupation aluminium =
  shell18 2 2 2 2 2 2 1 0 0
finiteAufbau18Occupation silicon =
  shell18 2 2 2 2 2 2 1 1 0
finiteAufbau18Occupation phosphorus =
  shell18 2 2 2 2 2 2 1 1 1
finiteAufbau18Occupation sulfur =
  shell18 2 2 2 2 2 2 2 1 1
finiteAufbau18Occupation chlorine =
  shell18 2 2 2 2 2 2 2 2 1
finiteAufbau18Occupation argon =
  shell18 2 2 2 2 2 2 2 2 2

data FiniteChemistryComputationKind : Set where
  aufbauComputation : FiniteChemistryComputationKind
  pauliCapacityDecision : FiniteChemistryComputationKind
  hundMultiplicityDecision : FiniteChemistryComputationKind
  rydbergRationalProjection : FiniteChemistryComputationKind
  gibbsIntegerProjection : FiniteChemistryComputationKind

pHundOk : Nat → Nat → Nat → Bool
pHundOk zero zero zero = true
pHundOk 1 zero zero = true
pHundOk 1 1 zero = true
pHundOk 1 1 1 = true
pHundOk 2 1 1 = true
pHundOk 2 2 1 = true
pHundOk 2 2 2 = true
pHundOk x y z = false

pauliCapacityOk : ShellOccupation18 → Bool
pauliCapacityOk occ =
  leq (oneS occ) 2
  && leq (twoS occ) 2
  && leq (twoPX occ) 2
  && leq (twoPY occ) 2
  && leq (twoPZ occ) 2
  && leq (threeS occ) 2
  && leq (threePX occ) 2
  && leq (threePY occ) 2
  && leq (threePZ occ) 2

hundMultiplicityOk : ShellOccupation18 → Bool
hundMultiplicityOk occ =
  pHundOk (twoPX occ) (twoPY occ) (twoPZ occ)
  && pHundOk (threePX occ) (threePY occ) (threePZ occ)

finiteChemistryRowOk : Element18 → Bool
finiteChemistryRowOk e =
  pauliCapacityOk (finiteAufbau18Occupation e)
  && hundMultiplicityOk (finiteAufbau18Occupation e)

record Element18ComputationRow : Set where
  constructor elementRow
  field
    element : Element18
    symbol : String
    atomicNumber : Nat
    occupation : ShellOccupation18
    electronCount : Nat
    electronCountMatchesAtomicNumber :
      electronCount ≡ atomicNumber
    pauliDecision : Bool
    pauliDecisionIsTrue : pauliDecision ≡ true
    hundDecision : Bool
    hundDecisionIsTrue : hundDecision ≡ true
    rowAccepted : Bool
    rowAcceptedIsTrue : rowAccepted ≡ true

open Element18ComputationRow public

mkElementRow :
  (e : Element18) →
  occupationElectronCount18 (finiteAufbau18Occupation e) ≡
  atomicNumber18 e →
  pauliCapacityOk (finiteAufbau18Occupation e) ≡ true →
  hundMultiplicityOk (finiteAufbau18Occupation e) ≡ true →
  finiteChemistryRowOk e ≡ true →
  Element18ComputationRow
mkElementRow e electronProof pauliProof hundProof rowProof =
  elementRow
    e
    (elementSymbol18 e)
    (atomicNumber18 e)
    (finiteAufbau18Occupation e)
    (occupationElectronCount18 (finiteAufbau18Occupation e))
    electronProof
    (pauliCapacityOk (finiteAufbau18Occupation e))
    pauliProof
    (hundMultiplicityOk (finiteAufbau18Occupation e))
    hundProof
    (finiteChemistryRowOk e)
    rowProof

canonicalElement18ComputationRows : List Element18ComputationRow
canonicalElement18ComputationRows =
  mkElementRow hydrogen refl refl refl refl
  ∷ mkElementRow helium refl refl refl refl
  ∷ mkElementRow lithium refl refl refl refl
  ∷ mkElementRow beryllium refl refl refl refl
  ∷ mkElementRow boron refl refl refl refl
  ∷ mkElementRow carbon refl refl refl refl
  ∷ mkElementRow nitrogen refl refl refl refl
  ∷ mkElementRow oxygen refl refl refl refl
  ∷ mkElementRow fluorine refl refl refl refl
  ∷ mkElementRow neon refl refl refl refl
  ∷ mkElementRow sodium refl refl refl refl
  ∷ mkElementRow magnesium refl refl refl refl
  ∷ mkElementRow aluminium refl refl refl refl
  ∷ mkElementRow silicon refl refl refl refl
  ∷ mkElementRow phosphorus refl refl refl refl
  ∷ mkElementRow sulfur refl refl refl refl
  ∷ mkElementRow chlorine refl refl refl refl
  ∷ mkElementRow argon refl refl refl refl
  ∷ []

record RydbergProjectionRow : Set where
  constructor rydbergRow
  field
    transitionLabel : String
    lowerLevel : Nat
    upperLevel : Nat
    numerator : Nat
    denominator : Nat
    numeratorProjection :
      numerator ≡ (upperLevel * upperLevel) - (lowerLevel * lowerLevel)
    denominatorProjection :
      denominator ≡ (lowerLevel * lowerLevel) * (upperLevel * upperLevel)
    exactIntegerLevels : Bool
    exactIntegerLevelsIsTrue : exactIntegerLevels ≡ true
    measuredRydbergConstantRequired : Bool
    measuredRydbergConstantRequiredIsTrue :
      measuredRydbergConstantRequired ≡ true
    promotesSpectroscopy : Bool
    promotesSpectroscopyIsFalse : promotesSpectroscopy ≡ false

open RydbergProjectionRow public

mkRydbergRow :
  String →
  (lower upper : Nat) →
  RydbergProjectionRow
mkRydbergRow label lower upper =
  rydbergRow
    label
    lower
    upper
    ((upper * upper) - (lower * lower))
    ((lower * lower) * (upper * upper))
    refl
    refl
    true
    refl
    true
    refl
    false
    refl

canonicalRydbergProjectionRows : List RydbergProjectionRow
canonicalRydbergProjectionRows =
  mkRydbergRow "Lyman-alpha n=2 to n=1 factor" 1 2
  ∷ mkRydbergRow "Lyman-beta n=3 to n=1 factor" 1 3
  ∷ mkRydbergRow "Balmer-alpha n=3 to n=2 factor" 2 3
  ∷ mkRydbergRow "Balmer-beta n=4 to n=2 factor" 2 4
  ∷ mkRydbergRow "Paschen-alpha n=4 to n=3 factor" 3 4
  ∷ mkRydbergRow "Brackett-alpha n=5 to n=4 factor" 4 5
  ∷ []

data SignedNat : Set where
  nonnegative : Nat → SignedNat
  negative : Nat → SignedNat

minusSigned : Nat → Nat → SignedNat
minusSigned zero zero = nonnegative 0
minusSigned zero (suc n) = negative (suc n)
minusSigned (suc m) zero = nonnegative (suc m)
minusSigned (suc m) (suc n) = minusSigned m n

gibbsDeltaG : Nat → Nat → Nat → SignedNat
gibbsDeltaG deltaH temperature deltaS =
  minusSigned deltaH (temperature * deltaS)

record GibbsProjectionRow : Set where
  constructor gibbsRow
  field
    gibbsLabel : String
    deltaH : Nat
    temperature : Nat
    deltaS : Nat
    tDeltaS : Nat
    tDeltaSProjection : tDeltaS ≡ temperature * deltaS
    deltaG : SignedNat
    deltaGProjection : deltaG ≡ gibbsDeltaG deltaH temperature deltaS
    integerArithmeticAccepted : Bool
    integerArithmeticAcceptedIsTrue :
      integerArithmeticAccepted ≡ true
    thermochemistryAuthorityRequired : Bool
    thermochemistryAuthorityRequiredIsTrue :
      thermochemistryAuthorityRequired ≡ true
    promotesPhysicalChemistry : Bool
    promotesPhysicalChemistryIsFalse :
      promotesPhysicalChemistry ≡ false

open GibbsProjectionRow public

mkGibbsRow :
  String →
  (deltaH temperature deltaS : Nat) →
  GibbsProjectionRow
mkGibbsRow label deltaH temperature deltaS =
  gibbsRow
    label
    deltaH
    temperature
    deltaS
    (temperature * deltaS)
    refl
    (gibbsDeltaG deltaH temperature deltaS)
    refl
    true
    refl
    true
    refl
    false
    refl

canonicalGibbsProjectionRows : List GibbsProjectionRow
canonicalGibbsProjectionRows =
  mkGibbsRow "positive delta-G integer fixture" 10 2 3
  ∷ mkGibbsRow "negative delta-G integer fixture" 12 3 5
  ∷ mkGibbsRow "zero delta-G integer fixture" 40 4 10
  ∷ mkGibbsRow "enthalpy-dominated integer fixture" 100 4 11
  ∷ mkGibbsRow "entropy-dominated integer fixture" 30 5 9
  ∷ []

record ChemistryFiniteComputationSurface : Set₁ where
  field
    finiteRuleTargets :
      Finite.ChemistryFiniteRuleTargets
    authorityBinding :
      Authority.ChemistryAuthorityBinding
    elementRows :
      List Element18ComputationRow
    elementRowCount :
      Nat
    elementRowCountMatches :
      elementRowCount ≡ count elementRows
    rydbergRows :
      List RydbergProjectionRow
    rydbergRowCount :
      Nat
    rydbergRowCountMatches :
      rydbergRowCount ≡ count rydbergRows
    gibbsRows :
      List GibbsProjectionRow
    gibbsRowCount :
      Nat
    gibbsRowCountMatches :
      gibbsRowCount ≡ count gibbsRows
    computationKindCount :
      Nat
    firstTenCompatibility :
      occupationElectronCount18 (finiteAufbau18Occupation neon) ≡
      Finite.atomicNumber Finite.neon
    firstEighteenClosure :
      occupationElectronCount18 (finiteAufbau18Occupation argon) ≡
      atomicNumber18 argon
    balmerAlphaNumerator :
      numerator (mkRydbergRow "Balmer-alpha n=3 to n=2 factor" 2 3) ≡ 5
    balmerAlphaDenominator :
      denominator (mkRydbergRow "Balmer-alpha n=3 to n=2 factor" 2 3) ≡ 36
    lymanAlphaNumerator :
      numerator (mkRydbergRow "Lyman-alpha n=2 to n=1 factor" 1 2) ≡ 3
    lymanAlphaDenominator :
      denominator (mkRydbergRow "Lyman-alpha n=2 to n=1 factor" 1 2) ≡ 4
    positiveGibbsFixture :
      gibbsDeltaG 10 2 3 ≡ nonnegative 4
    negativeGibbsFixture :
      gibbsDeltaG 12 3 5 ≡ negative 3
    zeroGibbsFixture :
      gibbsDeltaG 40 4 10 ≡ nonnegative 0
    finiteComputationAccepted :
      Bool
    finiteComputationAcceptedIsTrue :
      finiteComputationAccepted ≡ true
    measuredNumericAuthorityAccepted :
      Bool
    measuredNumericAuthorityAcceptedIsFalse :
      measuredNumericAuthorityAccepted ≡ false
    spectroscopyAuthorityAccepted :
      Bool
    spectroscopyAuthorityAcceptedIsFalse :
      spectroscopyAuthorityAccepted ≡ false
    thermochemistryAuthorityAccepted :
      Bool
    thermochemistryAuthorityAcceptedIsFalse :
      thermochemistryAuthorityAccepted ≡ false
    bondingInterpretationPromoted :
      Bool
    bondingInterpretationPromotedIsFalse :
      bondingInterpretationPromoted ≡ false
    physicalChemistryPromoted :
      Bool
    physicalChemistryPromotedIsFalse :
      physicalChemistryPromoted ≡ false
    wetLabValidationAccepted :
      Bool
    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false
    validationCommand :
      String

open ChemistryFiniteComputationSurface public

canonicalChemistryFiniteComputationSurface :
  ChemistryFiniteComputationSurface
canonicalChemistryFiniteComputationSurface = record
  { finiteRuleTargets =
      Finite.canonicalChemistryFiniteRuleTargets
  ; authorityBinding =
      Authority.canonicalChemistryAuthorityBinding
  ; elementRows =
      canonicalElement18ComputationRows
  ; elementRowCount =
      18
  ; elementRowCountMatches =
      refl
  ; rydbergRows =
      canonicalRydbergProjectionRows
  ; rydbergRowCount =
      6
  ; rydbergRowCountMatches =
      refl
  ; gibbsRows =
      canonicalGibbsProjectionRows
  ; gibbsRowCount =
      5
  ; gibbsRowCountMatches =
      refl
  ; computationKindCount =
      5
  ; firstTenCompatibility =
      refl
  ; firstEighteenClosure =
      refl
  ; balmerAlphaNumerator =
      refl
  ; balmerAlphaDenominator =
      refl
  ; lymanAlphaNumerator =
      refl
  ; lymanAlphaDenominator =
      refl
  ; positiveGibbsFixture =
      refl
  ; negativeGibbsFixture =
      refl
  ; zeroGibbsFixture =
      refl
  ; finiteComputationAccepted =
      true
  ; finiteComputationAcceptedIsTrue =
      refl
  ; measuredNumericAuthorityAccepted =
      false
  ; measuredNumericAuthorityAcceptedIsFalse =
      refl
  ; spectroscopyAuthorityAccepted =
      false
  ; spectroscopyAuthorityAcceptedIsFalse =
      refl
  ; thermochemistryAuthorityAccepted =
      false
  ; thermochemistryAuthorityAcceptedIsFalse =
      refl
  ; bondingInterpretationPromoted =
      false
  ; bondingInterpretationPromotedIsFalse =
      refl
  ; physicalChemistryPromoted =
      false
  ; physicalChemistryPromotedIsFalse =
      refl
  ; wetLabValidationAccepted =
      false
  ; wetLabValidationAcceptedIsFalse =
      refl
  ; validationCommand =
      "agda -i . DASHI/Promotion/ChemistryFiniteComputationSurface.agda"
  }

canonicalFiniteComputationElementRowCountIs18 :
  elementRowCount canonicalChemistryFiniteComputationSurface ≡ 18
canonicalFiniteComputationElementRowCountIs18 = refl

canonicalFiniteComputationRydbergRowCountIs6 :
  rydbergRowCount canonicalChemistryFiniteComputationSurface ≡ 6
canonicalFiniteComputationRydbergRowCountIs6 = refl

canonicalFiniteComputationGibbsRowCountIs5 :
  gibbsRowCount canonicalChemistryFiniteComputationSurface ≡ 5
canonicalFiniteComputationGibbsRowCountIs5 = refl

canonicalFiniteComputationKindCountIs5 :
  computationKindCount canonicalChemistryFiniteComputationSurface ≡ 5
canonicalFiniteComputationKindCountIs5 = refl

canonicalArgonElectronCountIs18 :
  occupationElectronCount18 (finiteAufbau18Occupation argon) ≡ 18
canonicalArgonElectronCountIs18 = refl

canonicalArgonPauliDecisionIsTrue :
  pauliCapacityOk (finiteAufbau18Occupation argon) ≡ true
canonicalArgonPauliDecisionIsTrue = refl

canonicalArgonHundDecisionIsTrue :
  hundMultiplicityOk (finiteAufbau18Occupation argon) ≡ true
canonicalArgonHundDecisionIsTrue = refl

canonicalBalmerAlphaRydbergFactorIs5Over36 :
  numerator (mkRydbergRow "Balmer-alpha n=3 to n=2 factor" 2 3) ≡ 5
canonicalBalmerAlphaRydbergFactorIs5Over36 = refl

canonicalBalmerAlphaRydbergDenominatorIs36 :
  denominator (mkRydbergRow "Balmer-alpha n=3 to n=2 factor" 2 3) ≡ 36
canonicalBalmerAlphaRydbergDenominatorIs36 = refl

canonicalPositiveGibbsFixtureIs4 :
  gibbsDeltaG 10 2 3 ≡ nonnegative 4
canonicalPositiveGibbsFixtureIs4 = refl

canonicalNegativeGibbsFixtureIsNegative3 :
  gibbsDeltaG 12 3 5 ≡ negative 3
canonicalNegativeGibbsFixtureIsNegative3 = refl

canonicalZeroGibbsFixtureIs0 :
  gibbsDeltaG 40 4 10 ≡ nonnegative 0
canonicalZeroGibbsFixtureIs0 = refl

canonicalFiniteComputationAcceptedIsTrue :
  finiteComputationAccepted
    canonicalChemistryFiniteComputationSurface ≡ true
canonicalFiniteComputationAcceptedIsTrue = refl

canonicalFiniteComputationMeasuredAuthorityIsFalse :
  measuredNumericAuthorityAccepted
    canonicalChemistryFiniteComputationSurface ≡ false
canonicalFiniteComputationMeasuredAuthorityIsFalse = refl

canonicalFiniteComputationSpectroscopyAuthorityIsFalse :
  spectroscopyAuthorityAccepted
    canonicalChemistryFiniteComputationSurface ≡ false
canonicalFiniteComputationSpectroscopyAuthorityIsFalse = refl

canonicalFiniteComputationThermochemistryAuthorityIsFalse :
  thermochemistryAuthorityAccepted
    canonicalChemistryFiniteComputationSurface ≡ false
canonicalFiniteComputationThermochemistryAuthorityIsFalse = refl

canonicalFiniteComputationBondingPromotionIsFalse :
  bondingInterpretationPromoted
    canonicalChemistryFiniteComputationSurface ≡ false
canonicalFiniteComputationBondingPromotionIsFalse = refl

canonicalFiniteComputationPhysicalChemistryPromotionIsFalse :
  physicalChemistryPromoted
    canonicalChemistryFiniteComputationSurface ≡ false
canonicalFiniteComputationPhysicalChemistryPromotionIsFalse = refl

canonicalFiniteComputationWetLabValidationIsFalse :
  wetLabValidationAccepted
    canonicalChemistryFiniteComputationSurface ≡ false
canonicalFiniteComputationWetLabValidationIsFalse = refl
