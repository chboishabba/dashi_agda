module DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Terence Tao.
-- Title: "Lecture Notes 6 for 247B: Paradifferential calculus,
-- fractional chain and Leibnitz rules".
-- Venue/year: UCLA Math 247B Fourier Analysis lecture notes, Winter 2007;
-- course page updated with relevant errata through 16 April 2026.
-- DOI: none; these are course lecture notes rather than a journal article.
-- Uses: the two transpose operators for bilinear multipliers, the
-- high-high/high-low/low-high trichotomy, and Lemma 2.7 (Bony's
-- paraproduct decomposition).
-- Relationship: supplies the permutation-combinatorics template for the
-- output condition and two partial adjoints.  The course-page erratum to
-- Lemma 3.3 and the 2026 footnote-5 sign correction are recorded and are
-- not used as proof inputs here.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularités pour les
-- équations aux dérivées partielles non linéaires".
-- Venue/year: Annales scientifiques de l'École Normale Supérieure,
-- Série 4, 14 (1981), no. 2, 209--246.
-- DOI: 10.24033/asens.1404.
-- Uses: the paradifferential decomposition underlying the trichotomy.
-- Relationship: original peer-reviewed provenance for Bony's
-- paraproduct calculus; no Navier--Stokes orbit-shell estimate is imported.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data TriadLeg : Set where
  leftLeg rightLeg outputLeg : TriadLeg

data FrozenLeg : Set where
  freezeOutput freezeLeft freezeRight : FrozenLeg

data RelativeRole : Set where
  inputA inputB frozen : RelativeRole

roleUnderFreeze : FrozenLeg → TriadLeg → RelativeRole
roleUnderFreeze freezeOutput leftLeg = inputA
roleUnderFreeze freezeOutput rightLeg = inputB
roleUnderFreeze freezeOutput outputLeg = frozen
roleUnderFreeze freezeLeft leftLeg = frozen
roleUnderFreeze freezeLeft rightLeg = inputA
roleUnderFreeze freezeLeft outputLeg = inputB
roleUnderFreeze freezeRight leftLeg = inputB
roleUnderFreeze freezeRight rightLeg = frozen
roleUnderFreeze freezeRight outputLeg = inputA

data AbsoluteTrichotomy : Set where
  leftLow : AbsoluteTrichotomy
  rightLow : AbsoluteTrichotomy
  outputLow : AbsoluteTrichotomy
  comparable : AbsoluteTrichotomy
  transition : AbsoluteTrichotomy
  residual : AbsoluteTrichotomy

data RelativeParaproductClass : Set where
  lowHigh : RelativeParaproductClass
  highLow : RelativeParaproductClass
  highHighToLow : RelativeParaproductClass
  nearClass : RelativeParaproductClass
  transitionClass : RelativeParaproductClass
  residualClass : RelativeParaproductClass

classUnderFreeze : FrozenLeg → AbsoluteTrichotomy → RelativeParaproductClass
classUnderFreeze freezeOutput leftLow = lowHigh
classUnderFreeze freezeOutput rightLow = highLow
classUnderFreeze freezeOutput outputLow = highHighToLow
classUnderFreeze freezeOutput comparable = nearClass
classUnderFreeze freezeOutput transition = transitionClass
classUnderFreeze freezeOutput residual = residualClass

classUnderFreeze freezeLeft leftLow = highHighToLow
classUnderFreeze freezeLeft rightLow = lowHigh
classUnderFreeze freezeLeft outputLow = highLow
classUnderFreeze freezeLeft comparable = nearClass
classUnderFreeze freezeLeft transition = transitionClass
classUnderFreeze freezeLeft residual = residualClass

classUnderFreeze freezeRight leftLow = highLow
classUnderFreeze freezeRight rightLow = highHighToLow
classUnderFreeze freezeRight outputLow = lowHigh
classUnderFreeze freezeRight comparable = nearClass
classUnderFreeze freezeRight transition = transitionClass
classUnderFreeze freezeRight residual = residualClass

record FrozenLegPermutationReceipt : Set where
  constructor receipt
  field
    outputFreezesOutput :
      roleUnderFreeze freezeOutput outputLeg ≡ frozen
    leftFreezesLeft :
      roleUnderFreeze freezeLeft leftLeg ≡ frozen
    rightFreezesRight :
      roleUnderFreeze freezeRight rightLeg ≡ frozen

    outputLeftLowIsLowHigh :
      classUnderFreeze freezeOutput leftLow ≡ lowHigh
    outputRightLowIsHighLow :
      classUnderFreeze freezeOutput rightLow ≡ highLow
    outputLowIsHighHighToLow :
      classUnderFreeze freezeOutput outputLow ≡ highHighToLow

    leftFrozenClassRotation :
      classUnderFreeze freezeLeft leftLow ≡ highHighToLow
    leftFrozenRightLowIsLowHigh :
      classUnderFreeze freezeLeft rightLow ≡ lowHigh
    leftFrozenOutputLowIsHighLow :
      classUnderFreeze freezeLeft outputLow ≡ highLow

    rightFrozenLeftLowIsHighLow :
      classUnderFreeze freezeRight leftLow ≡ highLow
    rightFrozenClassRotation :
      classUnderFreeze freezeRight rightLow ≡ highHighToLow
    rightFrozenOutputLowIsLowHigh :
      classUnderFreeze freezeRight outputLow ≡ lowHigh

open FrozenLegPermutationReceipt public

frozenLegPermutationReceipt : FrozenLegPermutationReceipt
frozenLegPermutationReceipt =
  receipt refl refl refl refl refl refl refl refl refl refl refl refl

record FrozenLegParametrizedTrichotomy
    {i s : Level} : Set (lsuc (i ⊔ s)) where
  field
    ShellIndex : Set i
    Scalar : Set s

    shellComparable : ShellIndex → ShellIndex → Set
    shellStrictlyBelow : ShellIndex → ShellIndex → Set
    shellSeparatedBy : ShellIndex → ShellIndex → Scalar → Set

    triadIncidence :
      ShellIndex → ShellIndex → ShellIndex → Set
    triadIncidencePermutationInvariant : Set s

    absoluteClass :
      ShellIndex → ShellIndex → ShellIndex → AbsoluteTrichotomy
    relativeClass :
      FrozenLeg →
      ShellIndex → ShellIndex → ShellIndex →
      RelativeParaproductClass

    classTransportAgreesWithPermutation : Set s
    exactClassDecompositionForEveryFrozenLeg : Set s

    outputMultiplierIdentified : Set s
    firstTransposeMultiplierIdentified : Set s
    secondTransposeMultiplierIdentified : Set s
    transposeSymbolIdentitiesClosed : Set s

    derivativeOwnerTransported : Set s
    holderExponentTargetTransported : Set s
    orbitNormalizationTransported : Set s
    lerayPlacementTransported : Set s

    nearMajorantParametrized : Set s
    separatedOneLowMajorantParametrized : Set s
    transitionMajorantParametrized : Set s
    residualMajorantParametrized : Set s

    outputExponentLedgerClosed : Set s
    firstAdjointExponentLedgerClosed : Set s
    secondAdjointExponentLedgerClosed : Set s
    allThreeLedgersCutoffUniform : Set s

open FrozenLegParametrizedTrichotomy public

taoTransposeAndTrichotomySourceRepresented : Bool
taoTransposeAndTrichotomySourceRepresented = true

taoTransposeAndTrichotomySourceRepresentedIsTrue :
  taoTransposeAndTrichotomySourceRepresented ≡ true
taoTransposeAndTrichotomySourceRepresentedIsTrue = refl

taoLemma33ErratumRecorded : Bool
taoLemma33ErratumRecorded = true

taoLemma33ErratumRecordedIsTrue :
  taoLemma33ErratumRecorded ≡ true
taoLemma33ErratumRecordedIsTrue = refl

taoFootnote5SignErratumRecorded : Bool
taoFootnote5SignErratumRecorded = true

taoFootnote5SignErratumRecordedIsTrue :
  taoFootnote5SignErratumRecorded ≡ true
taoFootnote5SignErratumRecordedIsTrue = refl

permutationCombinatoricsIdentical : Bool
permutationCombinatoricsIdentical = true

permutationCombinatoricsIdenticalIsTrue :
  permutationCombinatoricsIdentical ≡ true
permutationCombinatoricsIdenticalIsTrue = refl

permutationAloneClosesAllExponentLedgers : Bool
permutationAloneClosesAllExponentLedgers = false

permutationAloneClosesAllExponentLedgersIsFalse :
  permutationAloneClosesAllExponentLedgers ≡ false
permutationAloneClosesAllExponentLedgersIsFalse = refl
