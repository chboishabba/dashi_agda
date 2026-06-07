module DASHI.Physics.Closure.NSMonodromyIntegralBoundFinite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

------------------------------------------------------------------------
-- Finite monodromy integral-bound toy surface.
--
-- This module proves only a finite arithmetic fact: the four quarter-turn
-- samples around a loop with encoded sin^2 defect values [0, 1, 0, 1]
-- have average 2/4, rationally equal to the explicit positive lower
-- bound 1/2.  The pi/8-style continuum topological-stretching target is
-- recorded as target-only and is not promoted to a continuum PDE lemma or
-- Clay Navier-Stokes result.

nsMonodromyIntegralBoundFiniteLedgerClosed : Bool
nsMonodromyIntegralBoundFiniteLedgerClosed = true

data QuarterTurnSample : Set where
  theta0 :
    QuarterTurnSample
  thetaPiOver2 :
    QuarterTurnSample
  thetaPi :
    QuarterTurnSample
  theta3PiOver2 :
    QuarterTurnSample

canonicalQuarterTurnSamples :
  List QuarterTurnSample
canonicalQuarterTurnSamples =
  theta0
  ∷ thetaPiOver2
  ∷ thetaPi
  ∷ theta3PiOver2
  ∷ []

quarterTurnSampleCount : Nat
quarterTurnSampleCount = 4

quarterTurnSampleCountIsFour :
  quarterTurnSampleCount ≡ 4
quarterTurnSampleCountIsFour = refl

sinSquaredDefectNumerator :
  QuarterTurnSample → Nat
sinSquaredDefectNumerator theta0 = 0
sinSquaredDefectNumerator thetaPiOver2 = 1
sinSquaredDefectNumerator thetaPi = 0
sinSquaredDefectNumerator theta3PiOver2 = 1

encodedSinSquaredDefectValues :
  List Nat
encodedSinSquaredDefectValues =
  0 ∷ 1 ∷ 0 ∷ 1 ∷ []

sumNat :
  List Nat → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

finiteSinSquaredDefectSum : Nat
finiteSinSquaredDefectSum =
  sumNat encodedSinSquaredDefectValues

finiteSinSquaredDefectSumIsTwo :
  finiteSinSquaredDefectSum ≡ 2
finiteSinSquaredDefectSumIsTwo = refl

finiteAverageDenominator : Nat
finiteAverageDenominator = 4

finiteAverageDenominatorIsFour :
  finiteAverageDenominator ≡ 4
finiteAverageDenominatorIsFour = refl

record EncodedRational : Set where
  constructor encodedRational
  field
    numerator :
      Nat
    denominator :
      Nat

open EncodedRational public

finiteAverageSinSquared :
  EncodedRational
finiteAverageSinSquared =
  encodedRational finiteSinSquaredDefectSum finiteAverageDenominator

finiteAverageSinSquaredIsTwoOverFour :
  finiteAverageSinSquared ≡ encodedRational 2 4
finiteAverageSinSquaredIsTwoOverFour = refl

explicitPositiveLowerBoundHalf :
  EncodedRational
explicitPositiveLowerBoundHalf =
  encodedRational 1 2

explicitPositiveLowerBoundHalfIsOneOverTwo :
  explicitPositiveLowerBoundHalf ≡ encodedRational 1 2
explicitPositiveLowerBoundHalfIsOneOverTwo = refl

rationalCrossProductEquality :
  EncodedRational → EncodedRational → Set
rationalCrossProductEquality left right =
  numerator left * denominator right ≡
  numerator right * denominator left

finiteAverageEqualsExplicitHalf :
  rationalCrossProductEquality
    finiteAverageSinSquared
    explicitPositiveLowerBoundHalf
finiteAverageEqualsExplicitHalf = refl

rationalLowerBoundByCrossProduct :
  EncodedRational → EncodedRational → Set
rationalLowerBoundByCrossProduct lower average =
  numerator lower * denominator average ≤
  numerator average * denominator lower

finiteAverageAtLeastExplicitHalf :
  rationalLowerBoundByCrossProduct
    explicitPositiveLowerBoundHalf
    finiteAverageSinSquared
finiteAverageAtLeastExplicitHalf =
  s≤s (s≤s (s≤s (s≤s z≤n)))

quarterTurnDefectVectorRecorded : Bool
quarterTurnDefectVectorRecorded = true

finiteAverageLowerBoundEqualsOneHalf : Bool
finiteAverageLowerBoundEqualsOneHalf = true

piOver8StyleContinuumTargetOnly : Bool
piOver8StyleContinuumTargetOnly = true

topologicalStretchingLeakageFiniteSupport : Bool
topologicalStretchingLeakageFiniteSupport = true

continuumTopologicalStretchingLeakageLemma : Bool
continuumTopologicalStretchingLeakageLemma = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

recordsQuarterTurnDefectVector :
  quarterTurnDefectVectorRecorded ≡ true
recordsQuarterTurnDefectVector = refl

recordsFiniteAverageLowerBoundOneHalf :
  finiteAverageLowerBoundEqualsOneHalf ≡ true
recordsFiniteAverageLowerBoundOneHalf = refl

recordsPiOver8StyleContinuumTargetOnly :
  piOver8StyleContinuumTargetOnly ≡ true
recordsPiOver8StyleContinuumTargetOnly = refl

recordsFiniteTopologicalStretchingLeakageSupport :
  topologicalStretchingLeakageFiniteSupport ≡ true
recordsFiniteTopologicalStretchingLeakageSupport = refl

keepsContinuumTopologicalStretchingLeakageLemmaFalse :
  continuumTopologicalStretchingLeakageLemma ≡ false
keepsContinuumTopologicalStretchingLeakageLemmaFalse = refl

keepsClayNavierStokesPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotionFalse = refl

data NSMonodromyFiniteSampleRow : Set where
  sampleTheta0SinSquaredZero :
    NSMonodromyFiniteSampleRow
  sampleThetaPiOver2SinSquaredOne :
    NSMonodromyFiniteSampleRow
  sampleThetaPiSinSquaredZero :
    NSMonodromyFiniteSampleRow
  sampleTheta3PiOver2SinSquaredOne :
    NSMonodromyFiniteSampleRow

canonicalNSMonodromyFiniteSampleRows :
  List NSMonodromyFiniteSampleRow
canonicalNSMonodromyFiniteSampleRows =
  sampleTheta0SinSquaredZero
  ∷ sampleThetaPiOver2SinSquaredOne
  ∷ sampleThetaPiSinSquaredZero
  ∷ sampleTheta3PiOver2SinSquaredOne
  ∷ []

nsMonodromyFiniteSampleRowCount : Nat
nsMonodromyFiniteSampleRowCount = 4

nsMonodromyFiniteSampleRowCountIsFour :
  nsMonodromyFiniteSampleRowCount ≡ 4
nsMonodromyFiniteSampleRowCountIsFour = refl

data NSMonodromyFiniteBoundRow : Set where
  defectVectorZeroOneZeroOne :
    NSMonodromyFiniteBoundRow
  sumOfDefectsIsTwo :
    NSMonodromyFiniteBoundRow
  averageDenominatorIsFour :
    NSMonodromyFiniteBoundRow
  averageRationalIsTwoOverFour :
    NSMonodromyFiniteBoundRow
  averageLowerBoundIsOneHalf :
    NSMonodromyFiniteBoundRow
  crossProductLowerBoundFourLessOrEqualFour :
    NSMonodromyFiniteBoundRow

canonicalNSMonodromyFiniteBoundRows :
  List NSMonodromyFiniteBoundRow
canonicalNSMonodromyFiniteBoundRows =
  defectVectorZeroOneZeroOne
  ∷ sumOfDefectsIsTwo
  ∷ averageDenominatorIsFour
  ∷ averageRationalIsTwoOverFour
  ∷ averageLowerBoundIsOneHalf
  ∷ crossProductLowerBoundFourLessOrEqualFour
  ∷ []

nsMonodromyFiniteBoundRowCount : Nat
nsMonodromyFiniteBoundRowCount = 6

nsMonodromyFiniteBoundRowCountIsSix :
  nsMonodromyFiniteBoundRowCount ≡ 6
nsMonodromyFiniteBoundRowCountIsSix = refl

data NSMonodromyContinuumConnectionRow : Set where
  piOver8StyleContinuumTargetOnlyRow :
    NSMonodromyContinuumConnectionRow
  finiteSupportTopologicalStretchingLeakageRow :
    NSMonodromyContinuumConnectionRow
  continuumTopologicalStretchingLeakageLemmaFalseRow :
    NSMonodromyContinuumConnectionRow
  clayNavierStokesPromotedFalseRow :
    NSMonodromyContinuumConnectionRow

canonicalNSMonodromyContinuumConnectionRows :
  List NSMonodromyContinuumConnectionRow
canonicalNSMonodromyContinuumConnectionRows =
  piOver8StyleContinuumTargetOnlyRow
  ∷ finiteSupportTopologicalStretchingLeakageRow
  ∷ continuumTopologicalStretchingLeakageLemmaFalseRow
  ∷ clayNavierStokesPromotedFalseRow
  ∷ []

nsMonodromyContinuumConnectionRowCount : Nat
nsMonodromyContinuumConnectionRowCount = 4

nsMonodromyContinuumConnectionRowCountIsFour :
  nsMonodromyContinuumConnectionRowCount ≡ 4
nsMonodromyContinuumConnectionRowCountIsFour = refl

organizationString : String
organizationString =
  "O: NSMonodromyIntegralBoundFinite isolates a four-sample arithmetic surface for the monodromy integral-bound toy."

requirementString : String
requirementString =
  "R: Encode quarter-turn sin^2 defect values [0,1,0,1], prove sum=2, denominator=4, average=2/4, and the explicit lower bound 1/2."

codeArtifactString : String
codeArtifactString =
  "C: The Agda artifact exports finite samples, encoded rationals, cross-product equality, Nat lower-bound evidence, fail-closed continuum flags, rows, counts, and a canonical receipt."

stateString : String
stateString =
  "S: Finite arithmetic support is true; the pi/8-style continuum target is target-only, not a continuum topological-stretching leakage lemma."

latticeString : String
latticeString =
  "L: quarter-turn loop samples -> [0,1,0,1] defect vector -> sum 2 over denominator 4 -> 1/2 finite bound -> continuum target remains unproved."

proposalString : String
proposalString =
  "P: Use this finite support as a checked toy lower-bound surface while keeping the continuum PDE route separately gated."

governanceString : String
governanceString =
  "G: topologicalStretchingLeakageFiniteSupport=true, continuumTopologicalStretchingLeakageLemma=false, and clayNavierStokesPromoted=false."

gapString : String
gapString =
  "F: Open gaps are passage from finite quarter-turn support to pi/8-style continuum stretching leakage, PDE integration, and any Clay Navier-Stokes promotion."

record NSMonodromyFiniteORCSLPGF : Set where
  constructor nsMonodromyFiniteORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡ organizationString
    R :
      String
    RIsCanonical :
      R ≡ requirementString
    C :
      String
    CIsCanonical :
      C ≡ codeArtifactString
    S :
      String
    SIsCanonical :
      S ≡ stateString
    L :
      String
    LIsCanonical :
      L ≡ latticeString
    P :
      String
    PIsCanonical :
      P ≡ proposalString
    G :
      String
    GIsCanonical :
      G ≡ governanceString
    F :
      String
    FIsCanonical :
      F ≡ gapString

open NSMonodromyFiniteORCSLPGF public

canonicalNSMonodromyFiniteORCSLPGF :
  NSMonodromyFiniteORCSLPGF
canonicalNSMonodromyFiniteORCSLPGF =
  nsMonodromyFiniteORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

record NSMonodromyIntegralBoundFiniteReceipt : Set where
  constructor nsMonodromyIntegralBoundFiniteReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "NSMonodromyIntegralBoundFinite"
    orcslpgf :
      NSMonodromyFiniteORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSMonodromyFiniteORCSLPGF
    samples :
      List QuarterTurnSample
    samplesAreCanonical :
      samples ≡ canonicalQuarterTurnSamples
    sampleRows :
      List NSMonodromyFiniteSampleRow
    sampleRowsAreCanonical :
      sampleRows ≡ canonicalNSMonodromyFiniteSampleRows
    boundRows :
      List NSMonodromyFiniteBoundRow
    boundRowsAreCanonical :
      boundRows ≡ canonicalNSMonodromyFiniteBoundRows
    continuumConnectionRows :
      List NSMonodromyContinuumConnectionRow
    continuumConnectionRowsAreCanonical :
      continuumConnectionRows ≡ canonicalNSMonodromyContinuumConnectionRows
    defectVector :
      List Nat
    defectVectorIsCanonical :
      defectVector ≡ encodedSinSquaredDefectValues
    average :
      EncodedRational
    averageIsCanonical :
      average ≡ finiteAverageSinSquared
    lowerBound :
      EncodedRational
    lowerBoundIsCanonical :
      lowerBound ≡ explicitPositiveLowerBoundHalf
    finiteAverageEqualsHalfField :
      rationalCrossProductEquality average lowerBound
    finiteAverageAtLeastHalfField :
      rationalLowerBoundByCrossProduct lowerBound average
    topologicalStretchingLeakageFiniteSupportField :
      topologicalStretchingLeakageFiniteSupport ≡ true
    continuumTopologicalStretchingLeakageLemmaFalseField :
      continuumTopologicalStretchingLeakageLemma ≡ false
    clayNavierStokesPromotedFalseField :
      clayNavierStokesPromoted ≡ false
    sampleRowCountField :
      nsMonodromyFiniteSampleRowCount ≡ 4
    boundRowCountField :
      nsMonodromyFiniteBoundRowCount ≡ 6
    continuumConnectionRowCountField :
      nsMonodromyContinuumConnectionRowCount ≡ 4

canonicalNSMonodromyIntegralBoundFiniteReceipt :
  NSMonodromyIntegralBoundFiniteReceipt
canonicalNSMonodromyIntegralBoundFiniteReceipt =
  nsMonodromyIntegralBoundFiniteReceipt
    "NSMonodromyIntegralBoundFinite"
    refl
    canonicalNSMonodromyFiniteORCSLPGF
    refl
    canonicalQuarterTurnSamples
    refl
    canonicalNSMonodromyFiniteSampleRows
    refl
    canonicalNSMonodromyFiniteBoundRows
    refl
    canonicalNSMonodromyContinuumConnectionRows
    refl
    encodedSinSquaredDefectValues
    refl
    finiteAverageSinSquared
    refl
    explicitPositiveLowerBoundHalf
    refl
    finiteAverageEqualsExplicitHalf
    finiteAverageAtLeastExplicitHalf
    refl
    refl
    refl
    refl
    refl
    refl
