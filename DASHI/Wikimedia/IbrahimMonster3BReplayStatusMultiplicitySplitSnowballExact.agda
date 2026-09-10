module DASHI.Wikimedia.IbrahimMonster3BReplayStatusMultiplicitySplitSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchExact as Search
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Moonshine.Monster3BLiteralThreePhaseRegularResidualBidiExact as Literal
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine

------------------------------------------------------------------------
-- REPLAY STATUS / 12+78 MULTIPLICITY SPLIT / OEIS SNOWBALL
--
-- The branch owns the GAP/CTblLib restriction algorithm and the generated-
-- certificate renderer, but the generated certificate is not committed at the
-- audited head and no fresh current-head CI receipt is imported here.
--
-- Independently, the executable restriction lane exposes the exact paired-
-- phase multiplicity split
--
--   12 + 78 = 90,
--   2 * 729 = 1458,
--   1458 * 12 = 17496,
--   1458 * 78 = 113724,
--   17496 + 113724 = 131220 = 2 * 65610.
--
-- The total 90 is the SAME integer as A005052(2)=10*3^2, but OEIS does not
-- supply the CTblLib constituent decomposition or any action/intertwiner.
------------------------------------------------------------------------

firstMultiplicityDegree : Nat
firstMultiplicityDegree = 12

secondMultiplicityDegree : Nat
secondMultiplicityDegree = 78

multiplicityTotal : Nat
multiplicityTotal = firstMultiplicityDegree + secondMultiplicityDegree

multiplicitySplitIsNinety : multiplicityTotal ≡ 90
multiplicitySplitIsNinety = refl

pairedHeisenbergDegree : Nat
pairedHeisenbergDegree = 2 * 729

pairedHeisenbergDegreeIs1458 : pairedHeisenbergDegree ≡ 1458
pairedHeisenbergDegreeIs1458 = refl

firstPairedConstituentDegree : Nat
firstPairedConstituentDegree = pairedHeisenbergDegree * firstMultiplicityDegree

secondPairedConstituentDegree : Nat
secondPairedConstituentDegree = pairedHeisenbergDegree * secondMultiplicityDegree

firstPairedConstituentDegreeIs17496 : firstPairedConstituentDegree ≡ 17496
firstPairedConstituentDegreeIs17496 = refl

secondPairedConstituentDegreeIs113724 : secondPairedConstituentDegree ≡ 113724
secondPairedConstituentDegreeIs113724 = refl

pairedPhaseTotalIs131220 :
  firstPairedConstituentDegree + secondPairedConstituentDegree ≡ 131220
pairedPhaseTotalIs131220 = refl

pairedPhaseTotalIsTwoRegularSectors : 131220 ≡ 2 * 65610
pairedPhaseTotalIsTwoRegularSectors = refl

oneRegularSectorIs729Times90 : 65610 ≡ 729 * 90
oneRegularSectorIs729Times90 = refl

ninetyMatchesExistingModelMultiplicity :
  Multiplicity.modelMultiplicityDimension ≡ 90
ninetyMatchesExistingModelMultiplicity = refl

ninetyMatchesA005052Level2 : Nine.a005052 2 ≡ 90
ninetyMatchesA005052Level2 = Nine.ninetyIsA005052Level2

------------------------------------------------------------------------
-- Status correction: downstream records accepting ActualZetaSectorRecognition
-- are compilers/consumers.  They do not establish that a live inhabitant has
-- been produced on this branch.
------------------------------------------------------------------------

singleActionBoundary : Single.SingleActionProducerBoundary
singleActionBoundary = Single.canonicalSingleActionProducerBoundary

literalThreePhaseBoundary : Literal.LiteralThreePhaseResidualBoundary
literalThreePhaseBoundary = Literal.canonicalLiteralThreePhaseResidualBoundary

searchBoundary : Search.Monster3BRepresentationSearchBoundary
searchBoundary = Search.canonicalMonster3BRepresentationSearchBoundary

record ReplayStatusAudit : Set where
  constructor replay-status-audit
  field
    restrictionAlgorithmImplemented : Bool
    producerScriptPresent : Bool
    rendererPresent : Bool
    generatedCertificateRecipePresent : Bool
    generatedCertificateCommittedAtAuditedHead : Bool
    freshCurrentHeadKernelReceiptImportedHere : Bool
    downstreamRecognitionCompilerExists : Bool
    actualSingleActionProducerInhabitedUpstream : Bool
    commentSayingRecognitionExistsIsWitnessByItself : Bool
open ReplayStatusAudit public

canonicalReplayStatusAudit : ReplayStatusAudit
canonicalReplayStatusAudit = replay-status-audit
  true true true true
  false false true false false

------------------------------------------------------------------------
-- External coordinates and primary provenance.
------------------------------------------------------------------------

record ReplayMultiplicityExternalCoordinates : Set where
  constructor replay-multiplicity-external-coordinates
  field
    cyclicGroupQid : String
    groupRepresentationQid : String
    representationCharacterQid : String
    rootOfUnityQid : String
    powersOfThreeOEIS : String
    tenTimesPowersOfThreeOEIS : String
    monsterRepresentationDegreeOEIS : String
    multiplicityNinetyHasExactA005052Coordinate : Bool
    oeisCreatesTwelveSeventyEightDecomposition : Bool
    qidCreatesRestrictionReplay : Bool
open ReplayMultiplicityExternalCoordinates public

canonicalReplayMultiplicityExternalCoordinates : ReplayMultiplicityExternalCoordinates
canonicalReplayMultiplicityExternalCoordinates = replay-multiplicity-external-coordinates
  "Q245462" "Q1055807" "Q600043" "Q756747"
  "A000244" "A005052" "A001379"
  true false false

barracloughWilsonSource : Attribution.AttributedSource
barracloughWilsonSource = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary Monster subgroup/character-table provenance for the restriction lane; does not source the Base369/OEIS factorisation"
  Attribution.publicAttribution

terrasSource : Attribution.AttributedSource
terrasSource = Attribution.mkDOISource
  "Audrey Terras"
  "Fourier Analysis on Finite Groups and Applications"
  "Cambridge University Press"
  "1999"
  "10.1017/CBO9780511626265"
  "https://doi.org/10.1017/CBO9780511626265"
  Attribution.academicBookSource
  "finite-group Fourier/representation provenance for phase decomposition; not a source for CTblLib execution data"
  Attribution.publicAttribution

barracloughWilsonAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt barracloughWilsonSource

terrasAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt terrasSource

------------------------------------------------------------------------
-- BIDI firewalls.
------------------------------------------------------------------------

data NinetyEqualityCreatesSameMultiplicityRepresentation : Set where
data TwelvePlusSeventyEightCreatesBase369Action : Set where
data ExistingCompilerMeansRecognitionWitnessExists : Set where
data GeneratedRecipeMeansKernelReceiptExists : Set where

ninetyDoesNotIdentifyMultiplicityRepresentation :
  NinetyEqualityCreatesSameMultiplicityRepresentation → ⊥
ninetyDoesNotIdentifyMultiplicityRepresentation ()

twelveSeventyEightDoesNotCreateBase369Action :
  TwelvePlusSeventyEightCreatesBase369Action → ⊥
twelveSeventyEightDoesNotCreateBase369Action ()

compilerDoesNotManufactureRecognitionWitness :
  ExistingCompilerMeansRecognitionWitnessExists → ⊥
compilerDoesNotManufactureRecognitionWitness ()

recipeDoesNotManufactureKernelReceipt :
  GeneratedRecipeMeansKernelReceiptExists → ⊥
recipeDoesNotManufactureKernelReceipt ()

record ReplayMultiplicityFrontier : Set where
  constructor replay-multiplicity-frontier
  field
    twelvePlusSeventyEightIsNinetyPaid : Bool
    paired1458TimesTwelveSeventyEightArithmeticPaid : Bool
    pairedTotalIsTwoTimes65610Paid : Bool
    ninetyMatchesA005052Level2Paid : Bool
    restrictionAlgorithmExists : Bool
    generatedCertificateRecipeExists : Bool
    actualHeadReplayReceiptPaid : Bool
    actualSingleActionRecognitionPaid : Bool
    fixedRegular65610PlusResidual53Paid : Bool
    nextResidual : String
open ReplayMultiplicityFrontier public

currentReplayMultiplicityFrontier : ReplayMultiplicityFrontier
currentReplayMultiplicityFrontier = replay-multiplicity-frontier
  true true true true true true
  false false false
  "obtain/replay the actual generated Monster3B restriction certificate at the current head, then bind the literal selected 3B central action to the existing 729 x 90 recognition interface; only after that split the fixed phase as an action-stable regular 65610 block plus Residual53. Keep the exact 12+78=90=A005052(2) agreement as numerical/provenance support, not representation authority."
