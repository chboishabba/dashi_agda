module DASHI.Moonshine.Monster3BAtlasSourceD4OrderTwelvePhaseSieveExact where

------------------------------------------------------------------------
-- EXTERNAL ROOT / AUTHORSHIP (NOT NEW):
-- ATLAS of Finite Group Representations, original Monster power-ups
-- https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/
--   2B <- 4A,4C,4D; 3B <- 12B,12F,12G,12H,12I;
--   4A <- 12B; 4C <- 12H,12I; 4D <- 12F;
--   6E <- 12B,12H,12I; 6B <- 12F.
-- Norton--Wilson, Anatomy of the Monster II (2002),
-- DOI 10.1112/S0024611502013357: centre of 2.Suz is Monster 2B.
-- Barraclough--Wilson (2007), DOI 10.1112/S1461157000001352:
-- original 3B normalizer quotient and source-generator convention.
-- Conway--Norton / Ford--McKay--Norton: original Monster twining.
--
-- REPOSITORY PRIOR OWNERS:
-- #1098 actual ATLAS 2.Suz:2 original source word D4 with r²=-I12,
-- #1250 geometric no-go and earlier conditional 2B/6B/6E parity
-- discriminator (DO NOT reinvent actual Hom/Stone-von-Neumann).
--
-- This module transports the finite SOURCE-INPUT incidence relation
-- through a type-safe D4/class quotient consumer. An explicit 4A/4C/4D
-- class for the particular source word r, Monster diagonal H/D_i,
-- selected 6.Suz degree78 and actual Hom are NOT proved here.
-- Source-written Agda, untypechecked unless independently certified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

data MonsterFourClass : Set where
  fourA fourB fourC fourD : MonsterFourClass

data MonsterTwelveClass : Set where
  twelveB twelveF twelveH twelveI : MonsterTwelveClass

data MonsterSixClass : Set where
  sixB sixE : MonsterSixClass

data SuzukiMultiplicityFamily : Set where
  faithful78 nonfaithful78CentrePlus : SuzukiMultiplicityFamily

data FibreInversionScalar : Set where
  negativeParity positiveParity : FibreInversionScalar

record SourcePhaseRow : Set where
  constructor sourcePhaseRow
  field
    orderTwelveClass : MonsterTwelveClass
    orderSixClass : MonsterSixClass
    selectedPhaseTrace : Nat
    necessarySuzukiFamily : SuzukiMultiplicityFamily
    necessaryFibreParity : FibreInversionScalar
open SourcePhaseRow public

-- ATLAS four-class/cube/square power intersections; NOT an
-- authentication of which of these classes contains the source word r.
possibleSourceD4Rows : MonsterFourClass → List SourcePhaseRow
possibleSourceD4Rows fourA =
  sourcePhaseRow twelveB sixE 90 faithful78 negativeParity ∷ []
possibleSourceD4Rows fourB = []
possibleSourceD4Rows fourC =
  sourcePhaseRow twelveH sixE 90 faithful78 negativeParity
  ∷ sourcePhaseRow twelveI sixE 90 faithful78 negativeParity ∷ []
possibleSourceD4Rows fourD =
  sourcePhaseRow twelveF sixB 66 nonfaithful78CentrePlus positiveParity
  ∷ []

sourceFourBIncompatibleWithTwoBHalfTurn :
  possibleSourceD4Rows fourB ≡ []
sourceFourBIncompatibleWithTwoBHalfTurn = refl

sourceFourAAcceptsTwelveBSixENinety :
  possibleSourceD4Rows fourA
  ≡ sourcePhaseRow twelveB sixE 90 faithful78 negativeParity ∷ []
sourceFourAAcceptsTwelveBSixENinety = refl

sourceFourCAcceptsTwoOrderTwelveClasses :
  possibleSourceD4Rows fourC
  ≡ (sourcePhaseRow twelveH sixE 90 faithful78 negativeParity
     ∷ sourcePhaseRow twelveI sixE 90 faithful78 negativeParity ∷ [])
sourceFourCAcceptsTwoOrderTwelveClasses = refl

sourceFourDForcesSixBSixtySix :
  possibleSourceD4Rows fourD
  ≡ sourcePhaseRow twelveF sixB 66 nonfaithful78CentrePlus positiveParity
    ∷ []
sourceFourDForcesSixBSixtySix = refl

-- Tr_(Wζ)(r²)=(χ_M(r²)-χ_M(zr²))/3.
-- Source original Monster character values:
-- χ(2B)=275, χ(6B)=77, χ(6E)=5.
sixBPhaseTraceArithmetic : 3 * 66 + 77 ≡ 275
sixBPhaseTraceArithmetic = refl

sixEPhaseTraceArithmetic : 3 * 90 + 5 ≡ 275
sixEPhaseTraceArithmetic = refl

-- This is intentionally a CONDITIONAL finite ATLAS table consumer,
-- not a proof of the actually selected full Monster class function.
record SourcePhaseSieveBoundary : Set where
  constructor sourcePhaseSieveBoundary
  field
    reusedOriginalATLASMonsterPowerups : Bool
    reusedOriginalNortonWilsonTwoBFusion : Bool
    reusedOriginalBarracloughWilsonNormalizer : Bool
    reusedRepo1098ActualSourceD4 : Bool
    finiteConditionalClassSieveWritten : Bool
    actualRotationFourClassAuthenticated : Bool
    actualZTimesRotationTwelveClassAuthenticated : Bool
    actualSuzukiSelectedDegree78FullClassCharacter : Bool
    actualMonsterDiagonalQuotientHom : Bool
    agdaKernelChecked : Bool

currentBoundary : SourcePhaseSieveBoundary
currentBoundary = sourcePhaseSieveBoundary
  true true true true true false false false false false
