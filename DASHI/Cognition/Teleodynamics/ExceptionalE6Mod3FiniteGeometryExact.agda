module DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact where

------------------------------------------------------------------------
-- E6 MOD-3 FINITE QUADRATIC GEOMETRY
--
-- DASHI CONTRIBUTION
--
-- This owner formalises the finite geometry surfaced by the E6 Cartan lattice
-- reduced modulo 3.  It distinguishes three proof grades:
--
--   * definitional / arithmetic facts paid in Agda here;
--   * external finite-computation receipts reproduced independently in local
--     Python;
--   * actual E6/Weyl/E8 recognition, which remains gated by explicit
--     same-carrier/action or incidence intertwiners.
--
-- In the coordinate convention used below the three nonzero quadratic strata
-- have sizes 80, 90 and 72.  Scaling the quadratic form by the nonsquare 2
-- swaps the labels of the 72 and 90 nonsingular classes, so class labels are
-- not semantic authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as F3Add
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as F3Mul

------------------------------------------------------------------------
-- 1. Concrete five-trit coordinate presentation.
------------------------------------------------------------------------

record E6QuotientV5 : Set where
  constructor e6-v5
  field
    x0 x1 x2 x3 x4 : Trit
open E6QuotientV5 public

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = F3Add._+3_

infixl 7 _⊗_
_⊗_ : Trit → Trit → Trit
_⊗_ = F3Mul._*3_

twice : Trit → Trit
twice x = neg ⊗ x

term : Trit → Trit → Trit
term a b = twice (a ⊗ b)

-- Gram matrix on one complement to the one-dimensional mod-3 radical of the
-- standard E6 Cartan matrix.  The quotient object is canonical; this basis is
-- only a coordinate presentation.
e6Bilinear : E6QuotientV5 → E6QuotientV5 → Trit
e6Bilinear x y =
  term (x0 x) (x0 y) ⊕ term (x0 x) (x1 y) ⊕
  term (x1 x) (x0 y) ⊕ term (x1 x) (x1 y) ⊕
  term (x1 x) (x2 y) ⊕ term (x1 x) (x4 y) ⊕
  term (x2 x) (x1 y) ⊕ term (x2 x) (x2 y) ⊕
  term (x2 x) (x3 y) ⊕
  term (x3 x) (x2 y) ⊕ term (x3 x) (x3 y) ⊕
  term (x4 x) (x1 y) ⊕ term (x4 x) (x4 y)

e6Quadratic : E6QuotientV5 → Trit
e6Quadratic x = e6Bilinear x x

------------------------------------------------------------------------
-- 2. Exact arithmetic spine.
------------------------------------------------------------------------

stateCount : Nat
stateCount = 243

zeroCount nullNonzeroCount class90Count class72Count : Nat
zeroCount = 1
nullNonzeroCount = 80
class90Count = 90
class72Count = 72

statePartition : stateCount ≡ zeroCount + nullNonzeroCount + class90Count + class72Count
statePartition = refl

projectiveTotal nullLineCount rootLineCount otherLineCount : Nat
projectiveTotal = 121
nullLineCount = 40
rootLineCount = 36
otherLineCount = 45

projectivePartition : projectiveTotal ≡ nullLineCount + rootLineCount + otherLineCount
projectivePartition = refl

------------------------------------------------------------------------
-- 3. External finite computation receipts.
--
-- These are evidence records, not kernel proofs of enumeration.  Lean mirrors
-- the concrete finite model with native_decide theorem targets.
------------------------------------------------------------------------

data EvidenceGrade : Set where
  sourceWrittenDefinition : EvidenceGrade
  localFiniteComputation : EvidenceGrade
  kernelCheckedTheorem : EvidenceGrade

record FiniteQuadraticComputationReceipt : Set where
  constructor finite-quadratic-computation-receipt
  field
    grade : EvidenceGrade
    cartanDeterminant : Nat
    mod3Rank : Nat
    radicalDimension : Nat
    quotientDimension : Nat
    total : Nat
    nullNonzero : Nat
    nonsingularA : Nat
    nonsingularB : Nat
    rootReductionImageSize : Nat
    rootReductionEqualsOneNonsingularStratum : Bool
    localPythonReproduced : Bool
    provenance : String
open FiniteQuadraticComputationReceipt public

canonicalFiniteQuadraticComputationReceipt : FiniteQuadraticComputationReceipt
canonicalFiniteQuadraticComputationReceipt =
  finite-quadratic-computation-receipt
    localFiniteComputation
    3 5 1 5
    243 80 90 72 72
    true true
    "local Python reconstruction from the standard E6 Cartan matrix; external finite computation, not Agda kernel certification"

record ProjectiveAssociationReceipt : Set where
  constructor projective-association-receipt
  field
    grade : EvidenceGrade
    nullVertices nullDegree nullLambda nullMu : Nat
    rootVertices rootDegree rootLambda rootMu : Nat
    otherVertices otherDegree otherLambda otherMu : Nat
    allThreeUniform : Bool
    provenance : String
open ProjectiveAssociationReceipt public

canonicalProjectiveAssociationReceipt : ProjectiveAssociationReceipt
canonicalProjectiveAssociationReceipt =
  projective-association-receipt
    localFiniteComputation
    40 12 2 4
    36 15 6 6
    45 12 3 3
    true
    "local exhaustive projective quotient computation; parameters are evidence until a kernel enumeration theorem is attached"

------------------------------------------------------------------------
-- 4. Same-object/action recognition gates.
------------------------------------------------------------------------

record E6RootQuadraticRecognition : Set₁ where
  field
    E6Root : Set
    RootClass72 : Set
    rootToClass : E6Root → RootClass72
    classToRoot : RootClass72 → E6Root
    rootRoundTrip : (r : E6Root) → classToRoot (rootToClass r) ≡ r
    classRoundTrip : (q : RootClass72) → rootToClass (classToRoot q) ≡ q

    Weyl : Set
    rootAction : Weyl → E6Root → E6Root
    finiteAction : Weyl → RootClass72 → RootClass72
    actionIntertwines :
      (g : Weyl) →
      (r : E6Root) →
      rootToClass (rootAction g r) ≡ finiteAction g (rootToClass r)

    constructionProvenance : String

record E6WeylFaithfulMod3Recognition : Set₁ where
  field
    Weyl : Set
    act : Weyl → E6QuotientV5 → E6QuotientV5
    preservesBilinear :
      (g : Weyl) →
      (x y : E6QuotientV5) →
      e6Bilinear (act g x) (act g y) ≡ e6Bilinear x y
    FaithfulnessReceipt : Set
    faithfulnessProvenance : String

------------------------------------------------------------------------
-- 5. S6/A5 and E6--E8 incidence targets.
------------------------------------------------------------------------

record RootStabilizerA5Recognition : Set₁ where
  field
    RootLine : Set
    OrthogonalRootLine : Set
    SixSet : Set
    twoSubsetEncoding : OrthogonalRootLine → Set
    stabilizerOrder : Nat
    stabilizerOrderIs720 : stabilizerOrder ≡ 720
    kgSixTwoIntertwinerReceipt : Set
    provenance : String

record E6E8DualIncidenceRecognition : Set₁ where
  field
    E6NullProjectivePoint : Set
    E8SymplecticProjectivePoint : Set
    E8SymplecticProjectiveLine : Set
    e6NullToE8Line : E6NullProjectivePoint → E8SymplecticProjectiveLine
    e8LineToE6Null : E8SymplecticProjectiveLine → E6NullProjectivePoint
    e6AfterE8 :
      (x : E6NullProjectivePoint) →
      e8LineToE6Null (e6NullToE8Line x) ≡ x
    e8AfterE6 :
      (l : E8SymplecticProjectiveLine) →
      e6NullToE8Line (e8LineToE6Null l) ≡ l
    incidenceIntertwinerReceipt : Set
    provenance : String

------------------------------------------------------------------------
-- 6. Negative results / non-promotion boundaries.
------------------------------------------------------------------------

linearFourTritPossibleFixedNonzeroCounts : String
linearFourTritPossibleFixedNonzeroCounts = "0,2,8,26,80 = 3^d-1 for d=0..4"

data EightyCountCreatesLinearT4Recognition : Set where
data MatchingSRGParametersCreateIncidenceIsomorphism : Set where
data DepthNormCreatesProductDecomposition : Set where
data FinitePythonReceiptCreatesKernelTheorem : Set where

eightyCountDoesNotCreateLinearT4 : EightyCountCreatesLinearT4Recognition → ⊥
eightyCountDoesNotCreateLinearT4 ()

matchingParametersDoNotCreateIsomorphism : MatchingSRGParametersCreateIncidenceIsomorphism → ⊥
matchingParametersDoNotCreateIsomorphism ()

depthNormDoesNotCreateProduct : DepthNormCreatesProductDecomposition → ⊥
depthNormDoesNotCreateProduct ()

pythonReceiptDoesNotCreateKernelTheorem : FinitePythonReceiptCreatesKernelTheorem → ⊥
pythonReceiptDoesNotCreateKernelTheorem ()

record ExceptionalE6Mod3FiniteGeometryBoundary : Set where
  constructor exceptional-e6-mod3-finite-geometry-boundary
  field
    concreteV5QuadraticDefinitionWritten : Bool
    arithmetic243PartitionPaid : Bool
    projective121PartitionPaid : Bool
    localFiniteEnumerationReceiptPresent : Bool
    localProjectiveSRGReceiptPresent : Bool
    e6RootSameObjectRecognitionInhabitedHere : Bool
    faithfulWeylActionInhabitedHere : Bool
    a5S6RecognitionInhabitedHere : Bool
    e6E8DualIncidenceRecognitionInhabitedHere : Bool
    t4LinearIdentificationClaimed : Bool
    depthNormProductClaimed : Bool
    localPythonPromotedToKernelProof : Bool

canonicalExceptionalE6Mod3FiniteGeometryBoundary :
  ExceptionalE6Mod3FiniteGeometryBoundary
canonicalExceptionalE6Mod3FiniteGeometryBoundary =
  exceptional-e6-mod3-finite-geometry-boundary
    true true true true true
    false false false false
    false false false
