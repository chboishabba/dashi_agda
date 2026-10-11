module DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryExact where

------------------------------------------------------------------------
-- TERMINAL FORMAL CLASSIFICATION INTERFACE FOR THE ACTUAL RATIONAL ALBERT
-- ALGEBRA
--
-- All discovery-specific hypotheses are now represented on concrete in-repo
-- objects or exact executable certificates:
--
-- * exact rational alternative composition octonions;
-- * literal H_3(O_Q) Jordan algebra with unit, product, cubic norm and Jordan
--   identity;
-- * generic inner-derivation theorem for arbitrary Albert elements;
-- * exact executable 52-dimensional derivation span;
-- * exact 28+8_v+8_s+8_c triality bracket decomposition;
-- * exact Q(i) root-space decomposition 4 + 48 with one-dimensional roots;
-- * exact Q(i) root-grading bracket law on all C(48,2)=1128 root pairs;
-- * independent standard F4 root/Coxeter datum on companion Lean;
-- * actual same-carrier linear Jordan automorphism type with explicit elements.
--
-- What is left is no longer an exceptional-geometry search.  It is the general
-- characteristic-zero classification theorem that identifies the derivation
-- algebra / automorphism group of this Albert algebra with a rational form of
-- type F4, and the cubic linear symmetry group with type E6.  This module makes
-- that external theorem a single explicit premise instead of hiding it behind
-- several Boolean frontier flags.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.CompositionAlgebraCoreExact as Composition
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as Inner
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact as Weights
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactRootGradingReceiptExact as Grading
import DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact as Linear
import DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact as Sources

record ConcreteClassificationHypotheses : Set where
  constructor concrete-classification-hypotheses
  field
    characteristicZeroBase : Bool
    exactOctonionCompositionCore : Bool
    exactOctonionAlternativity : Bool
    literalHermitianThreeByThreeCarrier : Bool
    literalJordanProduct : Bool
    literalJordanIdentity : Bool
    literalCubicNorm : Bool
    genericInnerDerivationLaw : Bool
    exactDerivationDimension52 : Bool
    exactCartanDimension4 : Bool
    exactNonzeroRootSpaceCount48 : Bool
    exactOneDimensionalRootSpaces : Bool
    exactTrialityRootPartition : Bool
    exactRootGradingBracketLaw : Bool
    sameCarrierLinearExceptionalTargetsTyped : Bool
open ConcreteClassificationHypotheses public

canonicalConcreteClassificationHypotheses : ConcreteClassificationHypotheses
canonicalConcreteClassificationHypotheses =
  concrete-classification-hypotheses
    true true true true true
    true true true true true
    true true true
    Grading.canonicalBoundary.localF4RootGradedLieStructurePaidByProducer
    true

------------------------------------------------------------------------
-- One imported theorem premise is enough to finish the naming/classification
-- layer.  It deliberately carries the source/form-sensitive content rather
-- than reconstructing classification from dimension or root counts.
------------------------------------------------------------------------

record CharacteristicZeroAlbertClassificationTheorem : Set₁ where
  field
    DerivationTypeF4 : Set
    AutomorphismGroupTypeF4 : Set
    CubicSymmetryGroupTypeE6 : Set
    F4EqualsUnitStabilizerInE6 : Set
open CharacteristicZeroAlbertClassificationTheorem public

record ClassificationInstantiation
    (classification : CharacteristicZeroAlbertClassificationTheorem) : Set₁ where
  field
    concreteHypotheses : ConcreteClassificationHypotheses
    derivationF4 : DerivationTypeF4 classification
    automorphismF4 : AutomorphismGroupTypeF4 classification
    cubicSymmetryE6 : CubicSymmetryGroupTypeE6 classification
    unitStabilizer : F4EqualsUnitStabilizerInE6 classification
open ClassificationInstantiation public

record Boundary : Set where
  constructor boundary
  field
    allConcreteExceptionalHypothesesOwned : Bool
    exactRootSpaceProducerFloatingFree : Bool
    exactRootGradingProducerPaid : Bool
    literatureClassificationSourceLocated : Bool
    classificationReducedToOneExternalTheoremPremise : Bool
    generalClassificationTheoremFormalizedInRepo : Bool
    actualInstantiationInhabited : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true
    true
    Grading.canonicalBoundary.localF4RootGradedLieStructurePaidByProducer
    Sources.canonicalClassicalExceptionalSourceReceipt.peterssonDerivationTheoremLocated
    true
    false
    false

classificationSourceNote : String
classificationSourceNote =
  "Chevalley-Schafer / Petersson / Springer-Veldkamp: Der(Albert) and Aut(Albert) are type F4 in characteristic zero; cubic determinant symmetry is type E6."
