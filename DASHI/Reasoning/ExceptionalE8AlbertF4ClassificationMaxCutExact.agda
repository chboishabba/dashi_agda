module DASHI.Reasoning.ExceptionalE8AlbertF4ClassificationMaxCutExact where

------------------------------------------------------------------------
-- TERMINAL CURRENT EXCEPTIONAL CLASSIFICATION MAX-CUT
--
-- The finite/root/Jordan discovery programme is now exhausted through an
-- intrinsic structured E8 root datum and an actual rational Albert algebra.
-- The former floating F4 root-space diagnostic has additionally been replaced
-- by an exact symbolic Q(i) projector computation.
--
-- Internally/source-written or exact-executable on the same concrete objects:
--   * rational alternative composition octonions;
--   * H_3(O_Q), unit, cubic norm, Jordan product and Jordan identity;
--   * arbitrary inner-derivation law;
--   * exact 52-dimensional inner-derivation span;
--   * exact 28+8_v+8_s+8_c triality decomposition and bracket pattern;
--   * four explicit commuting Cartan derivations with vector/spin chirality;
--   * exact Q(i) root-space decomposition: rank-4 zero space + 48 one-
--     dimensional nonzero root spaces = 24+8+8+8;
--   * companion Lean standard F4 root datum and Weyl closure order 1152;
--   * actual same-carrier linear Jordan automorphism carrier with explicit
--     coordinate, signed-basis-octonion, and Moufang-triality elements;
--   * every compiled Jordan automorphism fixes the actual Jordan unit.
--
-- Classical sources identify Der(Albert) and Aut(Albert) as type F4 and the
-- cubic determinant symmetry group as type E6 in characteristic zero.
-- Therefore the only remaining formal exceptional-classification seam is the
-- GENERAL classification theorem itself (or an imported formal version of it)
-- instantiated on this rational form.  There is no longer a missing local
-- carrier, product, action, triality decomposition, Cartan or root-space search.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.CompositionAlgebraCoreExact as Composition
import DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact as Source
import DASHI.Mathematics.Algebra.RationalAlbertAutomorphismFixesUnitExact as UnitFix
import DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact as Linear
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact as ExactRoots
import DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryExact as Instantiation
import DASHI.Reasoning.ExceptionalE8AlbertF4RootMaxCutExact as Previous

record ExceptionalClassificationBoundary : Set where
  constructor exceptional-classification-boundary
  field
    exactRationalOctonionCompositionCorePaid : Bool
    actualRationalAlbertJordanAlgebraPaid : Bool
    arbitraryInnerDerivationLawPaid : Bool
    actualJordanAutomorphismsFixUnitPaid : Bool
    derivationDimension52PaidByExactProducer : Bool
    exactTrialityTwentyEightEightEightEightPaid : Bool
    exactCartanFourVectorSpinSpinPaid : Bool
    exactQIRootSpacesFourPlusFortyEightPaid : Bool
    floatingRootExtractionSuperseded : Bool
    companionLeanIndependentF4RootDatumPaid : Bool
    companionLeanF4WeylOrder1152Paid : Bool
    typedLinearJordanAutCarrierPaid : Bool

    classicalDerivationTypeF4SourcePaid : Bool
    classicalAutAlbertTypeF4SourcePaid : Bool
    classicalCubicSymmetryTypeE6SourcePaid : Bool
    linearSameCarrierE6F4TargetTyped : Bool
    allConcreteClassificationHypothesesOwned : Bool
    classificationReducedToSingleExternalPremise : Bool

    generalExceptionalClassificationFormalizedInRepo : Bool
    formalDerAlbertTypeF4InstantiationPaid : Bool
    formalAutAlbertEqualsF4Paid : Bool
    formalCubicGroupEqualsE6Paid : Bool
    formalF4EqualsE6UnitStabilizerPaid : Bool

    monsterNormalizerPhysicalRealizationPaid : Bool
    originalT5NaturalRestrictionBlocked : Bool
    originalT5IndependentRecognitionPaid : Bool
    empiricalLilaInstantiationPaid : Bool
    note : String
open ExceptionalClassificationBoundary public

canonicalExceptionalClassificationBoundary : ExceptionalClassificationBoundary
canonicalExceptionalClassificationBoundary =
  exceptional-classification-boundary
    true true true true
    true true true
    ExactRoots.canonicalBoundary.exactQIRootSpaceDecompositionPaidByProducer
    true true true true
    true true true true
    Instantiation.canonicalBoundary.allConcreteExceptionalHypothesesOwned
    Instantiation.canonicalBoundary.classificationReducedToOneExternalTheoremPremise
    false false false false false
    false true false false
    "All concrete exceptional hypotheses are now owned on the actual rational Albert/E8 objects, including an exact non-floating Q(i) 4+48 root-space certificate and an independent F4 Weyl datum. The remaining formal seam is a general characteristic-zero Albert/Lie/algebraic-group classification theorem, already located in classical sources but not formalized in this repo. Monster normalizer realization, any genuinely new original-T5 recognition, and LILA remain independent lanes."
