module DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryExact where

------------------------------------------------------------------------
-- TERMINAL FORMAL CLASSIFICATION INTERFACE FOR THE ACTUAL RATIONAL ALBERT
-- ALGEBRA
--
-- The local algebra/root-data lane owns the literal H_3(O_Q) Jordan algebra,
-- cubic norm, arbitrary inner derivations, exact dimension-52 derivation span,
-- triality decomposition, Q(i) 4+48 root spaces, full root grading and split-F4
-- root-datum recognition.
--
-- Companion Lean #52 source-writes cubic/adjoint recovery, nondegenerate trace
-- pairing and norm+unit rigidity on the same literal rational carrier.  Agda
-- records this only as a cross-prover receipt: no Lean proof authority is
-- silently transferred.
--
-- A new exact rational producer also evaluates the represented derivation
-- algebra at the real place: G_ij = -tr_27(D_i D_j) has rank 52 with exact
-- positive LDL diagonal and the represented center has dimension zero.  This
-- strongly selects the compact real completion as the correct target, but the
-- receipt deliberately does NOT classify the real form or the global Q-form.
--
-- Consequently:
--   * Stab_{Isom(N)}(1)=Aut(J) is structurally reduced by norm+unit rigidity;
--   * the real-place target is sharply constrained by exact invariant-form
--     diagnostics;
--   * the remaining terminal theorem is still original-Q-form/algebraic-group
--     classification: Der(J), Aut(J) and Isom(N) as the appropriate F4/E6
--     forms, instantiated proof-relevantly on this same object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.CompositionAlgebraCoreExact as Composition
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as Inner
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact as Weights
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactRootGradingReceiptExact as Grading
import DASHI.Mathematics.Algebra.RationalAlbertF4SplitRootDatumRecognitionExact as SplitF4
import DASHI.Mathematics.Algebra.RationalAlbertF4RealPlaceCompactnessReceiptExact as RealPlace
import DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact as Linear
import DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact as Sources
import DASHI.Reasoning.AlbertF4LeanCubicNormRigidityReceiptExact as Rigidity

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
    splitQIRootDatumTypeF4Recognized : Bool
    sameCarrierLinearExceptionalTargetsTyped : Bool
open ConcreteClassificationHypotheses public

canonicalConcreteClassificationHypotheses : ConcreteClassificationHypotheses
canonicalConcreteClassificationHypotheses =
  concrete-classification-hypotheses
    true true true true true
    true true true true true
    true true true
    Grading.canonicalBoundary.localF4RootGradedLieStructurePaidByProducer
    SplitF4.canonicalBoundary.splitLieRootDatumTypeF4Recognized
    true

------------------------------------------------------------------------
-- Proof-relevant imported theorem/application interface.
------------------------------------------------------------------------

record CharacteristicZeroAlbertClassificationTheorem : Set₁ where
  field
    RationalDerivationFormOfF4 : Set
    AutomorphismGroupTypeF4 : Set
    CubicSymmetryGroupTypeE6 : Set
    F4EqualsUnitStabilizerInE6 : Set
open CharacteristicZeroAlbertClassificationTheorem public

record ClassificationInstantiation
    (classification : CharacteristicZeroAlbertClassificationTheorem) : Set₁ where
  field
    concreteHypotheses : ConcreteClassificationHypotheses
    rationalDerivationForm : RationalDerivationFormOfF4 classification
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
    splitQIRootDatumTypeF4Recognized : Bool
    literatureClassificationSourceLocated : Bool
    remainingClassificationIsQFormAndGroupLevel : Bool
    normUnitRigiditySourceWrittenCrossKernel : Bool
    unitStabilizerJordanEqualityStructurallyReduced : Bool
    normUnitRigidityAgdaAuthorityPaid : Bool
    exactPositiveTraceFormRealPlaceDiagnosticPaid : Bool
    compactRealPlaceSuggested : Bool
    compactRealPlaceClassificationPaid : Bool
    realPlaceDiagnosticClassifiesOriginalQForm : Bool
    generalClassificationTheoremFormalizedInRepo : Bool
    actualQFormGroupInstantiationInhabited : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true
    true
    Grading.canonicalBoundary.localF4RootGradedLieStructurePaidByProducer
    SplitF4.canonicalBoundary.splitLieRootDatumTypeF4Recognized
    Sources.canonicalClassicalExceptionalSourceReceipt.peterssonDerivationTheoremLocated
    true
    Rigidity.canonicalBoundary.normUnitRigiditySourceWritten
    Rigidity.canonicalBoundary.unitStabilizerJordanEqualityStructurallyReduced
    Rigidity.canonicalBoundary.crossKernelProofAuthorityTransferred
    RealPlace.canonicalBoundary.exactPositiveInvariantTraceFormDiagnosticPaid
    RealPlace.canonicalBoundary.compactRealPlaceSuggestedByDiagnostic
    RealPlace.canonicalBoundary.compactRealPlaceClassificationFormalized
    RealPlace.canonicalBoundary.originalQFormClassifiedFromRealPlaceAlone
    false
    false

classificationSourceNote : String
classificationSourceNote =
  "Chevalley-Schafer / Petersson / Springer-Veldkamp provide characteristic-zero Albert/F4/E6 classification provenance. Companion Lean locally reduces unit-fixing cubic symmetry to Jordan automorphism on the native rational carrier. Exact rational trace-form diagnostics strongly select the compact real completion, but neither the Lean source nor the real-place computation is Agda/global-Q classification authority. The unpaid endpoint is the original-Q-form/full algebraic-group classification and its proof-relevant instantiation on this same object."
