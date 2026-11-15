module DASHI.Reasoning.ExceptionalE8AlbertF4ClassificationMaxCutExact where

------------------------------------------------------------------------
-- TERMINAL CURRENT EXCEPTIONAL CLASSIFICATION MAX-CUT
--
-- The local exceptional-algebra discovery programme is exhausted through an
-- intrinsic structured E8 root datum and an actual rational Albert algebra.
--
-- Native/local structure owned or exact-executable in the repo includes:
--
-- * rational H_3(O_Q), unit, cubic norm, Jordan product/identity;
-- * arbitrary inner-derivation law;
-- * exact 52-dimensional inner-derivation span;
-- * exact 28+8_v+8_s+8_c triality decomposition and bracket pattern;
-- * four explicit commuting Cartan derivations with vector/spin chirality;
-- * exact symbolic Q(i) root spaces: zero weight rank 4 plus 48 one-dimensional
--   nonzero root spaces = 24+8+8+8;
-- * exact bracket grading on all 1128 unordered root pairs;
-- * the root labels are literally the standard F4 root set after the declared
--   Q(i) scalar extension;
-- * companion Lean independently owns the same F4 root/Coxeter datum and Weyl
--   order 1152.
--
-- Companion Lean #52 has now narrowed the ORIGINAL-Q form boundary further:
--
-- * the literal positive eight-square rational octonion norm is theorem-bearing
--   anisotropic and hence the native octonion algebra has no zero divisors;
-- * the Q(i) 4+48 root chart is explicitly scalar-extension/splitting data and
--   does NOT classify the original Q-form;
-- * unit-fixing cubic symmetries and Jordan automorphisms are the same action
--   class on the same native carrier, so the structural
--   Stab_Isom(N)(1)=Aut_J(J) seam is locally paid.
--
-- TauCetiProject/TauCeti at pinned commit
--   85ed0984159b8de1ed8c11541105bb1d89c787e4
-- contains substantial formal Albert and canonical-F4 infrastructure.  The
-- audited search did not locate a same-object Albert-derivation -> canonical-F4
-- Lie equivalence or Albert-aut/F4 group theorem.  Tau Ceti remains an external
-- formal donor candidate; its Apache-2.0/source authorship is retained.
--
-- Therefore the surviving external classification wall has exactly three
-- named-form/group conclusions:
--
-- * native Der(J) is the appropriate rational form of type F4;
-- * native Aut_J(J) is the corresponding F4 algebraic group;
-- * native cubic norm-isometry/structure group is of type E6.
--
-- The old external unit-stabilizer leaf is retired because its concrete
-- same-action structural content is already paid in Lean.  Agda records that
-- result only as a cross-prover receipt; Lean kernel authority is not imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.CompositionAlgebraCoreExact as Composition
import DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact as Source
import DASHI.Mathematics.Algebra.RationalAlbertAutomorphismFixesUnitExact as UnitFix
import DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact as Linear
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact as ExactRoots
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactRootGradingReceiptExact as Grading
import DASHI.Mathematics.Algebra.RationalAlbertF4SplitRootDatumRecognitionExact as SplitF4
import DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryExact as Instantiation
import DASHI.Reasoning.AlbertF4LeanQFormAnisotropyReceiptExact as LeanQ
import DASHI.Reasoning.AlbertF4TauCetiFormalDonorReceiptExact as TauCeti
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
    exactRootGradingAll1128PairsPaid : Bool
    splitQIRootDatumTypeF4Recognized : Bool
    qiRootDataRecordedAsScalarExtension : Bool
    qiRootDataClassifiesOriginalQForm : Bool
    floatingRootExtractionSuperseded : Bool
    companionLeanIndependentF4RootDatumPaid : Bool
    companionLeanF4WeylOrder1152Paid : Bool
    typedLinearJordanAutCarrierPaid : Bool

    nativeQOctonionNormAnisotropyLeanReceiptPaid : Bool
    nativeQOctonionNoZeroDivisorsLeanReceiptPaid : Bool
    nativeNormUnitEqualsJordanSameActionLeanReceiptPaid : Bool
    leanKernelProofAuthorityImportedIntoAgda : Bool

    classicalRationalDerivationFormF4SourcePaid : Bool
    classicalAutAlbertTypeF4SourcePaid : Bool
    classicalCubicSymmetryTypeE6SourcePaid : Bool
    linearSameCarrierE6F4TargetTyped : Bool
    allConcreteClassificationHypothesesOwned : Bool
    remainingClassificationIsQFormAndGroupLevel : Bool

    tauCetiFormalDonorInventoryLocated : Bool
    tauCetiSameObjectClassificationLocated : Bool
    externalFormalDonorAuthorityImportedIntoAgda : Bool

    externalUnitStabilizerClassificationLeafRemaining : Bool
    threeNamedFormGroupLeavesRemain : Bool
    generalExceptionalClassificationFormalizedInRepo : Bool
    formalRationalDerivationFormF4Paid : Bool
    formalAutAlbertEqualsF4Paid : Bool
    formalCubicGroupEqualsE6Paid : Bool

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
    Grading.canonicalBoundary.localF4RootGradedLieStructurePaidByProducer
    SplitF4.canonicalBoundary.splitLieRootDatumTypeF4Recognized
    LeanQ.canonicalBoundary.qiRootChartRecordedAsScalarExtensionData
    LeanQ.canonicalBoundary.qiRootChartClassifiesOriginalQForm
    true true true true
    LeanQ.canonicalBoundary.leanNativeQOctonionNormAnisotropySourceWritten
    LeanQ.canonicalBoundary.leanNativeQOctonionNoZeroDivisorsSourceWritten
    LeanQ.canonicalBoundary.sameActionStructuralStabilizerPaidInLean
    LeanQ.canonicalBoundary.leanKernelProofAuthorityImportedIntoAgda
    true true true true
    Instantiation.canonicalBoundary.allConcreteExceptionalHypothesesOwned
    Instantiation.canonicalBoundary.remainingClassificationIsQFormAndGroupLevel
    TauCeti.canonicalBoundary.tauCetiAlbertStackLocated
    TauCeti.canonicalBoundary.sameObjectAlbertToCanonicalF4BridgeLocated
    TauCeti.canonicalBoundary.externalFormalAuthorityImportedIntoAgda
    false true
    false false false false
    false true false false
    "Local Albert/F4 structure is exhausted through actual H3(O_Q), exact derivations/triality/Cartan, Q(i) root grading and cross-kernel same-action rigidity receipts. Lean #52 adds theorem-bearing native-Q octonion norm anisotropy/no-zero-divisors and explicitly separates Q(i) scalar-extension data from original-Q classification. The old external unit-stabilizer leaf is retired. TauCeti is a pinned formal donor candidate but no same-object Albert-to-canonical-F4 theorem was located at the audited commit. Exactly three named original-Q form/group leaves remain: Der(J):F4-form, Aut_J(J):F4-group, cubic symmetry:E6-group."
