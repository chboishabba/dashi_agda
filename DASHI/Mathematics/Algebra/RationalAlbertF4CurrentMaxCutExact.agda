module DASHI.Mathematics.Algebra.RationalAlbertF4CurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT RATIONAL ALBERT / F4 MAX-CUT
--
-- The local exceptional-algebra discovery programme is paid/source-written or
-- exact-executable through:
--
-- * exact rational octonions and the actual H_3(O_Q) Jordan algebra;
-- * identity, trace, cubic determinant/norm, Jordan product and Jordan identity;
-- * explicit same-carrier automorphisms and typed linear Jordan automorphisms;
-- * generic arbitrary-element inner-derivation law;
-- * exact inner-derivation span dimension 52;
-- * exact triality basis 52 = 28 + 8_v + 8_s + 8_c and bracket pattern;
-- * exact four-dimensional Cartan with vector / chiral half-spin roles;
-- * exact symbolic Q(i) projectors giving zero-weight dimension 4 and 48
--   one-dimensional nonzero root spaces = 24 + 8 + 8 + 8;
-- * companion Lean standard F4 root/Coxeter datum and Weyl order 1152.
--
-- Companion Lean #52 additionally source-writes theorem-bearing original-Q
-- octonion norm anisotropy/no-zero-divisors and the exact same-action equality
-- between unit-fixing cubic symmetries and Jordan automorphisms.  Its Q(i) root
-- chart is explicitly scalar-extension data rather than original-Q-form
-- classification.  Agda records those as cross-prover receipts only.
--
-- TauCeti is pinned as a formal donor candidate containing both Albert and
-- canonical-F4 stacks, but no same-object bridge was located at the audited
-- commit.  Therefore the remaining theorem is genuinely the characteristic-
-- zero/original-Q classification of three already-constructed native objects:
-- Der(J) as the appropriate F4 form, Aut_J(J) as the F4 algebraic group, and
-- the cubic norm-isometry/structure group as type E6.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as Cubic
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4BoundaryExact as Inner
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as InnerLaw
import DASHI.Mathematics.Algebra.RationalAlbertTrialityDerivationExact as Triality
import DASHI.Mathematics.Algebra.RationalAlbertF4CartanRootReceiptExact as Cartan
import DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact as ExactRoots
import DASHI.Mathematics.Algebra.RationalAlbertLinearJordanAutomorphismExact as LinearAut
import DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryExact as Classification
import DASHI.Reasoning.AlbertF4LeanQFormAnisotropyReceiptExact as LeanQ
import DASHI.Reasoning.AlbertF4TauCetiFormalDonorReceiptExact as TauCeti

record F4CrossKernelReceipt : Set where
  constructor f4-cross-kernel-receipt
  field
    f4RootCount : Nat
    f4Rank : Nat
    f4WeylOrder : Nat
    albertDerivationRank : Nat
    octonionDerivationRank : Nat
    zeroWeightDimension : Nat
    nonzeroOneDimensionalRootSpaces : Nat
    so8Dimension : Nat
    vectorDimension : Nat
    spinPlusDimension : Nat
    spinMinusDimension : Nat
    floatingPointUsedForFinalRootCertificate : Bool
open F4CrossKernelReceipt public

canonicalF4CrossKernelReceipt : F4CrossKernelReceipt
canonicalF4CrossKernelReceipt =
  f4-cross-kernel-receipt 48 4 1152 52 14 4 48 28 8 8 8 false

arbitraryAlbertInnerDerivationLaw :
  (left right : Cubic.RationalAlbert) ->
  Inner.DerivationLaw (Inner.innerDerivation left right)
arbitraryAlbertInnerDerivationLaw = InnerLaw.innerDerivationLaw

record CurrentF4Boundary : Set where
  constructor current-f4-boundary
  field
    rationalAlbertAlgebraPaid : Bool
    typedLinearJordanAutomorphismCarrierPaid : Bool
    arbitraryInnerDerivationLawPaid : Bool
    exactAlbertDerivationRank52Paid : Bool
    exactTrialityTwentyEightEightEightEightPaid : Bool
    exactTrialityBracketPatternPaid : Bool
    exactCartanVectorSpinSpinPaid : Bool
    exactQIRootSpacesFourPlusFortyEightPaid : Bool
    qiRootDataRecordedAsScalarExtension : Bool
    qiRootDataClassifiesOriginalQForm : Bool
    floatingRootExtractionSuperseded : Bool
    independentF4Root48LeanReceiptPaid : Bool
    independentF4Rank4LeanReceiptPaid : Bool
    independentF4Weyl1152LeanReceiptPaid : Bool
    nativeQOctonionNormAnisotropyLeanReceiptPaid : Bool
    nativeQOctonionNoZeroDivisorsLeanReceiptPaid : Bool
    nativeNormUnitEqualsJordanSameActionLeanReceiptPaid : Bool
    leanProofAuthorityImportedIntoAgda : Bool
    tauCetiFormalDonorInventoryLocated : Bool
    tauCetiSameObjectClassificationLocated : Bool
    allConcreteClassificationHypothesesOwned : Bool
    classificationReducedToSingleExternalPremise : Bool
    externalUnitStabilizerClassificationLeafRemaining : Bool
    threeNamedFormGroupLeavesRemain : Bool
    generalExceptionalClassificationFormalizedInRepo : Bool
    sameLieAlgebraF4ClassificationPaid : Bool
    fullF4AutomorphismGroupPaid : Bool
    cubicE6GroupClassificationPaid : Bool
open CurrentF4Boundary public

currentF4Boundary : CurrentF4Boundary
currentF4Boundary =
  current-f4-boundary
    true true true true
    true true true
    ExactRoots.canonicalBoundary.exactQIRootSpaceDecompositionPaidByProducer
    LeanQ.canonicalBoundary.qiRootChartRecordedAsScalarExtensionData
    LeanQ.canonicalBoundary.qiRootChartClassifiesOriginalQForm
    true true true true
    LeanQ.canonicalBoundary.leanNativeQOctonionNormAnisotropySourceWritten
    LeanQ.canonicalBoundary.leanNativeQOctonionNoZeroDivisorsSourceWritten
    LeanQ.canonicalBoundary.sameActionStructuralStabilizerPaidInLean
    LeanQ.canonicalBoundary.leanKernelProofAuthorityImportedIntoAgda
    TauCeti.canonicalBoundary.tauCetiAlbertStackLocated
    TauCeti.canonicalBoundary.sameObjectAlbertToCanonicalF4BridgeLocated
    Classification.canonicalBoundary.allConcreteExceptionalHypothesesOwned
    Classification.canonicalBoundary.classificationReducedToOneExternalTheoremPremise
    false true
    false false false false
