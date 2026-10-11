module DASHI.Mathematics.Algebra.RationalAlbertF4CurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT RATIONAL ALBERT / F4 MAX-CUT
--
-- The local exceptional-algebra discovery programme is now paid/source-written
-- or exact-executable through:
--
-- * exact rational octonions and the actual H_3(O_Q) Jordan algebra;
-- * identity, trace, cubic determinant/norm, Jordan product and Jordan identity;
-- * explicit same-carrier automorphisms (coordinate S3, signed-basis octonion
--   lifts, selected Moufang triality) and typed linear Jordan automorphisms;
-- * generic arbitrary-element inner-derivation law;
-- * exact inner-derivation span dimension 52;
-- * exact triality basis 52 = 28 + 8_v + 8_s + 8_c and bracket pattern;
-- * exact four-dimensional Cartan with vector / chiral half-spin roles;
-- * exact symbolic Q(i) projectors giving zero-weight dimension 4 and 48
--   one-dimensional nonzero root spaces = 24 + 8 + 8 + 8;
-- * companion Lean standard F4 root/Coxeter datum and Weyl order 1152.
--
-- Consequently the remaining F4 theorem is not a local root-space search.  It
-- is the general characteristic-zero classification/recognition theorem that
-- identifies this concrete rational derivation Lie algebra and Aut(J) with the
-- appropriate rational form of type F4 (and the cubic linear symmetry group
-- with type E6).  Classical sources pay this theorem; the repo does not yet
-- formalize the general classification machinery itself.
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
    floatingRootExtractionSuperseded : Bool
    independentF4Root48LeanReceiptPaid : Bool
    independentF4Rank4LeanReceiptPaid : Bool
    independentF4Weyl1152LeanReceiptPaid : Bool
    allConcreteClassificationHypothesesOwned : Bool
    classificationReducedToSingleExternalPremise : Bool
    generalExceptionalClassificationFormalizedInRepo : Bool
    sameLieAlgebraF4ClassificationPaid : Bool
    fullF4AutomorphismGroupPaid : Bool
open CurrentF4Boundary public

currentF4Boundary : CurrentF4Boundary
currentF4Boundary =
  current-f4-boundary
    true true true true
    true true true
    ExactRoots.canonicalBoundary.exactQIRootSpaceDecompositionPaidByProducer
    true true true true
    Classification.canonicalBoundary.allConcreteExceptionalHypothesesOwned
    Classification.canonicalBoundary.classificationReducedToOneExternalTheoremPremise
    false false false
