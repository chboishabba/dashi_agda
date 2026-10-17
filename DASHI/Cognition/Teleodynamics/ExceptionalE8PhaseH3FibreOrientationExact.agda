module DASHI.Cognition.Teleodynamics.ExceptionalE8PhaseH3FibreOrientationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6
import DASHI.Cognition.Teleodynamics.ExceptionalE8Order3ZetaPhaseExact as Phase

------------------------------------------------------------------------
-- THE 120 = 40 x 3 H3 FIBRE AND THE E8 C3 PHASE
--
-- Existing hyperfabric computation gives 40 A2^3 subsystem classes and exactly
-- three distinguished-factor H3 patches over each class.  Local exact
-- enumeration shows that the stabilizer of one null/A2^3 class acts on those
-- three H3 patches as the full S3, not as a canonically oriented C3.
--
-- Therefore the E8 phase {I,w,w^2} is COMPATIBLE with a cyclic orientation of
-- the three H3 choices, and the normalizer involution gives the expected
-- inversion, but the E6 quotient carrier by itself does not choose that
-- orientation.  An oriented lift is extra structure and is kept explicit.
------------------------------------------------------------------------

record H3ThreeFibreComputationReceipt : Set where
  constructor h3-three-fibre-computation-receipt
  field
    grade : E6.EvidenceGrade
    baseClassCount : Nat
    h3PatchCount : Nat
    patchesPerBaseClass : Nat
    chosenBaseStabilizerOrder : Nat
    inducedThreePatchPermutationImageOrder : Nat
    inducedImageIsFullS3 : Bool
    canonicalC3OrientationAlreadyDeterminedByE6Carrier : Bool
    localPythonReproduced : Bool
    provenance : String
open H3ThreeFibreComputationReceipt public

canonicalH3ThreeFibreComputationReceipt : H3ThreeFibreComputationReceipt
canonicalH3ThreeFibreComputationReceipt =
  h3-three-fibre-computation-receipt
    E6.localFiniteComputation
    40 120 3 1296 6 true false true
    "local exact E6 quotient enumeration: each null/A2^3 class has three H3 patches; its stabilizer induces all six permutations of the fibre, so the unoriented fibre is S3 rather than a canonical C3"

-- Extra datum required to identify one oriented H3 three-fibre with the E8
-- phase carrier.  Once supplied, the repo-native C3 multiplication and
-- conjugation laws from ExceptionalE8Order3ZetaPhaseExact are available.
record OrientedH3PhaseLift : Set₁ where
  field
    BaseClass : Set
    H3Patch : BaseClass → Set
    phaseCoordinate : (b : BaseClass) → H3Patch b → Phase.E8Order3Phase
    phaseInverse : (b : BaseClass) → Phase.E8Order3Phase → H3Patch b
    provenance : String
open OrientedH3PhaseLift public

record H3PhaseOrientationBoundary : Set where
  constructor h3-phase-orientation-boundary
  field
    fortyBaseClassesPaid : Bool
    oneTwentyPatchesPaid : Bool
    threePatchesPerClassPaid : Bool
    fibreStabilizerImageS3Paid : Bool
    e8C3PhaseCarrierPaid : Bool
    normalizerConjugationPaid : Bool
    e6CarrierAloneChoosesCyclicOrientation : Bool
    cardinalityThreePromotedToSamePhase : Bool

canonicalH3PhaseOrientationBoundary : H3PhaseOrientationBoundary
canonicalH3PhaseOrientationBoundary =
  h3-phase-orientation-boundary true true true true true true false false
