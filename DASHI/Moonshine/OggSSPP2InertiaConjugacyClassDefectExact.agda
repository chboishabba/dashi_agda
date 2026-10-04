module DASHI.Moonshine.OggSSPP2InertiaConjugacyClassDefectExact where

------------------------------------------------------------------------
-- p=2 INERTIA CONJUGACY-CLASS DEFECT INTERPRETATION
--
-- CLASSICAL TERMINOLOGY
--
-- In modular representation theory the p-defect group of a conjugacy class
-- represented by g is a Sylow p-subgroup of C_G(g).  Equivalently, if
--
--     |C_G(g)|_p = p^d,
--
-- then the conjugacy class has p-defect d.
--
-- DASHI CROSS-WELD
--
-- For the five unoriented binary-tetrahedral inertia sectors the already-owned
-- centralizer 2-adic depths
--
--     3, 3, 2, 1, 1
--
-- are therefore exactly their conjugacy-class 2-defects.
--
-- FIREWALL
--
-- Block/class defect theory does NOT in general identify class defect with the
-- composition length of an arbitrary localized DVR module.  That equality is
-- precisely one of the remaining problem-specific p=2 localization theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as Centralizer
import DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact as StackDepth
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution for the standard defect definition.
------------------------------------------------------------------------

ctBlocksDefectSource : Source.AttributedSource
ctBlocksDefectSource =
  Source.mkNoDOISource
    "Thomas Breuer and CTBlocks contributors"
    "CTBlocks: Character theoretic functions for p-blocks, Defect classes and defect groups"
    "GAP package documentation"
    ""
    "https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctblocks/doc/chap3_mj.html"
    Source.technicalStandardSource
    "standard computational representation-theory reference for the definition that p-defect groups of a conjugacy class are Sylow p-subgroups of element centralizers; used only to name the already-computed centralizer depths as class defects"
    Source.publicAttribution

classDefectSourceAtlas : Source.AttributedSourceAtlas
classDefectSourceAtlas =
  Source.mkSourceAtlas
    "p=2 inertia conjugacy-class defect terminology"
    "DASHI.Moonshine.OggSSPP2InertiaConjugacyClassDefectExact"
    (ctBlocksDefectSource ∷ [])
    "external source supplies the standard class-defect definition; binary-tetrahedral class data and all DASHI sector matching remain separately owned"

------------------------------------------------------------------------
-- 2. Exact class-defect function on the five sectors.
------------------------------------------------------------------------

conjugacyClassTwoDefect :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Nat
conjugacyClassTwoDefect =
  Centralizer.unorientedCentralizerTwoAdicDepth

identityClassDefectIsThree :
  conjugacyClassTwoDefect Inertia.identityInertiaOrbit ≡ 3
identityClassDefectIsThree = refl

centralMinusOneClassDefectIsThree :
  conjugacyClassTwoDefect Inertia.centralMinusOneInertiaOrbit ≡ 3
centralMinusOneClassDefectIsThree = refl

orderFourClassDefectIsTwo :
  conjugacyClassTwoDefect Inertia.orderFourInertiaOrbit ≡ 2
orderFourClassDefectIsTwo = refl

orderThreeClassDefectIsOne :
  conjugacyClassTwoDefect Inertia.orderThreePairInertiaOrbit ≡ 1
orderThreeClassDefectIsOne = refl

orderSixClassDefectIsOne :
  conjugacyClassTwoDefect Inertia.orderSixPairInertiaOrbit ≡ 1
orderSixClassDefectIsOne = refl

------------------------------------------------------------------------
-- 3. Existing preferred weight and stack denominator depth coincide with
--    the classical class-defect number.
------------------------------------------------------------------------

preferredP2WeightIsConjugacyClassDefect :
  (sector : Inertia.BinaryTetrahedralInversionOrbit) ->
  Preferred.weight Preferred.p2PreferredPresentation sector
  ≡
  conjugacyClassTwoDefect sector
preferredP2WeightIsConjugacyClassDefect =
  StackDepth.preferredP2WeightIsIsotropyDenominatorDepth

------------------------------------------------------------------------
-- 4. No generic class-defect -> composition-length promotion.
------------------------------------------------------------------------

data ClassDefectEqualsLocalizedDVRCompositionLengthGenerically : Set where
data BrauerMinMaxDeterminesDASHISectorLength : Set where
data DefectClassTerminologyProvesMonsterCorrection : Set where

classDefectDoesNotGenericallyEqualLocalizedLength :
  ClassDefectEqualsLocalizedDVRCompositionLengthGenerically -> ⊥
classDefectDoesNotGenericallyEqualLocalizedLength ()

brauerMinMaxDoesNotDetermineDASHISectorLength :
  BrauerMinMaxDeterminesDASHISectorLength -> ⊥
brauerMinMaxDoesNotDetermineDASHISectorLength ()

defectTerminologyDoesNotProveMonsterCorrection :
  DefectClassTerminologyProvesMonsterCorrection -> ⊥
defectTerminologyDoesNotProveMonsterCorrection ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2InertiaConjugacyClassDefectBoundary : Set where
  constructor p2-inertia-conjugacy-class-defect-boundary
  field
    classDefectDefinitionExternallySourced : Bool
    centralizerDepthVectorOwned : Bool
    preferredWeightsIdentifiedAsClassDefects : Bool
    defectVectorThreeThreeTwoOneOneExact : Bool
    genericDefectEqualsCompositionLengthClaimed : Bool
    monsterCorrectionMechanismClaimed : Bool
    attributionFirewallPreserved : Bool

canonicalP2InertiaConjugacyClassDefectBoundary :
  P2InertiaConjugacyClassDefectBoundary
canonicalP2InertiaConjugacyClassDefectBoundary =
  p2-inertia-conjugacy-class-defect-boundary
    true true true true false false true
