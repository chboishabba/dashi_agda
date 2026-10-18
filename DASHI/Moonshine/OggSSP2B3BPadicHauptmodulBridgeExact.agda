module DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact where

------------------------------------------------------------------------
-- CLASS-SPECIFIC 2B / 3B p-ADIC HAUPTMODUL BRIDGE
--
-- EXTERNAL INPUT
--
-- Standard monstrous moonshine identifications:
--
--   T_2B  is the normalized Hauptmodul for Gamma0(2),
--   T_3B  is the normalized Hauptmodul for Gamma0(3).
--
-- Chen--Marks--Tyler prove p-adic annihilation for the level-2 Hauptmodul at
-- p=2 and the level-3 Hauptmodul at p=3 (their Table 4.1 / Theorem 4.1).
--
-- Therefore the SAME Monster conjugacy classes selected by the independent
-- local-centralizer target have class-specific Hauptmoduln with genuine
-- small-prime p-adic analytic behavior.
--
-- UNPAID STEP
--
-- p-adic annihilation is an asymptotic U_p statement.  It does not by itself
-- define a finite integer "decay depth" equal to the local-centralizer defects
-- 10 and 2.  A valid bridge must derive such a finite valuation/defect from the
-- q-expansion / U_p / bad-level structure without inserting the target value.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

borcherdsICM : Source.AttributedSource
borcherdsICM =
  Source.mkNoDOISource
    "Richard E. Borcherds"
    "Monstrous moonshine"
    "Documenta Mathematica, Extra Volume ICM 1998"
    "1998"
    "https://ems.press/content/book-chapter-files/27123"
    Source.academicArticleSource
    "standard moonshine source explicitly exhibiting T_2B as the Hauptmodul for Gamma0(2); source for the class/modular-group identification only"
    Source.publicAttribution

class3BHauptmodulSource : Source.AttributedSource
class3BHauptmodulSource =
  Source.mkNoDOISource
    "standard monstrous moonshine Hauptmodul tables"
    "McKay--Thompson series for class 3B"
    "standard moonshine tables / eta-quotient presentation"
    ""
    "https://oeis.org/A198955"
    Source.institutionalSource
    "records T_3B = 12 + (eta(tau)/eta(3tau))^12, the normalized Hauptmodul for Gamma0(3); used only for the class/modular-group/q-expansion identification"
    Source.publicAttribution

chenMarksTyler : Source.AttributedSource
chenMarksTyler =
  Source.mkNoDOISource
    "Ryan C. Chen, Samuel Marks, and Matthew Tyler"
    "p-adic Properties of Hauptmoduln with Applications to Moonshine"
    "SIGMA 15 (2019), arXiv:1809.02913"
    "2019"
    "https://arxiv.org/abs/1809.02913"
    Source.academicArticleSource
    "Theorem 4.1/Table 4.1 source for p-adic annihilation of the level-2 Hauptmodul at p=2 and level-3 Hauptmodul at p=3; does not state the finite 10/2 defect extraction theorem"
    Source.publicAttribution

classSpecificPadicAtlas : Source.AttributedSourceAtlas
classSpecificPadicAtlas =
  Source.mkSourceAtlas
    "2B/3B class-specific p-adic Hauptmodul bridge"
    "DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact"
    (borcherdsICM ∷ class3BHauptmodulSource ∷ chenMarksTyler ∷ [])
    "external sources own class-specific Hauptmodul identities and p-adic annihilation; DASHI owns only the proposed finite defect-extraction interface"

------------------------------------------------------------------------
-- 1. Source-backed class-specific analytic flags.
------------------------------------------------------------------------

data SmallPrimeMonsterClass : Set where
  class2B class3B : SmallPrimeMonsterClass

classPrime : SmallPrimeMonsterClass -> Nat
classPrime class2B = 2
classPrime class3B = 3

hauptmodulLevel : SmallPrimeMonsterClass -> Nat
hauptmodulLevel class2B = 2
hauptmodulLevel class3B = 3

padicallyAnnihilatedAtClassPrime :
  SmallPrimeMonsterClass ->
  Bool
padicallyAnnihilatedAtClassPrime class2B = true
padicallyAnnihilatedAtClassPrime class3B = true

classSpecificLocalDefect :
  SmallPrimeMonsterClass ->
  Nat
classSpecificLocalDefect class2B =
  Local.p2LocalCentralizerResidual
classSpecificLocalDefect class3B =
  Local.p3LocalCentralizerResidual

class2BLocalDefectIsTen :
  classSpecificLocalDefect class2B ≡ 10
class2BLocalDefectIsTen = refl

class3BLocalDefectIsTwo :
  classSpecificLocalDefect class3B ≡ 2
class3BLocalDefectIsTwo = refl

------------------------------------------------------------------------
-- 2. Missing finite defect extraction from p-adic Hauptmodul behavior.
------------------------------------------------------------------------

record PadicHauptmodulDefectExtractionAuthority : Set₁ where
  field
    AnalyticState : Set

    state2B :
      AnalyticState

    state3B :
      AnalyticState

    finiteDefect :
      SmallPrimeMonsterClass ->
      AnalyticState ->
      Nat

    stateComesFromClassSpecificHauptmodul :
      Bool
    stateComesFromClassSpecificHauptmodulIsTrue :
      stateComesFromClassSpecificHauptmodul ≡ true

    usesUpOperatorOrEquivalentPadicDynamics :
      Bool
    usesUpOperatorOrEquivalentPadicDynamicsIsTrue :
      usesUpOperatorOrEquivalentPadicDynamics ≡ true

    usesBadLevelLocalGeometry :
      Bool
    usesBadLevelLocalGeometryIsTrue :
      usesBadLevelLocalGeometry ≡ true

    class2BDefectIsLocalCentralizerDefect :
      finiteDefect class2B state2B
      ≡ classSpecificLocalDefect class2B

    class3BDefectIsLocalCentralizerDefect :
      finiteDefect class3B state3B
      ≡ classSpecificLocalDefect class3B

    proofDoesNotInsertTargetDefect :
      Bool
    proofDoesNotInsertTargetDefectIsTrue :
      proofDoesNotInsertTargetDefect ≡ true

open PadicHauptmodulDefectExtractionAuthority public

------------------------------------------------------------------------
-- 3. Scope firewalls.
------------------------------------------------------------------------

data PadicAnnihilationAutomaticallyDefinesFiniteDefect : Set where
data LevelEqualsPrimeThereforeDefectEqualsPrimeData : Set where
data ClassSpecificPadicBridgeAlreadyInhabited : Set where

padicAnnihilationDoesNotAutomaticallyDefineFiniteDefect :
  PadicAnnihilationAutomaticallyDefinesFiniteDefect -> ⊥
padicAnnihilationDoesNotAutomaticallyDefineFiniteDefect ()

levelPrimeIdentityDoesNotCreateDefect :
  LevelEqualsPrimeThereforeDefectEqualsPrimeData -> ⊥
levelPrimeIdentityDoesNotCreateDefect ()

classSpecificPadicBridgeStillOpen :
  ClassSpecificPadicBridgeAlreadyInhabited -> ⊥
classSpecificPadicBridgeStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record ClassSpecificPadicHauptmodulBridgeBoundary : Set where
  constructor class-specific-padic-hauptmodul-bridge-boundary
  field
    class2BGamma02IdentificationSourced : Bool
    class3BGamma03IdentificationSourced : Bool
    class2BTwoAdicAnnihilationSourced : Bool
    class3BThreeAdicAnnihilationSourced : Bool
    localCentralizerDefectsIndependent : Bool
    finiteDefectExtractionAuthoritySpecified : Bool
    finiteDefectExtractionAuthorityInhabited : Bool
    pAdicAnnihilationPromotedToTenTwoWithoutProof : Bool
    attributionFirewallPreserved : Bool

canonicalClassSpecificPadicHauptmodulBridgeBoundary :
  ClassSpecificPadicHauptmodulBridgeBoundary
canonicalClassSpecificPadicHauptmodulBridgeBoundary =
  class-specific-padic-hauptmodul-bridge-boundary
    true true true true true true false false true
