module DASHI.Moonshine.Monster3BAtlasD4FourESourceSubmoduleExact where

------------------------------------------------------------------------
-- SOURCE: original ATLAS/AtlasRep 2.Suz:2 GF(3) matrix generators.
-- Prior repo #1098 source D4 words, invariant 12D alternating form,
-- and six-pair extraspecial Heisenberg models are the original owners.
-- Script: scripts/monster3b_atlas_d4_fourE_h4_source_submodule.py
--
-- Classical representation theory (Serre): D4 in characteristic 3 has
-- irreducibles A1,A2,B1,B2,E.  The source 12D module is SIX E copies.
-- Its source-derived nondegenerate D4-submodule of 8D is FOUR E copies;
-- the symplectic orthogonal complement is TWO E copies.
-- A specific source 12x8 intertwiner and H4 group-lift checks are Python
-- finite-source calculations, not kernel proof terms in this module.
-- The original geometric 3x3 JFine D4 and the modified A2 model are
-- DISTINCT reps.  Neither is identified with the source's 4E module.
-- Selected Monster diagonal H/D_i, faithful 78, Hom_E(H,W), physical
-- Monster action and Agda kernel compilation remain UNPAID.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Irrep
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as D4

sourceTwelveIrrepCount : Irrep.D4IrrepKind → Nat
sourceTwelveIrrepCount Irrep.A1 = 0
sourceTwelveIrrepCount Irrep.A2 = 0
sourceTwelveIrrepCount Irrep.B1 = 0
sourceTwelveIrrepCount Irrep.B2 = 0
sourceTwelveIrrepCount Irrep.E2 = 6

sourceEightIrrepCount : Irrep.D4IrrepKind → Nat
sourceEightIrrepCount Irrep.A1 = 0
sourceEightIrrepCount Irrep.A2 = 0
sourceEightIrrepCount Irrep.B1 = 0
sourceEightIrrepCount Irrep.B2 = 0
sourceEightIrrepCount Irrep.E2 = 4

sourceComplementIrrepCount : Irrep.D4IrrepKind → Nat
sourceComplementIrrepCount Irrep.A1 = 0
sourceComplementIrrepCount Irrep.A2 = 0
sourceComplementIrrepCount Irrep.B1 = 0
sourceComplementIrrepCount Irrep.B2 = 0
sourceComplementIrrepCount Irrep.E2 = 2

twelveIsSixE : sourceTwelveIrrepCount Irrep.E2
  * Irrep.irrepDimension Irrep.E2 ≡ 12
twelveIsSixE = refl

eightIsFourE : sourceEightIrrepCount Irrep.E2
  * Irrep.irrepDimension Irrep.E2 ≡ 8
eightIsFourE = refl

fourIsTwoE : sourceComplementIrrepCount Irrep.E2
  * Irrep.irrepDimension Irrep.E2 ≡ 4
fourIsTwoE = refl

sourceDecompositionDimension : 8 + 4 ≡ 12
sourceDecompositionDimension = refl

sourceHalfTurnTrace : D4.scaleInt 4
  (D4.d4Character Irrep.E2 D4.centralHalfTurnClass)
  ≡ -[1+ 7 ]
sourceHalfTurnTrace = refl

sourceQuarterTrace : D4.scaleInt 4
  (D4.d4Character Irrep.E2 D4.quarterTurnPairClass)
  ≡ + 0
sourceQuarterTrace = refl

sourceAxisMirrorTrace : D4.scaleInt 4
  (D4.d4Character Irrep.E2 D4.axisHalfTurnPairClass)
  ≡ + 0
sourceAxisMirrorTrace = refl

-- Earlier IIT model A1+A2+2B1+2B2+E has half-turn trace
-- 1+1+2+2-2=4, versus this source 4E's -8.
-- Hence their D4 representations cannot be identified by relabelling.
oldOrientedEightHalfTurnCharacter : ℤ
oldOrientedEightHalfTurnCharacter =
  D4.d4Character Irrep.A1 D4.centralHalfTurnClass
  +ℤ D4.d4Character Irrep.A2 D4.centralHalfTurnClass
  +ℤ D4.scaleInt 2 (D4.d4Character Irrep.B1 D4.centralHalfTurnClass)
  +ℤ D4.scaleInt 2 (D4.d4Character Irrep.B2 D4.centralHalfTurnClass)
  +ℤ D4.d4Character Irrep.E2 D4.centralHalfTurnClass

oldOrientedEightHalfTurnTrace : oldOrientedEightHalfTurnCharacter ≡ + 4
oldOrientedEightHalfTurnTrace = refl

record SourceFourEAdmission : Set where
  constructor source-fourE-admission
  field
    originalAtlasMatrixSourceReused : Bool
    existingATLASSourceD4WordsReused : Bool
    sourceSubmoduleDimension : Nat
    sourceComplementDimension : Nat
    sourceD4FourECharacterWritten : Bool
    actualSymplecticEightEmbeddingLocallyExecuted : Bool
    quadraticCorrectedH4GeneratorChecksLocallyExecuted : Bool
    geometricNineCellD4Preserved : Bool
    modifiedA2D4Identified : Bool
    actualMonsterSelectedDiagonalQuotientPaid : Bool
    selected6SuzCharacter78Paid : Bool
    actualHomIntertwinerPaid : Bool
    thisModuleAgdaKernelChecked : Bool

currentAdmission : SourceFourEAdmission
currentAdmission = source-fourE-admission
  true true 8 4 true true true false false false false false false
