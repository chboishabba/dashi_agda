module DASHI.Interop.WorldEigenResidualStratification where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Cognition.PNF.WikidataTypePressureMiniWorldExact as MiniWorld
import DASHI.Interop.SensibLawResidualLattice as Residual
import Ontology.Hecke.PNFResidualBridge as Hecke

------------------------------------------------------------------------
-- WORLD -> MACRO EIGEN -> SUB-EIGEN -> FIBRE
--
-- The levels have different authority.
--
-- * world: external or local typed world constraints
-- * macro eigen: coarse domain/orbit relation only
-- * sub-eigen: typed signature meet and residual classification
-- * fibre: carrier-local mutation law and defect classification
--
-- A macro spectral relation is not itself a PNF residual theorem.
------------------------------------------------------------------------

data WorldEigenScale : Set where
  worldScale : WorldEigenScale
  macroEigenScale : WorldEigenScale
  subEigenScale : WorldEigenScale
  fibreScale : WorldEigenScale

scaleDepth : WorldEigenScale → Nat
scaleDepth worldScale = 0
scaleDepth macroEigenScale = 1
scaleDepth subEigenScale = 2
scaleDepth fibreScale = 3

worldDepthIsZero : scaleDepth worldScale ≡ 0
worldDepthIsZero = refl

macroDepthIsOne : scaleDepth macroEigenScale ≡ 1
macroDepthIsOne = refl

subEigenDepthIsTwo : scaleDepth subEigenScale ≡ 2
subEigenDepthIsTwo = refl

fibreDepthIsThree : scaleDepth fibreScale ≡ 3
fibreDepthIsThree = refl

data MacroOrbitRelation : Set where
  orthogonalDomains : MacroOrbitRelation
  sharedQuotientOrbit : MacroOrbitRelation

data MacroRelationCreatesResidual : MacroOrbitRelation → Set where

macroOrthogonalityDoesNotCreateResidual :
  MacroRelationCreatesResidual orthogonalDomains → ⊥
macroOrthogonalityDoesNotCreateResidual ()

sharedMacroOrbitDoesNotCreateResidual :
  MacroRelationCreatesResidual sharedQuotientOrbit → ⊥
sharedMacroOrbitDoesNotCreateResidual ()

------------------------------------------------------------------------
-- noTypedMeet belongs to the sub-eigen typed-signature comparison.
------------------------------------------------------------------------

data SubEigenMeet : Set where
  exactMeet : SubEigenMeet
  partialMeet : SubEigenMeet
  noTypedMeetMeet : SubEigenMeet

subEigenResidual : SubEigenMeet → Residual.ResidualLevel
subEigenResidual exactMeet = Residual.exact
subEigenResidual partialMeet = Residual.partial
subEigenResidual noTypedMeetMeet = Residual.noTypedMeet

exactMeetResidualIsExact :
  subEigenResidual exactMeet ≡ Residual.exact
exactMeetResidualIsExact = refl

partialMeetResidualIsPartial :
  subEigenResidual partialMeet ≡ Residual.partial
partialMeetResidualIsPartial = refl

noTypedMeetIsSubEigenResidual :
  subEigenResidual noTypedMeetMeet ≡ Residual.noTypedMeet
noTypedMeetIsSubEigenResidual = refl

noTypedMeetSubEigenSeverityIsThree :
  Residual.residualSeverity (subEigenResidual noTypedMeetMeet) ≡ 3
noTypedMeetSubEigenSeverityIsThree = refl

------------------------------------------------------------------------
-- Lawful zoom-out: a bounded Wikidata role mismatch may underspecify.
------------------------------------------------------------------------

wikidataSeriesEditionMismatchZoomsOutLawfully :
  MiniWorld.repairForMismatch MiniWorld.seriesDeclaredEditionObserved
  ≡
  Repair.underspecifyType
wikidataSeriesEditionMismatchZoomsOutLawfully =
  MiniWorld.seriesEditionMismatchUnderspecifies

wikidataEditionSeriesMismatchZoomsOutLawfully :
  MiniWorld.repairForMismatch MiniWorld.editionDeclaredSeriesObserved
  ≡
  Repair.underspecifyType
wikidataEditionSeriesMismatchZoomsOutLawfully =
  MiniWorld.editionSeriesMismatchUnderspecifies

------------------------------------------------------------------------
-- World invalidation cannot be repaired by quotient coarsening.
--
-- If two world states are forced into one quotient class while a required
-- structural signature still separates them, then no coarse-only signature
-- observer can reproduce that required signature. This reuses the canonical
-- projection-collision theorem instead of inventing a second quotient law.
------------------------------------------------------------------------

record WorldInvalidationWitness
    {World Quotient Signature : Set}
    (project : World → Quotient)
    (signature : World → Signature) : Set where
  constructor worldInvalidationWitness
  field
    leftWorld rightWorld : World
    forcedSameQuotient :
      project leftWorld ≡ project rightWorld
    axiomaticSignatureSeparation :
      signature leftWorld ≡ signature rightWorld → ⊥

open WorldInvalidationWitness public

worldInvalidationProjectionCollision :
  ∀ {World Quotient Signature : Set}
    {project : World → Quotient}
    {signature : World → Signature} →
  WorldInvalidationWitness project signature →
  Coarse.ProjectionCollision project signature
worldInvalidationProjectionCollision witness =
  Coarse.projectionCollision
    (leftWorld witness)
    (rightWorld witness)
    (forcedSameQuotient witness)
    (axiomaticSignatureSeparation witness)

worldInvalidationCannotBeAccommodatedByZoomOut :
  ∀ {World Quotient Signature : Set}
    {project : World → Quotient}
    {signature : World → Signature} →
  WorldInvalidationWitness project signature →
  (coarseSignature : Quotient → Signature) →
  ((state : World) →
    signature state ≡ coarseSignature (project state)) →
  ⊥
worldInvalidationCannotBeAccommodatedByZoomOut witness =
  Coarse.consumerCannotFactorThroughProjection
    (worldInvalidationProjectionCollision witness)

forcedCollapsedQuotientIsInconsistent :
  ∀ {World Quotient Signature : Set}
    {project : World → Quotient}
    {signature : World → Signature} →
  WorldInvalidationWitness project signature →
  (coarseSignature : Quotient → Signature) →
  ((state : World) →
    signature state ≡ coarseSignature (project state)) →
  ⊥
forcedCollapsedQuotientIsInconsistent =
  worldInvalidationCannotBeAccommodatedByZoomOut

------------------------------------------------------------------------
-- Fibre law: illegalDefect cannot be repaired by zoom-out.
------------------------------------------------------------------------

illegalDefectResidualIsContradiction :
  Hecke.defectResidual Hecke.illegalDefect ≡ Residual.contradiction
illegalDefectResidualIsContradiction =
  Hecke.defectResidual-illegal

illegalDefectPressureIsCritical :
  Residual.residualToPressure
    (Hecke.defectResidual Hecke.illegalDefect)
  ≡
  Hecke.critical
illegalDefectPressureIsCritical =
  Hecke.illegalDefect-critical

illegalDefectCannotBecomePartial :
  Hecke.defectResidual Hecke.illegalDefect ≡ Residual.partial →
  ⊥
illegalDefectCannotBecomePartial ()

illegalDefectCannotBecomeNoTypedMeet :
  Hecke.defectResidual Hecke.illegalDefect ≡ Residual.noTypedMeet →
  ⊥
illegalDefectCannotBecomeNoTypedMeet ()

illegalDefectCannotBecomeExact :
  Hecke.defectResidual Hecke.illegalDefect ≡ Residual.exact →
  ⊥
illegalDefectCannotBecomeExact ()
