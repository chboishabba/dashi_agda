module DASHI.Moonshine.JInvariant369ConsolidatedNextStageExact where

------------------------------------------------------------------------
-- CONSOLIDATED 369/J NEXT-STAGE FORMULATION
--
-- This owner composes the now-paid theorem surfaces:
--
--   base modular/J surface
--          |
--          v
--   C6 phase x C27 principal-level x SignedMultiplicity
--          |
--          +--> C9 -> C3 principal-level
--          |
--          +--> coarse SSP C3  ~=_equiv  level C3
--          |
--          +--> signed SSP stalk anchored into the Stage-12 / 144 relation site
--
-- while retaining three distinct residuals:
--
--   * level lift does not factor through the base J surface;
--   * signed magnitude does not factor through coarse SSP sign/C3;
--   * the coarse C3 equivariance does not canonically lift to a
--     magnitude-preserving action on full SignedMultiplicity.
--
-- The Stage-12 relation site remains a finite Grothendieck site.  This module
-- does NOT identify it with the analytic modular-curve site.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Base369 as Base
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact as SSPDihedral
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Canonical
import DASHI.Moonshine.JInvariant369SSPLevelDihedralIntertwinerExact as SSPLevel
import DASHI.Moonshine.JInvariant369JointFibredObserverExact as Joint
import DASHI.Moonshine.JInvariant369JointFibreBifiltrationExact as JointBif
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Stage12
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- 1. A consolidated state: one joint modular fibre, one signed relation-field
--    section, and one proof that the chosen relation cell carries exactly the
--    joint state's signed SSP coordinate.
------------------------------------------------------------------------

record Consolidated369State
    (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor consolidated369State
  field
    jointLift :
      Joint.Joint369Lift R

    signedRelationField :
      Stage12.SignedRelationField

    anchorCell :
      Stage12.StageRelation144

    anchorAgreesWithJointSigned :
      signedRelationField anchorCell
      ≡
      Joint.signedSSPCoordinate
        (Joint.fibre jointLift)

open Consolidated369State public

jointSignedMultiplicity :
  ∀ {R} →
  Consolidated369State R →
  Signed.SignedMultiplicity
jointSignedMultiplicity state =
  Joint.signedSSPCoordinate
    (Joint.fibre (jointLift state))

principalLevel27 :
  ∀ {R} →
  Consolidated369State R →
  Level.level27CuspFibre
principalLevel27 state =
  Joint.level27Coordinate
    (Joint.fibre (jointLift state))

principalLevel3 :
  ∀ {R} →
  Consolidated369State R →
  Level.level3CuspFibre
principalLevel3 state =
  Joint.jointLevel3
    (Joint.fibre (jointLift state))

signedCoarseLevel3 :
  ∀ {R} →
  Consolidated369State R →
  Level.level3CuspFibre
signedCoarseLevel3 state =
  SSPLevel.signedMultiplicityLevel3Observer
    (jointSignedMultiplicity state)

------------------------------------------------------------------------
-- 2. Optional coherence is explicit data, not a definitional identification.
------------------------------------------------------------------------

SignedLevel3Coherent :
  ∀ {R} →
  Consolidated369State R →
  Set
SignedLevel3Coherent state =
  signedCoarseLevel3 state
  ≡
  principalLevel3 state

record CoherentConsolidated369State
    (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor coherent-consolidated369-state
  field
    consolidated :
      Consolidated369State R
    signedLevel3Coherence :
      SignedLevel3Coherent consolidated

open CoherentConsolidated369State public

------------------------------------------------------------------------
-- 3. Modular translation preserves base, phase, signed SSP and relation field;
--    it changes only the principal-level coordinate.
------------------------------------------------------------------------

translateConsolidated :
  ∀ {R} →
  Consolidated369State R →
  Consolidated369State R
translateConsolidated state =
  consolidated369State
    (Joint.translateJointLift (jointLift state))
    (signedRelationField state)
    (anchorCell state)
    (anchorAgreesWithJointSigned state)

------------------------------------------------------------------------
-- 4. Fibre-only reflection negates the signed relation stalk pointwise.
--
-- Analytic reflection of the base point remains a separate analytic theorem.
------------------------------------------------------------------------

negateSignedField :
  Stage12.SignedRelationField →
  Stage12.SignedRelationField
negateSignedField field cell =
  Signed.negateMultiplicity (field cell)

reflectJointLiftFibreOnly :
  ∀ {R} →
  Joint.Joint369Lift R →
  Joint.Joint369Lift R
reflectJointLiftFibreOnly state =
  Joint.joint369Lift
    (Joint.basePoint state)
    (Joint.reflectJoint (Joint.fibre state))

reflectConsolidatedFibreOnly :
  ∀ {R} →
  Consolidated369State R →
  Consolidated369State R
reflectConsolidatedFibreOnly state =
  consolidated369State
    (reflectJointLiftFibreOnly (jointLift state))
    (negateSignedField (signedRelationField state))
    (anchorCell state)
    (cong Signed.negateMultiplicity
      (anchorAgreesWithJointSigned state))

------------------------------------------------------------------------
-- 5. The Stage-12 signed stalk is really the local restriction of the
--    consolidated state at its declared anchor.
------------------------------------------------------------------------

anchorRestriction :
  ∀ {R} →
  Consolidated369State R →
  Signed.SignedMultiplicity
anchorRestriction state =
  signedRelationField state (anchorCell state)

anchorRestrictionIsJointSigned :
  ∀ {R}
    (state : Consolidated369State R) →
  anchorRestriction state
  ≡
  jointSignedMultiplicity state
anchorRestrictionIsJointSigned =
  anchorAgreesWithJointSigned

anchorCoarseSign :
  ∀ {R} →
  Consolidated369State R →
  Base.TriTruth
anchorCoarseSign state =
  Stage12.signedMultiplicityToTriTruth
    (anchorRestriction state)

anchorMagnitude :
  ∀ {R} →
  Consolidated369State R →
  Nat
anchorMagnitude state =
  Stage12.signedMagnitudeConsumer
    (anchorCell state , anchorRestriction state)

------------------------------------------------------------------------
-- 6. Coarse base surface: base point + phase6 + coarse signed anchor.
--
-- Translation is invisible to this surface, but changes the level-27
-- consumer.  This is the consolidated form of "j/base forgets the lift".
------------------------------------------------------------------------

record ConsolidatedBaseSurface
    (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor consolidated-base-surface
  field
    basePoint :
      Klein.Point (Render.klein R)
    phase6 :
      Base.HexTruth
    anchorCell :
      Stage12.StageRelation144
    anchorSign :
      Base.TriTruth

open ConsolidatedBaseSurface public

consolidatedBaseObserver :
  ∀ {R} →
  Consolidated369State R →
  ConsolidatedBaseSurface R
consolidatedBaseObserver state =
  consolidated-base-surface
    (Joint.basePoint (jointLift state))
    (Joint.phase6Coordinate (Joint.fibre (jointLift state)))
    (anchorCell state)
    (anchorCoarseSign state)

translationInvisibleToConsolidatedBase :
  ∀ {R}
    (state : Consolidated369State R) →
  consolidatedBaseObserver (translateConsolidated state)
  ≡
  consolidatedBaseObserver state
translationInvisibleToConsolidatedBase state = refl

separationEmptyElim :
  Canonical.Separation.Empty → ⊥
separationEmptyElim ()

level27ChangesUnderTranslation :
  (level : Level.level27CuspFibre) →
  Level.translateTriadic Canonical.Q.three level
  ≡ level →
  ⊥
level27ChangesUnderTranslation level fixed =
  separationEmptyElim
    (Canonical.Separation.level27TranslationNoFixedPoint level fixed)

consolidatedLevelNonDescent :
  ∀ {R}
    (state : Consolidated369State R) →
  Descent.ConsumerNonDescentWitness
    consolidatedBaseObserver
    principalLevel27
consolidatedLevelNonDescent state =
  Descent.consumerNonDescentWitness
    state
    (translateConsolidated state)
    (translationInvisibleToConsolidatedBase state)
    (λ same →
      level27ChangesUnderTranslation
        (principalLevel27 state)
        same)

consolidatedLevelCannotFactorThroughBase :
  ∀ {R}
    (state : Consolidated369State R) →
  Descent.FactorsThrough
    consolidatedBaseObserver
    principalLevel27 →
  ⊥
consolidatedLevelCannotFactorThroughBase state =
  Descent.nonDescentWitnessBlocksFactorization
    (consolidatedLevelNonDescent state)

------------------------------------------------------------------------
-- 7. A richer surface may retain level-27 and still lose signed magnitude.
------------------------------------------------------------------------

record ConsolidatedAnchorSurface
    (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor consolidated-anchor-surface
  field
    basePoint :
      Klein.Point (Render.klein R)
    phase6 :
      Base.HexTruth
    level27 :
      Level.level27CuspFibre
    anchorCell :
      Stage12.StageRelation144
    anchorSign :
      Base.TriTruth

open ConsolidatedAnchorSurface public

consolidatedAnchorObserver :
  ∀ {R} →
  Consolidated369State R →
  ConsolidatedAnchorSurface R
consolidatedAnchorObserver state =
  consolidated-anchor-surface
    (Joint.basePoint (jointLift state))
    (Joint.phase6Coordinate (Joint.fibre (jointLift state)))
    (principalLevel27 state)
    (anchorCell state)
    (anchorCoarseSign state)

constantSignedField :
  Signed.SignedMultiplicity →
  Stage12.SignedRelationField
constantSignedField multiplicity cell = multiplicity

positiveOneState :
  ∀ {R} →
  Klein.Point (Render.klein R) →
  Base.HexTruth →
  Level.level27CuspFibre →
  Stage12.StageRelation144 →
  Consolidated369State R
positiveOneState z phase level cell =
  consolidated369State
    (Joint.joint369Lift z
      (Joint.joint369FiniteFibre
        phase
        level
        (Signed.positiveMultiplicity 1)))
    (constantSignedField (Signed.positiveMultiplicity 1))
    cell
    refl

positiveTwoState :
  ∀ {R} →
  Klein.Point (Render.klein R) →
  Base.HexTruth →
  Level.level27CuspFibre →
  Stage12.StageRelation144 →
  Consolidated369State R
positiveTwoState z phase level cell =
  consolidated369State
    (Joint.joint369Lift z
      (Joint.joint369FiniteFibre
        phase
        level
        (Signed.positiveMultiplicity 2)))
    (constantSignedField (Signed.positiveMultiplicity 2))
    cell
    refl

positiveOneTwoSameAnchorSurface :
  ∀ {R}
    (z : Klein.Point (Render.klein R))
    (phase : Base.HexTruth)
    (level : Level.level27CuspFibre)
    (cell : Stage12.StageRelation144) →
  consolidatedAnchorObserver
    (positiveOneState z phase level cell)
  ≡
  consolidatedAnchorObserver
    (positiveTwoState z phase level cell)
positiveOneTwoSameAnchorSurface z phase level cell = refl

positiveOneTwoDifferentAnchorMagnitude :
  ∀ {R}
    (z : Klein.Point (Render.klein R))
    (phase : Base.HexTruth)
    (level : Level.level27CuspFibre)
    (cell : Stage12.StageRelation144) →
  anchorMagnitude (positiveOneState z phase level cell)
  ≡
  anchorMagnitude (positiveTwoState z phase level cell) →
  ⊥
positiveOneTwoDifferentAnchorMagnitude z phase level cell ()

consolidatedMagnitudeNonDescent :
  ∀ {R}
    (z : Klein.Point (Render.klein R))
    (phase : Base.HexTruth)
    (level : Level.level27CuspFibre)
    (cell : Stage12.StageRelation144) →
  Descent.ConsumerNonDescentWitness
    consolidatedAnchorObserver
    anchorMagnitude
consolidatedMagnitudeNonDescent z phase level cell =
  Descent.consumerNonDescentWitness
    (positiveOneState z phase level cell)
    (positiveTwoState z phase level cell)
    (positiveOneTwoSameAnchorSurface z phase level cell)
    (positiveOneTwoDifferentAnchorMagnitude z phase level cell)

consolidatedMagnitudeCannotFactor :
  ∀ {R}
    (z : Klein.Point (Render.klein R))
    (phase : Base.HexTruth)
    (level : Level.level27CuspFibre)
    (cell : Stage12.StageRelation144) →
  Descent.FactorsThrough
    consolidatedAnchorObserver
    anchorMagnitude →
  ⊥
consolidatedMagnitudeCannotFactor z phase level cell =
  Descent.nonDescentWitnessBlocksFactorization
    (consolidatedMagnitudeNonDescent z phase level cell)

consolidatedMagnitudeRepair :
  ∀ {R} →
  Repair.RefinementRepairs
    (consolidatedAnchorObserver {R})
    anchorMagnitude
    anchorMagnitude
consolidatedMagnitudeRepair =
  Observer.pairRefinesRight
    consolidatedAnchorObserver
    anchorMagnitude

------------------------------------------------------------------------
-- 8. Coarse SSP-level coherence is meaningful, but it does not lift to a
--    magnitude-preserving SignedMultiplicity C3 action.
------------------------------------------------------------------------

record MagnitudePreservingSignedCycleLift : Set where
  field
    lift :
      Signed.SignedMultiplicity →
      Signed.SignedMultiplicity

    coarseCycle :
      (m : Signed.SignedMultiplicity) →
      SSPLevel.signedMultiplicityToSSP (lift m)
      ≡
      SSPDihedral.cycle
        (SSPLevel.signedMultiplicityToSSP m)

    preservesMagnitude :
      (m : Signed.SignedMultiplicity) →
      SSPLevel.signedMagnitude (lift m)
      ≡
      SSPLevel.signedMagnitude m

open MagnitudePreservingSignedCycleLift public

noMagnitudePreservingSignedCycleLift :
  MagnitudePreservingSignedCycleLift →
  ⊥
noMagnitudePreservingSignedCycleLift bridge
  with lift bridge (Signed.negativeMultiplicity 1)
... | Signed.negativeMultiplicity n
    with coarseCycle bridge (Signed.negativeMultiplicity 1)
...   | ()
... | Signed.zeroMultiplicity
    with preservesMagnitude bridge (Signed.negativeMultiplicity 1)
...   | ()
... | Signed.positiveMultiplicity n
    with coarseCycle bridge (Signed.negativeMultiplicity 1)
...   | ()

------------------------------------------------------------------------
-- 9. Existing finite Grothendieck/sheaf and independent bifiltration receipts.
------------------------------------------------------------------------

stage12SiteReceipt :
  Stage12.StageTwelveSiteSheafReceipt
stage12SiteReceipt =
  Stage12.canonicalStageTwelveSiteSheafReceipt

jointBifiltrationReceipt :
  JointBif.JointFibreBifiltrationBoundary
jointBifiltrationReceipt =
  JointBif.canonicalJointFibreBifiltrationBoundary

------------------------------------------------------------------------
-- 10. Exact next-stage claim boundary.
------------------------------------------------------------------------

record Consolidated369NextStageBoundary : Set where
  constructor consolidated369-next-stage-boundary
  field
    jointFibreAnd144SignedStalkComposed : Bool
    anchorRestrictionEqualsJointSignedCoordinate : Bool
    optionalSignedLevel3CoherenceTyped : Bool

    level27NonDescentFromConsolidatedBasePaid : Bool
    signedMagnitudeNonDescentFromAnchorSurfacePaid : Bool
    signedMagnitudeRepairPaid : Bool

    coarseSSPLevel3DihedralEquivalencePaid : Bool
    magnitudePreservingFineCycleLiftExists : Bool

    finiteStage12GrothendieckSiteReused : Bool
    jointResolutionBifiltrationReused : Bool

    stage12SiteEqualsAnalyticModularSite : Bool
    fibreOnlyReflectionEqualsAnalyticReflection : Bool
    signedFRACTRANArithmeticEqualsModularGeometry : Bool
    principalLevelTowerEqualsOldRelational369Horizon : Bool

open Consolidated369NextStageBoundary public

canonicalConsolidated369NextStageBoundary :
  Consolidated369NextStageBoundary
canonicalConsolidated369NextStageBoundary =
  consolidated369-next-stage-boundary
    true true true
    true true true
    true false
    true true
    false false false false
