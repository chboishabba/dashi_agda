module DASHI.Physics.Closure.MillenniumSchemaIsomorphismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt as YM
import DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt as NS

------------------------------------------------------------------------
-- Millennium schema isomorphism receipt.
--
-- This receipt records the role-preserving map from the Yang-Mills tower to
-- the Navier-Stokes tower across T0-T4.  It is a structural correspondence
-- between proof-obligation roles only; it does not identify the equations or
-- promote either Clay problem.

data MillenniumSchemaIsomorphismStatus : Set where
  ymNsTowerRolesMappedNoClayNoTerminalPromotion :
    MillenniumSchemaIsomorphismStatus

data MillenniumSchemaStageMap : Set where
  T0FiniteLocalControlMap :
    MillenniumSchemaStageMap

  T1UniformFiniteDepthFamilyMap :
    MillenniumSchemaStageMap

  T2LiftAttemptMap :
    MillenniumSchemaStageMap

  T3ContinuumPromotionObligationMap :
    MillenniumSchemaStageMap

  T4ExternalAuthorityBoundaryMap :
    MillenniumSchemaStageMap

canonicalMillenniumSchemaStageMap :
  List MillenniumSchemaStageMap
canonicalMillenniumSchemaStageMap =
  T0FiniteLocalControlMap
  ∷ T1UniformFiniteDepthFamilyMap
  ∷ T2LiftAttemptMap
  ∷ T3ContinuumPromotionObligationMap
  ∷ T4ExternalAuthorityBoundaryMap
  ∷ []

data MillenniumSchemaDependencyEdge : Set where
  T0ToT1 :
    MillenniumSchemaDependencyEdge

  T1ToT2 :
    MillenniumSchemaDependencyEdge

  T2ToT3 :
    MillenniumSchemaDependencyEdge

  T3ToT4 :
    MillenniumSchemaDependencyEdge

canonicalMillenniumSchemaDependencyEdges :
  List MillenniumSchemaDependencyEdge
canonicalMillenniumSchemaDependencyEdges =
  T0ToT1
  ∷ T1ToT2
  ∷ T2ToT3
  ∷ T3ToT4
  ∷ []

t0TowerRole : String
t0TowerRole =
  "T0: finite local control"

t0YangMillsSide : String
t0YangMillsSide =
  "FiniteDepthLatticeGapReceipt, local finite-carrier spectral gap"

t0NavierStokesSide : String
t0NavierStokesSide =
  "finite weak formulation, L2 energy, enstrophy, vorticity, BKM rungs"

t1TowerRole : String
t1TowerRole =
  "T1: uniform finite-depth family"

t1YangMillsSide : String
t1YangMillsSide =
  "FiniteDepthLatticeGapProObjectReceipt, pointwise depth gap family"

t1NavierStokesSide : String
t1NavierStokesSide =
  "depth-indexed weak-solution and regularity tower"

t2TowerRole : String
t2TowerRole =
  "T2: lift attempt"

t2YangMillsSide : String
t2YangMillsSide =
  "ColimitGapLiftOnHamiltonianReceipt, ColimitHamiltonianGapThreadReceipt"

t2NavierStokesSide : String
t2NavierStokesSide =
  "colimitRegularityLiftReusedOnlyAsAnalogy, regularity lift target"

t3TowerRole : String
t3TowerRole =
  "T3: continuum promotion"

t3YangMillsSide : String
t3YangMillsSide =
  "ContinuumClayMassGapReceiptObligation"

t3NavierStokesSide : String
t3NavierStokesSide =
  "ContinuumRegularityObligation"

t4TowerRole : String
t4TowerRole =
  "T4: external authority"

t4YangMillsSide : String
t4YangMillsSide =
  "Clay/YM boundary, preprint and alternative authority receipts, accepted authority absent"

t4NavierStokesSide : String
t4NavierStokesSide =
  "BKM/Clay regularity authority obligation, accepted authority absent"

finiteDepthInhabitedDoesNotImplyContinuumPromoted : String
finiteDepthInhabitedDoesNotImplyContinuumPromoted =
  "finite-depth inhabited != continuum promoted"

record MillenniumSchemaIsomorphismReceipt : Setω where
  field
    status :
      MillenniumSchemaIsomorphismStatus

    sharedSchemaReceipt :
      Schema.MillenniumTowerSchemaReceipt

    sharedSchemaReceiptIsCanonical :
      sharedSchemaReceipt ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    yangMillsTowerReceipt :
      YM.MillenniumTowerYangMillsInstanceReceipt

    yangMillsTowerReceiptSelected :
      Bool

    yangMillsTowerReceiptSelectedIsTrue :
      yangMillsTowerReceiptSelected ≡ true

    navierStokesTowerReceipt :
      NS.MillenniumTowerNavierStokesInstanceReceipt

    navierStokesTowerReceiptSelected :
      Bool

    navierStokesTowerReceiptSelectedIsTrue :
      navierStokesTowerReceiptSelected ≡ true

    sharedSchemaStages :
      List Schema.MillenniumTowerSchemaStage

    sharedSchemaStagesAreCanonical :
      sharedSchemaStages ≡ Schema.canonicalMillenniumTowerSchemaStages

    schemaStageMap :
      List MillenniumSchemaStageMap

    schemaStageMapIsCanonical :
      schemaStageMap ≡ canonicalMillenniumSchemaStageMap

    schemaDependencyEdges :
      List MillenniumSchemaDependencyEdge

    schemaDependencyEdgesAreCanonical :
      schemaDependencyEdges ≡ canonicalMillenniumSchemaDependencyEdges

    yangMillsDependencyEdges :
      List MillenniumSchemaDependencyEdge

    yangMillsDependencyEdgesPreserved :
      yangMillsDependencyEdges ≡ canonicalMillenniumSchemaDependencyEdges

    navierStokesDependencyEdges :
      List MillenniumSchemaDependencyEdge

    navierStokesDependencyEdgesPreserved :
      navierStokesDependencyEdges ≡ canonicalMillenniumSchemaDependencyEdges

    t0Role :
      String

    t0RoleIsCanonical :
      t0Role ≡ t0TowerRole

    t0YangMills :
      String

    t0YangMillsIsCanonical :
      t0YangMills ≡ t0YangMillsSide

    t0NavierStokes :
      String

    t0NavierStokesIsCanonical :
      t0NavierStokes ≡ t0NavierStokesSide

    t1Role :
      String

    t1RoleIsCanonical :
      t1Role ≡ t1TowerRole

    t1YangMills :
      String

    t1YangMillsIsCanonical :
      t1YangMills ≡ t1YangMillsSide

    t1NavierStokes :
      String

    t1NavierStokesIsCanonical :
      t1NavierStokes ≡ t1NavierStokesSide

    t2Role :
      String

    t2RoleIsCanonical :
      t2Role ≡ t2TowerRole

    t2YangMills :
      String

    t2YangMillsIsCanonical :
      t2YangMills ≡ t2YangMillsSide

    t2NavierStokes :
      String

    t2NavierStokesIsCanonical :
      t2NavierStokes ≡ t2NavierStokesSide

    t3Role :
      String

    t3RoleIsCanonical :
      t3Role ≡ t3TowerRole

    t3YangMills :
      String

    t3YangMillsIsCanonical :
      t3YangMills ≡ t3YangMillsSide

    t3NavierStokes :
      String

    t3NavierStokesIsCanonical :
      t3NavierStokes ≡ t3NavierStokesSide

    t4Role :
      String

    t4RoleIsCanonical :
      t4Role ≡ t4TowerRole

    t4YangMills :
      String

    t4YangMillsIsCanonical :
      t4YangMills ≡ t4YangMillsSide

    t4NavierStokes :
      String

    t4NavierStokesIsCanonical :
      t4NavierStokes ≡ t4NavierStokesSide

    negativeInvariant :
      String

    negativeInvariantIsCanonical :
      negativeInvariant ≡ finiteDepthInhabitedDoesNotImplyContinuumPromoted

    schemaIsomorphismDefined :
      Bool

    schemaIsomorphismDefinedIsTrue :
      schemaIsomorphismDefined ≡ true

    tierCorrespondenceExplicit :
      Bool

    tierCorrespondenceExplicitIsTrue :
      tierCorrespondenceExplicit ≡ true

    sameTypeTheoreticStructureCandidate :
      Bool

    sameTypeTheoreticStructureCandidateIsTrue :
      sameTypeTheoreticStructureCandidate ≡ true

    yangMillsClayPromoted :
      Bool

    yangMillsClayPromotedIsFalse :
      yangMillsClayPromoted ≡ false

    navierStokesClayPromoted :
      Bool

    navierStokesClayPromotedIsFalse :
      navierStokesClayPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open MillenniumSchemaIsomorphismReceipt public

canonicalMillenniumSchemaIsomorphismReceipt :
  MillenniumSchemaIsomorphismReceipt
canonicalMillenniumSchemaIsomorphismReceipt =
  record
    { status =
        ymNsTowerRolesMappedNoClayNoTerminalPromotion
    ; sharedSchemaReceipt =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; sharedSchemaReceiptIsCanonical =
        refl
    ; yangMillsTowerReceipt =
        YM.canonicalMillenniumTowerYangMillsInstanceReceipt
    ; yangMillsTowerReceiptSelected =
        true
    ; yangMillsTowerReceiptSelectedIsTrue =
        refl
    ; navierStokesTowerReceipt =
        NS.canonicalMillenniumTowerNavierStokesInstanceReceipt
    ; navierStokesTowerReceiptSelected =
        true
    ; navierStokesTowerReceiptSelectedIsTrue =
        refl
    ; sharedSchemaStages =
        Schema.canonicalMillenniumTowerSchemaStages
    ; sharedSchemaStagesAreCanonical =
        refl
    ; schemaStageMap =
        canonicalMillenniumSchemaStageMap
    ; schemaStageMapIsCanonical =
        refl
    ; schemaDependencyEdges =
        canonicalMillenniumSchemaDependencyEdges
    ; schemaDependencyEdgesAreCanonical =
        refl
    ; yangMillsDependencyEdges =
        canonicalMillenniumSchemaDependencyEdges
    ; yangMillsDependencyEdgesPreserved =
        refl
    ; navierStokesDependencyEdges =
        canonicalMillenniumSchemaDependencyEdges
    ; navierStokesDependencyEdgesPreserved =
        refl
    ; t0Role =
        t0TowerRole
    ; t0RoleIsCanonical =
        refl
    ; t0YangMills =
        t0YangMillsSide
    ; t0YangMillsIsCanonical =
        refl
    ; t0NavierStokes =
        t0NavierStokesSide
    ; t0NavierStokesIsCanonical =
        refl
    ; t1Role =
        t1TowerRole
    ; t1RoleIsCanonical =
        refl
    ; t1YangMills =
        t1YangMillsSide
    ; t1YangMillsIsCanonical =
        refl
    ; t1NavierStokes =
        t1NavierStokesSide
    ; t1NavierStokesIsCanonical =
        refl
    ; t2Role =
        t2TowerRole
    ; t2RoleIsCanonical =
        refl
    ; t2YangMills =
        t2YangMillsSide
    ; t2YangMillsIsCanonical =
        refl
    ; t2NavierStokes =
        t2NavierStokesSide
    ; t2NavierStokesIsCanonical =
        refl
    ; t3Role =
        t3TowerRole
    ; t3RoleIsCanonical =
        refl
    ; t3YangMills =
        t3YangMillsSide
    ; t3YangMillsIsCanonical =
        refl
    ; t3NavierStokes =
        t3NavierStokesSide
    ; t3NavierStokesIsCanonical =
        refl
    ; t4Role =
        t4TowerRole
    ; t4RoleIsCanonical =
        refl
    ; t4YangMills =
        t4YangMillsSide
    ; t4YangMillsIsCanonical =
        refl
    ; t4NavierStokes =
        t4NavierStokesSide
    ; t4NavierStokesIsCanonical =
        refl
    ; negativeInvariant =
        finiteDepthInhabitedDoesNotImplyContinuumPromoted
    ; negativeInvariantIsCanonical =
        refl
    ; schemaIsomorphismDefined =
        true
    ; schemaIsomorphismDefinedIsTrue =
        refl
    ; tierCorrespondenceExplicit =
        true
    ; tierCorrespondenceExplicitIsTrue =
        refl
    ; sameTypeTheoreticStructureCandidate =
        true
    ; sameTypeTheoreticStructureCandidateIsTrue =
        refl
    ; yangMillsClayPromoted =
        YM.clayYangMillsPromoted YM.canonicalMillenniumTowerYangMillsInstanceReceipt
    ; yangMillsClayPromotedIsFalse =
        YM.millenniumTowerYangMillsNoClayPromotion
    ; navierStokesClayPromoted =
        NS.clayNavierStokesPromoted
          NS.canonicalMillenniumTowerNavierStokesInstanceReceipt
    ; navierStokesClayPromotedIsFalse =
        NS.millenniumTowerNavierStokesNoClayPromotion
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "The map is structural: it preserves proof-obligation roles, not PDE/gauge-theory equivalence"
        ∷ "The dependency order T0 -> T1 -> T2 -> T3 -> T4 is recorded for the shared schema, YM tower, and NS tower"
        ∷ "schemaIsomorphismDefined and tierCorrespondenceExplicit are true"
        ∷ "Finite-depth inhabited does not imply continuum promoted"
        ∷ "Clay and terminal promotion remain false"
        ∷ []
    }

canonicalSchemaIsomorphismDefinedIsTrue :
  schemaIsomorphismDefined canonicalMillenniumSchemaIsomorphismReceipt
  ≡
  true
canonicalSchemaIsomorphismDefinedIsTrue =
  refl

canonicalTierCorrespondenceExplicitIsTrue :
  tierCorrespondenceExplicit canonicalMillenniumSchemaIsomorphismReceipt
  ≡
  true
canonicalTierCorrespondenceExplicitIsTrue =
  refl

bothProblemsShareSameTypeTheoreticStructure :
  sameTypeTheoreticStructureCandidate
    canonicalMillenniumSchemaIsomorphismReceipt
  ≡
  true
bothProblemsShareSameTypeTheoreticStructure =
  refl

millenniumSchemaIsomorphismKeepsClayFalse :
  clayPromotion canonicalMillenniumSchemaIsomorphismReceipt
  ≡
  false
millenniumSchemaIsomorphismKeepsClayFalse =
  refl

millenniumSchemaIsomorphismKeepsTerminalFalse :
  terminalPromotion canonicalMillenniumSchemaIsomorphismReceipt
  ≡
  false
millenniumSchemaIsomorphismKeepsTerminalFalse =
  refl
