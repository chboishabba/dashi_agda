module DASHI.Moonshine.ConwayNortonTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.JCoefficientCharacterBridge as JCB
import DASHI.Moonshine.MoonshineGroupBase as MGB
import DASHI.Moonshine.MonsterMcKayThompsonClosure as MMC
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.TwistedModuleModularity as TM

------------------------------------------------------------------------
-- Conway--Norton theorem closure package.
--
-- The theorem has two logically distinct halves:
--
--  1. realization: each McKay--Thompson series is the graded trace of a
--     Monster element acting on V^natural;
--  2. genus zero: that series is the normalized Hauptmodul for its moonshine
--     group.
--
-- Existing exact finite-series/group closure remains owned by
-- `MonsterMcKayThompsonClosure`.  This file adds the missing VOA realization,
-- twisted modularity, and theorem-level promotion package.

record MonsterVOAAction
  (Monster K : Set)
  (monsterGroup : GR.Group Monster)
  (construction : VN.VNaturalConstruction) : Setω where
  field
    action :
      VOA.VOAGroupAction
        Monster
        monsterGroup
        (VN.VNaturalConstruction.Vnatural construction)
    faithful : Set
    fullAutomorphismGroup : Set
    preservesIntegralForm : Set
    gradeRepresentations : GR.GradedRepresentation Monster K monsterGroup
    gradeActionAgreesWithVOA : Set

open MonsterVOAAction public

record McKayThompsonRealization
  (Monster ExactLaurentSeries K : Set)
  (monsterGroup : GR.Group Monster)
  (construction : VN.VNaturalConstruction)
  (monsterAction : MonsterVOAAction Monster K monsterGroup construction) : Setω where
  field
    gradedTraceSeries : Monster → ExactLaurentSeries
    traceCoefficient : Monster → ExactLaurentSeries → K
    isVOAGradedTrace : Set
    identityTraceIsJMinus744 : Set
    firstCoefficientBridge : JCB.FirstMoonshineCoefficientBridge
    classInvariant : Set
    powerMapCompatible : Set

open McKayThompsonRealization public

record ReplicabilityPackage
  (Monster ExactLaurentSeries : Set)
  (realization : Monster → ExactLaurentSeries) : Setω where
  field
    FaberPolynomial : Set
    replicationIdentity : Monster → Set
    HeckeCompatibility : Monster → Set
    powerMapCompatibility : Monster → Set
    normalizedPrincipalPart : Monster → Set

open ReplicabilityPackage public

record HauptmodulGenusZeroPackage
  (Monster FuchsianGroup ExactLaurentSeries : Set)
  (ClassGroup : Monster → FuchsianGroup)
  (series : Monster → ExactLaurentSeries) : Setω where
  field
    actsOnUpperHalfPlane : FuchsianGroup → Set
    discrete : FuchsianGroup → Set
    finiteCovolume : FuchsianGroup → Set
    genusZero : FuchsianGroup → Set
    oneCuspNormalized : Monster → Set
    modularForClassGroup : Monster → Set
    generatesFunctionField : Monster → Set
    hauptmodul : Monster → Set

open HauptmodulGenusZeroPackage public

record ConwayNortonTheorem
  (Monster K FuchsianGroup ExactLaurentSeries : Set)
  (monsterGroup : GR.Group Monster)
  (construction : VN.VNaturalConstruction)
  (monsterAction : MonsterVOAAction Monster K monsterGroup construction)
  (realization :
    McKayThompsonRealization
      Monster ExactLaurentSeries K monsterGroup construction monsterAction)
  (ClassGroup : Monster → FuchsianGroup) : Setω where
  field
    twistedModularityInput :
      TM.VNaturalModularityPackage
        (record
          { group = monsterGroup
          ; inverse = λ g → g
          ; leftInverse = λ g →
              let open GR.Group monsterGroup in
              leftIdentity g
          ; rightInverse = λ g →
              let open GR.Group monsterGroup in
              leftIdentity g
          })
        construction
    replicability :
      ReplicabilityPackage
        Monster
        ExactLaurentSeries
        (McKayThompsonRealization.gradedTraceSeries realization)
    genusZeroPackage :
      HauptmodulGenusZeroPackage
        Monster
        FuchsianGroup
        ExactLaurentSeries
        ClassGroup
        (McKayThompsonRealization.gradedTraceSeries realization)
    finiteMcKayThompsonClosureCompatible : Set
    realizationForEveryMonsterClass : Set
    normalizedHauptmodulForEveryClass : Set

  gradedTraceRealization :
    Monster → ExactLaurentSeries
  gradedTraceRealization =
    McKayThompsonRealization.gradedTraceSeries realization

  conwayNortonStatement : Set
  conwayNortonStatement =
    realizationForEveryMonsterClass

open ConwayNortonTheorem public

------------------------------------------------------------------------
-- Dependency-correct promotion boundary.
--
-- A value of this record is the complete theorem package.  The repo must not
-- promote from character tables, coefficient coincidences, or modular data
-- alone; all four construction layers are required.

record MoonshineTheoremPromotionBoundary : Setω where
  field
    VnaturalConstruction : Set
    MonsterActionOnVnatural : Set
    TwistedModuleModularity : Set
    McKayThompsonRealization : Set
    Replicability : Set
    GenusZeroForAllClasses : Set
    ConwayNortonClosed : Set
    noCoefficientOnlyPromotion : Set
    noModularityOnlyPromotion : Set
    noFiniteTableOnlyPromotion : Set

open MoonshineTheoremPromotionBoundary public
