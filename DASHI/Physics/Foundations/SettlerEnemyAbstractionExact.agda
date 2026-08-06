module DASHI.Physics.Foundations.SettlerEnemyAbstractionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- This module models a rhetorical compression and its information loss.  It
-- does not endorse any classification below and does not identify a population
-- with an ancient, theological, or ideological enemy category.

data ConcreteActor : Set where
  hamasActor : ConcreteActor
  palestinianCivilianPopulation : ConcreteActor
  malayanCommunistForces : ConcreteActor
  heterogeneousAntiColonialMovements : ConcreteActor

data AbsoluteEnemyCategory : Set where
  amalekCategory : AbsoluteEnemyCategory
  globalCommunismCategory : AbsoluteEnemyCategory

rhetoricalCompression : ConcreteActor → AbsoluteEnemyCategory
rhetoricalCompression hamasActor = amalekCategory
rhetoricalCompression palestinianCivilianPopulation = amalekCategory
rhetoricalCompression malayanCommunistForces = globalCommunismCategory
rhetoricalCompression heterogeneousAntiColonialMovements =
  globalCommunismCategory

combatantAndCivilianCollapseUnderCompression :
  rhetoricalCompression hamasActor
  ≡
  rhetoricalCompression palestinianCivilianPopulation
combatantAndCivilianCollapseUnderCompression = refl

communistAndAntiColonialCollapseUnderCompression :
  rhetoricalCompression malayanCommunistForces
  ≡
  rhetoricalCompression heterogeneousAntiColonialMovements
communistAndAntiColonialCollapseUnderCompression = refl

hamasActorIsNotCivilianPopulation :
  hamasActor ≡ palestinianCivilianPopulation → ⊥
hamasActorIsNotCivilianPopulation ()

malayanCommunistsAreNotAllAntiColonialMovements :
  malayanCommunistForces ≡ heterogeneousAntiColonialMovements → ⊥
malayanCommunistsAreNotAllAntiColonialMovements ()

CompressionInjective : Set
CompressionInjective =
  (x y : ConcreteActor) →
  rhetoricalCompression x ≡ rhetoricalCompression y →
  x ≡ y

rhetoricalCompressionIsNotInjective : ¬ CompressionInjective
rhetoricalCompressionIsNotInjective injective =
  hamasActorIsNotCivilianPopulation
    (injective hamasActor palestinianCivilianPopulation refl)

------------------------------------------------------------------------
-- Explicit lexical use and structural comparison are separate authorities.
-- The attached material supports only structural homology for colonial
-- Australia; it does not document local settlers using the word "Amalek".

data AnalogyAuthority : Set where
  explicitLexicalUse : AnalogyAuthority
  structuralHomologyOnly : AnalogyAuthority

data ComparisonContext : Set where
  palestineAmalekRhetoric : ComparisonContext
  indigenousAustraliaSettlerStructure : ComparisonContext

comparisonAuthority : ComparisonContext → AnalogyAuthority
comparisonAuthority palestineAmalekRhetoric = explicitLexicalUse
comparisonAuthority indigenousAustraliaSettlerStructure =
  structuralHomologyOnly

australianComparisonIsStructuralOnly :
  comparisonAuthority indigenousAustraliaSettlerStructure
  ≡ structuralHomologyOnly
australianComparisonIsStructuralOnly = refl

structuralHomologyIsNotExplicitLexicalUse :
  structuralHomologyOnly ≡ explicitLexicalUse → ⊥
structuralHomologyIsNotExplicitLexicalUse ()

------------------------------------------------------------------------
-- A finite model of the eliminatory frontier transformation described in the
-- source literature.  It represents the settler framing, not a moral or legal
-- justification for it.

data SettlerFramingStage : Set where
  priorSovereignty : SettlerFramingStage
  constitutedAsObstacle : SettlerFramingStage
  representedAsRemovable : SettlerFramingStage

nextFramingStage : SettlerFramingStage → SettlerFramingStage
nextFramingStage priorSovereignty = constitutedAsObstacle
nextFramingStage constitutedAsObstacle = representedAsRemovable
nextFramingStage representedAsRemovable = representedAsRemovable

eliminatoryFramingSequence :
  nextFramingStage (nextFramingStage priorSovereignty)
  ≡ representedAsRemovable
eliminatoryFramingSequence = refl

record EnemyAbstractionBoundary : Set where
  constructor enemyAbstractionBoundary
  field
    rhetoricalCategoryPreservesActorDistinctions : Bool
    rhetoricalCategoryPreservesActorDistinctionsIsFalse :
      rhetoricalCategoryPreservesActorDistinctions ≡ false

    structuralHomologyProvesIdenticalHistories : Bool
    structuralHomologyProvesIdenticalHistoriesIsFalse :
      structuralHomologyProvesIdenticalHistories ≡ false

    indigenousAustraliansDocumentedAsLiteralAmalek : Bool
    indigenousAustraliansDocumentedAsLiteralAmalekIsFalse :
      indigenousAustraliansDocumentedAsLiteralAmalek ≡ false

    eliminatoryDescriptionJustifiesElimination : Bool
    eliminatoryDescriptionJustifiesEliminationIsFalse :
      eliminatoryDescriptionJustifiesElimination ≡ false

open EnemyAbstractionBoundary public

canonicalEnemyAbstractionBoundary : EnemyAbstractionBoundary
canonicalEnemyAbstractionBoundary =
  enemyAbstractionBoundary
    false refl
    false refl
    false refl
    false refl
