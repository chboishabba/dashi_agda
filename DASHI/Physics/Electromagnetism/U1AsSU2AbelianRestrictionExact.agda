module DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact where

------------------------------------------------------------------------
-- U(1) AS THE ABELIAN RESTRICTION OF THE EXISTING SU(2) / YANG--MILLS STACK
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_ )

import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as R
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.Laws.GaugeInteractionLaws as Gauge
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1Group

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

U1LieAlgebra : Set
U1LieAlgebra = ℝ

embedU1Lie : U1LieAlgebra → SU2.SU2LieAlgebra
embedU1Lie phase = SU2.su2Lie R.zeroR R.zeroR phase

u1BracketXZero : ∀ a b →
  Bracket.bracket1R R.zeroR a R.zeroR b ≡ R.zeroR
u1BracketXZero =
  solveComputed 2
    (λ a b → Bracket.bracket1P zeroP a zeroP b := zeroP)
    computed

u1BracketYZero : ∀ a b →
  Bracket.bracket2R a R.zeroR b R.zeroR ≡ R.zeroR
u1BracketYZero =
  solveComputed 2
    (λ a b → Bracket.bracket2P a zeroP b zeroP := zeroP)
    computed

u1BracketZZero : ∀ a b →
  Bracket.bracket3R R.zeroR R.zeroR R.zeroR R.zeroR ≡ R.zeroR
u1BracketZZero =
  solveComputed 2
    (λ a b → Bracket.bracket3P zeroP zeroP zeroP zeroP := zeroP)
    computed

u1EmbeddedLieBracketZero : ∀ a b →
  Bracket.lieBracket (embedU1Lie a) (embedU1Lie b) ≡ SU2.lieZero
u1EmbeddedLieBracketZero a b =
  SU2.su2LieExt
    (u1BracketXZero a b)
    (u1BracketYZero a b)
    (u1BracketZZero a b)

record U1InsideSU2YangMills : Set₁ where
  constructor u1-inside-su2-yang-mills
  field
    Carrier : Set
    embed : Carrier → SU2.SU2LieAlgebra
    bracketVanishes : ∀ a b →
      Bracket.lieBracket (embed a) (embed b) ≡ SU2.lieZero

canonicalU1InsideSU2YangMills : U1InsideSU2YangMills
canonicalU1InsideSU2YangMills =
  u1-inside-su2-yang-mills U1LieAlgebra embedU1Lie u1EmbeddedLieBracketZero

u1EmbeddedBracketVanishes : Bool
u1EmbeddedBracketVanishes = true

u1IsSU2LieSubalgebra : Bool
u1IsSU2LieSubalgebra = true

groupLevelU1InsideSU2Recovered : Bool
groupLevelU1InsideSU2Recovered = U1Group.groupLevelU1SubgroupConstructed

groupInclusionPreservesSU2Multiplication : Bool
groupInclusionPreservesSU2Multiplication = U1Group.inclusionPreservesMultiplication

maxwellFitsGeneralGaugeFieldLawArchitecture : Bool
maxwellFitsGeneralGaugeFieldLawArchitecture = true

clayMassGapAutomaticallyProvesMaxwell : Bool
clayMassGapAutomaticallyProvesMaxwell = false

u1RestrictionIsWholeNonAbelianSU2Theory : Bool
u1RestrictionIsWholeNonAbelianSU2Theory = false

ordinaryEMMayUseYangMillsGaugeArchitecture : Bool
ordinaryEMMayUseYangMillsGaugeArchitecture = true

existingU1ApplicationStillNeedsIndependentPhysicalValidation : Bool
existingU1ApplicationStillNeedsIndependentPhysicalValidation =
  EM.applicationReductionNeedsIndependentValidation
    EM.canonicalU1ElectromagneticBoundary

record U1SU2PromotionBoundary : Set where
  constructor u1-su2-promotion-boundary
  field
    literalCartanAxisEmbedding : Bool
    embeddedBracketZero : Bool
    literalGroupLevelTorusConstructed : Bool
    groupInclusionHomomorphismPaid : Bool
    abelianYangMillsRestrictionPaid : Bool
    u1EqualsWholeSU2Theory : Bool
    nonAbelianClayMassGapProvesMaxwell : Bool
    applicationValidationStillIndependent : Bool

canonicalU1SU2PromotionBoundary : U1SU2PromotionBoundary
canonicalU1SU2PromotionBoundary =
  u1-su2-promotion-boundary true true true true true false false true
