module DASHI.Law.SensibLawWrongTypeRelationalDepthHyperfabricExact where

------------------------------------------------------------------------
-- DASHI-original finite relational-depth / query adequacy mathematics.
--
-- McNamara (user-provided transcript, 2026-09-30): three modes and their
-- ordered nine cells (violated frame, imposed logic), with an asserted but
-- unproved coverage of serious wrongs. All deeper axes and proofs are DASHI.
--
-- Crenshaw, Mapping the Margins (1991), DOI 10.2307/1229039 motivates
-- intersectional loss under flattening, NOT this finite theorem.
-- Kimmerer, Braiding Sweetgrass (2013): relational/reciprocal inspiration,
-- not an Artin braid proof or permission to represent Indigenous knowledge.
-- Two-Eyed Seeing / custodianship: independently sourced obligations and
-- authorities must be retained rather than invented by the grid.
-- Lacan/Irigaray grammar, dialectical materialism and pants/cobordism are
-- distinct source-bounded interpretation/transport lanes.
--
-- No legal offence elements, cultural authority, or case-specific liability
-- are inferred from coordinate membership or any gluing operation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWrongTypeCareTransactionPowerGridExact as Grid
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants

-- n independent, ordered ternary RELATIONAL AXES, not a tetration tower.
Hypervoxel : Nat → Set
Hypervoxel n = Vec Grid.Mode n

xy : Hypervoxel 2
xy = Grid.care ∷ Grid.care ∷ []

xyz : Hypervoxel 3
xyz = Grid.care ∷ Grid.care ∷ Grid.care ∷ []

xyza : Hypervoxel 4
xyza = Grid.care ∷ Grid.care ∷ Grid.care ∷ Grid.care ∷ []

productSiteCount : Nat → Nat
productSiteCount n = Tower.pow 3 n

gridNine : productSiteCount 2 ≡ 9
gridNine = refl

cubeTwentySeven : productSiteCount 3 ≡ 27
cubeTwentySeven = refl

fourAxisEightyOne : productSiteCount 4 ≡ 81
fourAxisEightyOne = refl

threeCubesAreNotFourAxes : Tower.pow 27 3 ≡ 19683
threeCubesAreNotFourAxes = refl

ternaryFunctionSpaceAboveCube :
  Tower.tetration 3 3 ≡ Tower.pow 3 27
ternaryFunctionSpaceAboveCube = Tower.triadicTetrationThree

-- The first two coordinates are the ORIGINAL McNamara cell.
-- Later coordinates are typed roles, and MUST NOT be interpreted as
-- violated/imposed pairs without a separate role specification.
firstTwo : ∀ {n} → Hypervoxel (suc (suc n)) → Grid.Cell
firstTwo (x ∷ y ∷ rest) = Grid.cell x y

-- Generic depth loss: an (n+1)-coordinate situation and its n-coordinate
-- suffix can coincide while an exact consumer still needs the leading axis.
tail : ∀ {n} → Hypervoxel (suc n) → Hypervoxel n
tail (x ∷ rest) = rest

head : ∀ {n} → Hypervoxel (suc n) → Grid.Mode
head (x ∷ rest) = x

allCare : (n : Nat) → Hypervoxel n
allCare zero = []
allCare (suc n) = Grid.care ∷ allCare n

careNotPower : Grid.care ≡ Grid.power → ⊥
careNotPower ()

lossOfOneAxis : ∀ (n : Nat) →
  INF.NonFactorabilityWitness
    (tail {n = n}) (head {n = n})
lossOfOneAxis n =
  INF.nonFactorabilityWitness
    (Grid.care ∷ allCare n)
    (Grid.power ∷ allCare n)
    refl
    careNotPower

oneAxisLostCannotAnswer : ∀ (n : Nat) →
  INF.FactorsThrough (tail {n = n}) (head {n = n}) → ⊥
oneAxisLostCannotAnswer n =
  INF.witnessRulesOutEveryFlatFactorisation (lossOfOneAxis n)

-- More useful than a cardinality argument: any rechart of the
-- n-coordinate suffix STILL cannot answer that leading-axis query.
noSuffixOnlyRechart : ∀ (n : Nat) {View : Set}
  (rechart : Hypervoxel n → View) →
  INF.FactorsThrough (λ state → rechart (tail state))
    (head {n = n}) → ⊥
noSuffixOnlyRechart n rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart (lossOfOneAxis n)

------------------------------------------------------------------------
-- Four-way example: every coordinate is indispensable for a consumer
-- whose answer is the FULL XYZA state, among the four 3-coordinate drops.
-- Not a claim that every legal query has minimum width four!
------------------------------------------------------------------------

Triple : Set
Triple = Grid.Mode × (Grid.Mode × Grid.Mode)

Quad : Set
Quad = Grid.Mode × (Grid.Mode × (Grid.Mode × Grid.Mode))

base : Quad
base = Grid.care , (Grid.care , (Grid.care , Grid.care))

xChanged yChanged zChanged aChanged : Quad
xChanged = Grid.power , (Grid.care , (Grid.care , Grid.care))
yChanged = Grid.care , (Grid.power , (Grid.care , Grid.care))
zChanged = Grid.care , (Grid.care , (Grid.power , Grid.care))
aChanged = Grid.care , (Grid.care , (Grid.care , Grid.power))

data ThreeAxisView : Set where
  omitX omitY omitZ omitA : ThreeAxisView

observeThree : ThreeAxisView → Quad → Triple
observeThree omitX (x , (y , (z , a))) = y , (z , a)
observeThree omitY (x , (y , (z , a))) = x , (z , a)
observeThree omitZ (x , (y , (z , a))) = x , (y , a)
observeThree omitA (x , (y , (z , a))) = x , (y , z)

xDifferent : base ≡ xChanged → ⊥
xDifferent equal = careNotPower (cong proj₁ equal)

yDifferent : base ≡ yChanged → ⊥
yDifferent equal = careNotPower (cong (λ q → proj₁ (proj₂ q)) equal)

zDifferent : base ≡ zChanged → ⊥
zDifferent equal =
  careNotPower (cong (λ q → proj₁ (proj₂ (proj₂ q))) equal)

aDifferent : base ≡ aChanged → ⊥
aDifferent equal =
  careNotPower (cong (λ q → proj₂ (proj₂ (proj₂ q))) equal)

fourAxisCollision : (view : ThreeAxisView) →
  INF.NonFactorabilityWitness (observeThree view) (λ q → q)
fourAxisCollision omitX =
  INF.nonFactorabilityWitness base xChanged refl xDifferent
fourAxisCollision omitY =
  INF.nonFactorabilityWitness base yChanged refl yDifferent
fourAxisCollision omitZ =
  INF.nonFactorabilityWitness base zChanged refl zDifferent
fourAxisCollision omitA =
  INF.nonFactorabilityWitness base aChanged refl aDifferent

noThreeAxisViewDeterminesFullFour : (view : ThreeAxisView) →
  INF.FactorsThrough (observeThree view) (λ q → q) → ⊥
noThreeAxisViewDeterminesFullFour view =
  INF.witnessRulesOutEveryFlatFactorisation (fourAxisCollision view)

fullFourIsSufficient :
  INF.FactorsThrough (λ q → q) (λ q → q)
fullFourIsSufficient = INF.factorsThrough (λ q → q) (λ _ → refl)

------------------------------------------------------------------------
-- The classified cell is an INDEX; retain source/permission/identity
-- evidence in its fibre. Glue only with evidence-backed compatibility.
------------------------------------------------------------------------

record RelationalFibre (n : Nat) : Set where
  constructor relational-fibre
  field
    address : Hypervoxel n
    actorAndInterestReference : String
    legalSystemAndPeriodReference : String
    sourceRevisionReference : String
    custodialAuthorityReference : String
    interpretationReference : String
    evidenceReference : String

record CompatibleGluing {n m : Nat}
    (left : RelationalFibre n) (right : RelationalFibre m) : Set where
  field
    sharedInterface : String
    identityAndTimeWeld : Set
    sameNormativeAuthorityOrExplicitComparison : Set
    evidenceThatInterfaceIsShared : Set

-- A compatibility record is a DEMAND for proofs/evidence. Neither pants
-- geometry nor shared identifiers discharge the producer obligations.
-- No automatic conversion to WrongType applicability or violation receipts.
