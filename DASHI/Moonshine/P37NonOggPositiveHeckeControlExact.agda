module DASHI.Moonshine.P37NonOggPositiveHeckeControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / EXECUTABLE REFERENCE
--
-- SageMath, "Module of supersingular points" reference manual:
--
--   S = SupersingularModule(37)
--   S.hecke_matrix(2)
--     [1 1 1]
--     [1 0 2]
--     [1 2 0]
--
-- SageMath Brandt-module reference also records
--
--   BrandtModule(37).monodromy_weights() = (1,1,1).
--
-- No DOI is asserted for software documentation.
-- Mathematical context: John Voight, "Quaternion Algebras",
-- DOI: 10.1007/978-3-030-56694-4.
--
-- OGG CLASSIFICATION AUTHORITY
-- Andrew P. Ogg, 1974/75; Duncan--Ono, "The Jack Daniels Problem",
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Run the same positivity test used at p=11 on the non-Ogg control p=37.
-- Since all monodromy weights are one, stack unweighting is trivial: the three
-- Brandt classes are already an ordinary unweighted carrier.
--
-- The source T2 matrix is symmetric, positive and 3-regular.  Moreover
--
--   B_37(2)^2 - 2 I
--     = [[1,3,3],[3,3,1],[3,1,3]]
--
-- is entrywise Nat-valued and 7-regular, so the first unital prime-square
-- positivity gate survives this NON-OGG control.  Therefore positivity,
-- reciprocal unweighting, symmetry and T2-square positivity are not by
-- themselves Ogg selectors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Controls

------------------------------------------------------------------------
-- Source T2 as literal positive neighbours.
------------------------------------------------------------------------

p37T2Neighbour : Controls.P37BrandtClass → Fin 3 → Controls.P37BrandtClass
p37T2Neighbour Controls.p37c0 zero = Controls.p37c0
p37T2Neighbour Controls.p37c0 (suc zero) = Controls.p37c1
p37T2Neighbour Controls.p37c0 (suc (suc zero)) = Controls.p37c2
p37T2Neighbour Controls.p37c1 zero = Controls.p37c0
p37T2Neighbour Controls.p37c1 (suc zero) = Controls.p37c2
p37T2Neighbour Controls.p37c1 (suc (suc zero)) = Controls.p37c2
p37T2Neighbour Controls.p37c2 zero = Controls.p37c0
p37T2Neighbour Controls.p37c2 (suc zero) = Controls.p37c1
p37T2Neighbour Controls.p37c2 (suc (suc zero)) = Controls.p37c1

P37R2 : Positive.PositiveFiniteNeighbourSystem Controls.P37BrandtClass
P37R2 =
  record
    { Positive.arity = 3
    ; Positive.neighbour = p37T2Neighbour
    }

isC0 : Controls.P37BrandtClass → Nat
isC0 Controls.p37c0 = 1
isC0 Controls.p37c1 = 0
isC0 Controls.p37c2 = 0

isC1 : Controls.P37BrandtClass → Nat
isC1 Controls.p37c0 = 0
isC1 Controls.p37c1 = 1
isC1 Controls.p37c2 = 0

isC2 : Controls.P37BrandtClass → Nat
isC2 Controls.p37c0 = 0
isC2 Controls.p37c1 = 0
isC2 Controls.p37c2 = 1

p37T2Row0 :
  Positive.positiveOperator P37R2 isC0 Controls.p37c0 ≡ 1
  × Positive.positiveOperator P37R2 isC1 Controls.p37c0 ≡ 1
  × Positive.positiveOperator P37R2 isC2 Controls.p37c0 ≡ 1
p37T2Row0 = refl , refl , refl

p37T2Row1 :
  Positive.positiveOperator P37R2 isC0 Controls.p37c1 ≡ 1
  × Positive.positiveOperator P37R2 isC1 Controls.p37c1 ≡ 0
  × Positive.positiveOperator P37R2 isC2 Controls.p37c1 ≡ 2
p37T2Row1 = refl , refl , refl

p37T2Row2 :
  Positive.positiveOperator P37R2 isC0 Controls.p37c2 ≡ 1
  × Positive.positiveOperator P37R2 isC1 Controls.p37c2 ≡ 2
  × Positive.positiveOperator P37R2 isC2 Controls.p37c2 ≡ 0
p37T2Row2 = refl , refl , refl

------------------------------------------------------------------------
-- Two-step path counts and positive T4 residual.
------------------------------------------------------------------------

twoStepCount :
  (target source : Controls.P37BrandtClass) → Nat
twoStepCount target source =
  Positive.positiveOperator P37R2
    (λ middle → Positive.positiveOperator P37R2
      (λ end → ifTarget target end) middle)
    source
  where
  ifTarget : Controls.P37BrandtClass → Controls.P37BrandtClass → Nat
  ifTarget Controls.p37c0 Controls.p37c0 = 1
  ifTarget Controls.p37c0 Controls.p37c1 = 0
  ifTarget Controls.p37c0 Controls.p37c2 = 0
  ifTarget Controls.p37c1 Controls.p37c0 = 0
  ifTarget Controls.p37c1 Controls.p37c1 = 1
  ifTarget Controls.p37c1 Controls.p37c2 = 0
  ifTarget Controls.p37c2 Controls.p37c0 = 0
  ifTarget Controls.p37c2 Controls.p37c1 = 0
  ifTarget Controls.p37c2 Controls.p37c2 = 1

p37T4Residual : Controls.P37BrandtClass → Controls.P37BrandtClass → Nat
p37T4Residual Controls.p37c0 Controls.p37c0 = 1
p37T4Residual Controls.p37c0 Controls.p37c1 = 3
p37T4Residual Controls.p37c0 Controls.p37c2 = 3
p37T4Residual Controls.p37c1 Controls.p37c0 = 3
p37T4Residual Controls.p37c1 Controls.p37c1 = 3
p37T4Residual Controls.p37c1 Controls.p37c2 = 1
p37T4Residual Controls.p37c2 Controls.p37c0 = 3
p37T4Residual Controls.p37c2 Controls.p37c1 = 1
p37T4Residual Controls.p37c2 Controls.p37c2 = 3

identityMultiplicity : Controls.P37BrandtClass → Controls.P37BrandtClass → Nat
identityMultiplicity Controls.p37c0 Controls.p37c0 = 1
identityMultiplicity Controls.p37c0 Controls.p37c1 = 0
identityMultiplicity Controls.p37c0 Controls.p37c2 = 0
identityMultiplicity Controls.p37c1 Controls.p37c0 = 0
identityMultiplicity Controls.p37c1 Controls.p37c1 = 1
identityMultiplicity Controls.p37c1 Controls.p37c2 = 0
identityMultiplicity Controls.p37c2 Controls.p37c0 = 0
identityMultiplicity Controls.p37c2 Controls.p37c1 = 0
identityMultiplicity Controls.p37c2 Controls.p37c2 = 1

p37T2SquareRelation :
  (source target : Controls.P37BrandtClass) →
  twoStepCount target source
  ≡ p37T4Residual source target + 2 * identityMultiplicity source target
p37T2SquareRelation Controls.p37c0 Controls.p37c0 = refl
p37T2SquareRelation Controls.p37c0 Controls.p37c1 = refl
p37T2SquareRelation Controls.p37c0 Controls.p37c2 = refl
p37T2SquareRelation Controls.p37c1 Controls.p37c0 = refl
p37T2SquareRelation Controls.p37c1 Controls.p37c1 = refl
p37T2SquareRelation Controls.p37c1 Controls.p37c2 = refl
p37T2SquareRelation Controls.p37c2 Controls.p37c0 = refl
p37T2SquareRelation Controls.p37c2 Controls.p37c1 = refl
p37T2SquareRelation Controls.p37c2 Controls.p37c2 = refl

record P37PositiveControlBoundary : Set where
  field
    sourceT2PositiveNeighbourSystemConstructed : Bool
    sourceT2PositiveNeighbourSystemConstructedIsTrue :
      sourceT2PositiveNeighbourSystemConstructed ≡ true

    stackUnweightingTrivialAtP37 : Bool
    stackUnweightingTrivialAtP37IsTrue : stackUnweightingTrivialAtP37 ≡ true

    primeSquareResidualPositive : Bool
    primeSquareResidualPositiveIsTrue : primeSquareResidualPositive ≡ true

    p37ExternallyOgg : Bool
    p37ExternallyOggIsFalse : p37ExternallyOgg ≡ false

    positivityPromotedToOggSelector : Bool
    positivityPromotedToOggSelectorIsFalse : positivityPromotedToOggSelector ≡ false

canonicalP37PositiveControlBoundary : P37PositiveControlBoundary
canonicalP37PositiveControlBoundary =
  record
    { sourceT2PositiveNeighbourSystemConstructed = true
    ; sourceT2PositiveNeighbourSystemConstructedIsTrue = refl
    ; stackUnweightingTrivialAtP37 = true
    ; stackUnweightingTrivialAtP37IsTrue = refl
    ; primeSquareResidualPositive = true
    ; primeSquareResidualPositiveIsTrue = refl
    ; p37ExternallyOgg = false
    ; p37ExternallyOggIsFalse = refl
    ; positivityPromotedToOggSelector = false
    ; positivityPromotedToOggSelectorIsFalse = refl
    }
