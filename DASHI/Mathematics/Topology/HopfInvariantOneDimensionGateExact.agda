module DASHI.Mathematics.Topology.HopfInvariantOneDimensionGateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Heinz Hopf,
-- "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche",
-- Mathematische Annalen 104 (1931), 637--665.
-- DOI: 10.1007/BF01457962.
--
-- J. F. Adams,
-- "On the Non-Existence of Elements of Hopf Invariant One",
-- Annals of Mathematics 72 (1960), 20--104.
-- DOI: 10.2307/1970147.
--
-- John C. Baez,
-- "The Octonions".
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- DASHI CONTRIBUTION
--
-- Encode the exact finite coincidence between the classical composition-
-- algebra dimensions and the dimensions appearing in the Hopf-invariant-one
-- theorem.  The equivalence below is only an equivalence between two finite
-- indexed data types.  It does not prove Adams's theorem, construct homotopy
-- groups, or prove that a displayed algebraic map is a locally trivial fibre
-- bundle.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Mathematics.Algebra.HurwitzFrobeniusLawProfileExact
  using (HurwitzDimension; hurwitz1; hurwitz2; hurwitz4; hurwitz8)

data HopfInvariantOneDimension : Nat → Set where
  hopf1 : HopfInvariantOneDimension 1
  hopf2 : HopfInvariantOneDimension 2
  hopf4 : HopfInvariantOneDimension 4
  hopf8 : HopfInvariantOneDimension 8

hurwitzDimensionToHopfDimension : ∀ {n} →
  HurwitzDimension n → HopfInvariantOneDimension n
hurwitzDimensionToHopfDimension hurwitz1 = hopf1
hurwitzDimensionToHopfDimension hurwitz2 = hopf2
hurwitzDimensionToHopfDimension hurwitz4 = hopf4
hurwitzDimensionToHopfDimension hurwitz8 = hopf8

hopfDimensionToHurwitzDimension : ∀ {n} →
  HopfInvariantOneDimension n → HurwitzDimension n
hopfDimensionToHurwitzDimension hopf1 = hurwitz1
hopfDimensionToHurwitzDimension hopf2 = hurwitz2
hopfDimensionToHurwitzDimension hopf4 = hurwitz4
hopfDimensionToHurwitzDimension hopf8 = hurwitz8

hopfInvariantOneExcludesSixteen : HopfInvariantOneDimension 16 → ⊥
hopfInvariantOneExcludesSixteen ()

record ClassicalHopfSphereDimensions : Set where
  constructor hopfSphereDimensions
  field
    algebraDimension : Nat
    fibreSphereDimension : Nat
    totalSphereDimension : Nat
    baseSphereDimension : Nat

realHopfDimensions : ClassicalHopfSphereDimensions
realHopfDimensions = hopfSphereDimensions 1 0 1 1

complexHopfDimensions : ClassicalHopfSphereDimensions
complexHopfDimensions = hopfSphereDimensions 2 1 3 2

quaternionHopfDimensions : ClassicalHopfSphereDimensions
quaternionHopfDimensions = hopfSphereDimensions 4 3 7 4

octonionHopfDimensions : ClassicalHopfSphereDimensions
octonionHopfDimensions = hopfSphereDimensions 8 7 15 8
