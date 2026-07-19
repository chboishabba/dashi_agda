module DASHI.Analysis.WeilPositivityCore where

-- A reusable sufficient condition for universal Weil positivity.
--
-- The open research problem is reduced to constructing an exact decomposition
-- of the spectral Weil form into two independently nonnegative terms.  Once
-- such a decomposition is supplied, positivity is derived below.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula

record WeilPositiveDecomposition
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    coerciveCore : Test → Scalar
    nonnegativeRemainder : Test → Scalar

    decomposition :
      (f : Test) → admissible f →
      spectralZeroForm f
      ≡
      (coerciveCore f +S nonnegativeRemainder f)

    corePositive :
      (f : Test) → admissible f → nonnegative (coerciveCore f)

    remainderPositive :
      (f : Test) → admissible f →
      nonnegative (nonnegativeRemainder f)

decompositionImpliesWeilPositivity :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  WeilPositiveDecomposition space formula →
  (f : WeilTestSpace.Test space) →
  WeilTestSpace.admissible space f →
  WeilTestSpace.nonnegative space
    (RiemannExplicitFormula.spectralZeroForm formula f)
decompositionImpliesWeilPositivity space formula decomposition f admissibleF =
  WeilTestSpace.nonnegativeTransport space
    (≡-sym
      (WeilPositiveDecomposition.decomposition decomposition f admissibleF))
    (WeilTestSpace.nonnegativeAdd space
      (WeilPositiveDecomposition.corePositive decomposition f admissibleF)
      (WeilPositiveDecomposition.remainderPositive decomposition f admissibleF))

record DensePositivityExtension
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (bridge : DashiWeilQuadraticLike space formula) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  open DashiWeilQuadraticLike bridge
  field
    Approximation : Test → Set
    denseRange : (f : Test) → admissible f → Approximation f
    spectralContinuous : Set
    nonnegativeClosed : Set

    extendPositive :
      ((x : DashiTest) → nonnegative (spectralZeroForm (embed x))) →
      (f : Test) → admissible f → nonnegative (spectralZeroForm f)

-- Minimal interface used by the dense extension, separated from the exact
-- identification module to avoid a dependency cycle.
record DashiWeilQuadraticLike
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  field
    DashiTest : Set
    embed : DashiTest → Test
