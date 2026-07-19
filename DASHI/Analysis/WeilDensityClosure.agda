module DASHI.Analysis.WeilDensityClosure where

-- Sequential form of the density/closure step.
--
-- A finite or countable DASHI test family is useful only if every admissible
-- Weil test has an explicit approximating sequence and spectral positivity is
-- closed under that convergence.  The constructor at the end turns those
-- concrete obligations into the generic completion bridge.

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilPositivityCore

record SequentialApproximation
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (bridge : DashiWeilQuadraticLike space formula)
  (target : WeilTestSpace.Test space) : Set₁ where
  open DashiWeilQuadraticLike bridge
  field
    sequence : Nat → DashiTest
    convergesToTarget : Set
    spectralFormConverges : Set

record SequentialDashiDensity
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (bridge : DashiWeilQuadraticLike space formula) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  open DashiWeilQuadraticLike bridge
  field
    approximation :
      (f : Test) → admissible f →
      SequentialApproximation space formula bridge f

    limitPreservesNonnegative :
      (f : Test) →
      (admissibleF : admissible f) →
      (approx : SequentialApproximation space formula bridge f) →
      ((n : Nat) →
        nonnegative
          (spectralZeroForm
            (embed
              (SequentialApproximation.sequence approx n)))) →
      nonnegative (spectralZeroForm f)

sequentialDensityToExtension :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (bridge : DashiWeilQuadraticLike space formula) →
  SequentialDashiDensity space formula bridge →
  DensePositivityExtension space formula bridge
sequentialDensityToExtension space formula bridge density = record
  { Approximation =
      SequentialApproximation space formula bridge
  ; denseRange = SequentialDashiDensity.approximation density
  ; spectralContinuous =
      (f : WeilTestSpace.Test space) →
      WeilTestSpace.admissible space f →
      Set
  ; nonnegativeClosed =
      (f : WeilTestSpace.Test space) →
      WeilTestSpace.admissible space f →
      Set
  ; extendPositive = extend
  }
  where
  extend :
    ((x : DashiWeilQuadraticLike.DashiTest bridge) →
      WeilTestSpace.nonnegative space
        (RiemannExplicitFormula.spectralZeroForm formula
          (DashiWeilQuadraticLike.embed bridge x))) →
    (f : WeilTestSpace.Test space) →
    WeilTestSpace.admissible space f →
    WeilTestSpace.nonnegative space
      (RiemannExplicitFormula.spectralZeroForm formula f)
  extend embeddedPositive f admissibleF =
    let approx = SequentialDashiDensity.approximation density f admissibleF
    in
    SequentialDashiDensity.limitPreservesNonnegative density
      f admissibleF approx
      (λ n → embeddedPositive
        (SequentialApproximation.sequence approx n))
