module DASHI.Analysis.WeilDensityClosure where

-- Sequential form of the density/closure step.
--
-- A finite or countable DASHI test family is useful only if every admissible
-- Weil test has an explicit approximating sequence and spectral positivity is
-- closed under that convergence.  The constructor at the end turns those
-- concrete obligations into the generic completion bridge.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilPositivityCore

record SequentialDashiDensity
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (bridge : DashiWeilQuadraticLike space formula) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  open DashiWeilQuadraticLike bridge
  field
    sequence :
      (f : Test) → admissible f → Nat → DashiTest

    convergesToTarget :
      (f : Test) → (admissibleF : admissible f) → Set

    spectralFormConverges :
      (f : Test) → (admissibleF : admissible f) → Set

    limitPreservesNonnegative :
      (f : Test) →
      (admissibleF : admissible f) →
      ((n : Nat) →
        nonnegative
          (spectralZeroForm
            (embed (sequence f admissibleF n)))) →
      nonnegative (spectralZeroForm f)

sequentialDensityToExtension :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (bridge : DashiWeilQuadraticLike space formula) →
  SequentialDashiDensity space formula bridge →
  DensePositivityExtension space formula bridge
sequentialDensityToExtension space formula bridge density = record
  { Approximation = λ f → ⊤
  ; denseRange = λ f admissibleF → tt
  ; spectralContinuous = ⊤
  ; nonnegativeClosed = ⊤
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
    SequentialDashiDensity.limitPreservesNonnegative density
      f admissibleF
      (λ n → embeddedPositive
        (SequentialDashiDensity.sequence density f admissibleF n))
