module DASHI.Analysis.RiemannAnalyticSubstrate where

-- Analytic ownership ladder required before the explicit formula can refer to
-- the genuine Riemann zeta function.  These records are interfaces for real
-- constructions; no field is discharged by the existing Abel samples.

open import Agda.Builtin.Equality using (_≡_)

record ComplexAnalyticCarrier : Set₁ where
  field
    Complex Real : Set
    zeroC oneC : Complex
    _+C_ _*C_ : Complex → Complex → Complex
    negC conjC : Complex → Complex
    realPart imaginaryPart : Complex → Real

    Function : Set
    apply : Function → Complex → Complex
    Holomorphic : Function → Set
    Entire : Function → Set
    Meromorphic : Function → Set

record GammaMellinLayer (carrier : ComplexAnalyticCarrier) : Set₁ where
  open ComplexAnalyticCarrier carrier
  field
    Test : Set
    gamma : Function
    mellin : Test → Function
    gammaMeromorphic : Meromorphic gamma
    mellinHolomorphicOnDomain : (f : Test) → Set
    mellinInversion : (f : Test) → Set

record ZetaHalfPlaneLayer (carrier : ComplexAnalyticCarrier) : Set₁ where
  open ComplexAnalyticCarrier carrier
  field
    zetaHalfPlane : Function
    realPartGreaterThanOne : Complex → Set
    dirichletSeriesConverges :
      (s : Complex) → realPartGreaterThanOne s → Set
    zetaEqualsDirichletSeries :
      (s : Complex) → realPartGreaterThanOne s → Set
    eulerProductConverges :
      (s : Complex) → realPartGreaterThanOne s → Set
    zetaEqualsEulerProduct :
      (s : Complex) → realPartGreaterThanOne s → Set

record CompletedRiemannZeta
  (carrier : ComplexAnalyticCarrier)
  (gammaMellin : GammaMellinLayer carrier)
  (halfPlane : ZetaHalfPlaneLayer carrier) : Set₁ where
  open ComplexAnalyticCarrier carrier
  field
    zeta : Function
    xi : Function
    oneMinus : Complex → Complex

    agreesWithHalfPlane :
      (s : Complex) →
      ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
      apply zeta s ≡
      apply (ZetaHalfPlaneLayer.zetaHalfPlane halfPlane) s

    zetaMeromorphic : Meromorphic zeta
    simplePoleAtOne : Set
    xiEntire : Entire xi
    completedDefinition : (s : Complex) → Set
    functionalEquation :
      (s : Complex) → apply xi s ≡ apply xi (oneMinus s)
    conjugationLaw :
      (s : Complex) → apply xi (conjC s) ≡ conjC (apply xi s)
    nontrivialZetaZerosMatchXiZeros : Set

record AnalyticSubstrate : Set₁ where
  field
    carrier : ComplexAnalyticCarrier
    gammaMellin : GammaMellinLayer carrier
    halfPlane : ZetaHalfPlaneLayer carrier
    completed : CompletedRiemannZeta carrier gammaMellin halfPlane
