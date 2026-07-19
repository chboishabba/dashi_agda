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
    SimplePoleAt : Function → Complex → Set

record GammaMellinLayer (carrier : ComplexAnalyticCarrier) : Set₁ where
  open ComplexAnalyticCarrier carrier
  field
    Test : Set
    MellinDomain : Test → Set
    MellinInversionLaw : Test → Set

    gamma : Function
    mellin : Test → Function

    gammaMeromorphic : Meromorphic gamma
    mellinHolomorphicOnDomain :
      (f : Test) → MellinDomain f → Holomorphic (mellin f)
    mellinInversion :
      (f : Test) → MellinDomain f → MellinInversionLaw f

record ZetaHalfPlaneLayer (carrier : ComplexAnalyticCarrier) : Set₁ where
  open ComplexAnalyticCarrier carrier
  field
    zetaHalfPlane : Function
    realPartGreaterThanOne : Complex → Set

    DirichletSeriesConverges : Complex → Set
    ZetaEqualsDirichletSeries : Complex → Set
    EulerProductConverges : Complex → Set
    ZetaEqualsEulerProduct : Complex → Set

    dirichletSeriesConverges :
      (s : Complex) → realPartGreaterThanOne s →
      DirichletSeriesConverges s

    zetaEqualsDirichletSeries :
      (s : Complex) → realPartGreaterThanOne s →
      ZetaEqualsDirichletSeries s

    eulerProductConverges :
      (s : Complex) → realPartGreaterThanOne s →
      EulerProductConverges s

    zetaEqualsEulerProduct :
      (s : Complex) → realPartGreaterThanOne s →
      ZetaEqualsEulerProduct s

record CompletedRiemannZeta
  (carrier : ComplexAnalyticCarrier)
  (gammaMellin : GammaMellinLayer carrier)
  (halfPlane : ZetaHalfPlaneLayer carrier) : Set₁ where
  open ComplexAnalyticCarrier carrier
  field
    zeta : Function
    xi : Function
    oneMinus : Complex → Complex

    isZero : Function → Complex → Set
    nontrivialZero : Complex → Set
    criticalLine : Complex → Set

    agreesWithHalfPlane :
      (s : Complex) →
      ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
      apply zeta s ≡
      apply (ZetaHalfPlaneLayer.zetaHalfPlane halfPlane) s

    CompletedDefinition : Complex → Set

    zetaMeromorphic : Meromorphic zeta
    simplePoleAtOne : SimplePoleAt zeta oneC
    xiEntire : Entire xi
    completedDefinition :
      (s : Complex) → CompletedDefinition s
    functionalEquation :
      (s : Complex) → apply xi s ≡ apply xi (oneMinus s)
    conjugationLaw :
      (s : Complex) → apply xi (conjC s) ≡ conjC (apply xi s)

    nontrivialZeroIsZetaZero :
      (s : Complex) → nontrivialZero s → isZero zeta s
    nontrivialZeroIsXiZero :
      (s : Complex) → nontrivialZero s → isZero xi s
    xiZeroIsNontrivialZetaZero :
      (s : Complex) → isZero xi s → nontrivialZero s

record AnalyticSubstrate : Set₁ where
  field
    carrier : ComplexAnalyticCarrier
    gammaMellin : GammaMellinLayer carrier
    halfPlane : ZetaHalfPlaneLayer carrier
    completed : CompletedRiemannZeta carrier gammaMellin halfPlane

RiemannHypothesisFor : AnalyticSubstrate → Set
RiemannHypothesisFor analytic =
  (s : ComplexAnalyticCarrier.Complex
    (AnalyticSubstrate.carrier analytic)) →
  CompletedRiemannZeta.nontrivialZero
    (AnalyticSubstrate.completed analytic) s →
  CompletedRiemannZeta.criticalLine
    (AnalyticSubstrate.completed analytic) s
