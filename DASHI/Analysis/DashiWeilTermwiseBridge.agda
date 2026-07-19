module DASHI.Analysis.DashiWeilTermwiseBridge where

-- Term-by-term bridge from DASHI arithmetic owners to the classical Riemann
-- explicit formula.  This removes the possibility of satisfying the bridge
-- with one unexplained global equality.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.DashiWeilExactIdentification

cong₂ :
  {A B C : Set} →
  (op : A → B → C) →
  {x x′ : A} {y y′ : B} →
  x ≡ x′ → y ≡ y′ → op x y ≡ op x′ y′
cong₂ op refl refl = refl

record DashiWeilTermwiseBridge
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    DashiTest : Set
    embed : DashiTest → Test
    embeddedAdmissible : (x : DashiTest) → admissible (embed x)

    dashiPrimePowerTerm : DashiTest → Scalar
    dashiArchimedeanTerm : DashiTest → Scalar
    dashiPoleTerm : DashiTest → Scalar
    dashiTrivialZeroTerm : DashiTest → Scalar
    dashiQuadratic : DashiTest → Scalar

    dashiDecomposition :
      (x : DashiTest) →
      dashiQuadratic x
      ≡
      (dashiPrimePowerTerm x +S
       (dashiArchimedeanTerm x +S
        (dashiPoleTerm x +S dashiTrivialZeroTerm x)))

    primePowerAgreement :
      (x : DashiTest) →
      dashiPrimePowerTerm x ≡ primePowerTerm (embed x)

    archimedeanAgreement :
      (x : DashiTest) →
      dashiArchimedeanTerm x ≡ archimedeanGammaTerm (embed x)

    poleAgreement :
      (x : DashiTest) →
      dashiPoleTerm x ≡ poleTerm (embed x)

    trivialZeroAgreement :
      (x : DashiTest) →
      dashiTrivialZeroTerm x ≡ trivialZeroTerm (embed x)

    dashiCoercive :
      (x : DashiTest) → nonnegative (dashiQuadratic x)

termSumAgreement :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (bridge : DashiWeilTermwiseBridge space formula) →
  (x : DashiWeilTermwiseBridge.DashiTest bridge) →
  WeilTestSpace._+S_ space
    (DashiWeilTermwiseBridge.dashiPrimePowerTerm bridge x)
    (WeilTestSpace._+S_ space
      (DashiWeilTermwiseBridge.dashiArchimedeanTerm bridge x)
      (WeilTestSpace._+S_ space
        (DashiWeilTermwiseBridge.dashiPoleTerm bridge x)
        (DashiWeilTermwiseBridge.dashiTrivialZeroTerm bridge x)))
  ≡
  WeilTestSpace._+S_ space
    (RiemannExplicitFormula.primePowerTerm formula
      (DashiWeilTermwiseBridge.embed bridge x))
    (WeilTestSpace._+S_ space
      (RiemannExplicitFormula.archimedeanGammaTerm formula
        (DashiWeilTermwiseBridge.embed bridge x))
      (WeilTestSpace._+S_ space
        (RiemannExplicitFormula.poleTerm formula
          (DashiWeilTermwiseBridge.embed bridge x))
        (RiemannExplicitFormula.trivialZeroTerm formula
          (DashiWeilTermwiseBridge.embed bridge x))))
termSumAgreement space formula bridge x =
  cong₂ (WeilTestSpace._+S_ space)
    (DashiWeilTermwiseBridge.primePowerAgreement bridge x)
    (cong₂ (WeilTestSpace._+S_ space)
      (DashiWeilTermwiseBridge.archimedeanAgreement bridge x)
      (cong₂ (WeilTestSpace._+S_ space)
        (DashiWeilTermwiseBridge.poleAgreement bridge x)
        (DashiWeilTermwiseBridge.trivialZeroAgreement bridge x)))

termwiseArithmeticAgreement :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (bridge : DashiWeilTermwiseBridge space formula) →
  (x : DashiWeilTermwiseBridge.DashiTest bridge) →
  DashiWeilTermwiseBridge.dashiQuadratic bridge x
  ≡
  RiemannExplicitFormula.arithmeticForm formula
    (DashiWeilTermwiseBridge.embed bridge x)
termwiseArithmeticAgreement space formula bridge x =
  ≡-trans
    (DashiWeilTermwiseBridge.dashiDecomposition bridge x)
    (≡-trans
      (termSumAgreement space formula bridge x)
      (≡-sym
        (RiemannExplicitFormula.arithmeticDecomposition formula
          (DashiWeilTermwiseBridge.embed bridge x)
          (DashiWeilTermwiseBridge.embeddedAdmissible bridge x))))

termwiseToExactIdentification :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  DashiWeilTermwiseBridge space formula →
  DashiWeilQuadratic space formula
termwiseToExactIdentification space formula bridge = record
  { DashiTest = DashiWeilTermwiseBridge.DashiTest bridge
  ; dashiQuadratic = DashiWeilTermwiseBridge.dashiQuadratic bridge
  ; embed = DashiWeilTermwiseBridge.embed bridge
  ; embeddedAdmissible =
      DashiWeilTermwiseBridge.embeddedAdmissible bridge
  ; dashiArithmeticAgreement =
      termwiseArithmeticAgreement space formula bridge
  ; dashiCoercive = DashiWeilTermwiseBridge.dashiCoercive bridge
  }
