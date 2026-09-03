module DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact where

------------------------------------------------------------------------
-- ROUND400 / PHYSICAL R290 PAIR-RATE POSITIVITY ON NONZERO OUTPUT FIBRES
--
-- R396/R397 localized the R290 reciprocal premise to exactly the pairs that
-- occur in a selected output fibre.  R399 proved the finite lattice fact that
-- a nonzero output k=p+q forces at least one input to be nonzero.
--
-- This file pays the remaining rational-order arithmetic:
--
--   * every rational mode norm-square is nonnegative;
--   * the inverse-square law makes it nonzero on a NonZeroMode;
--   * hence it is strictly positive on a NonZeroMode;
--   * positive viscosity therefore makes rho(k)=nu |k|^2 positive there;
--   * on a nonzero output fibre, rho(p)+rho(q)>0;
--   * the R291 pair rate, being the sum of two positive cell rates, is positive.
--
-- Consequently the complete R396 PairRatePositiveOn witness for a literal
-- nonzero physical output fibre is constructed, not caller-supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _*_; _<_; _≤_;
   nonNegative; ≢-nonZero)
open import Data.Rational.Base using (positive)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNNonzeroOutputInputAlternativeRound399Exact as R399

F : C3.RealField _
F = Rational.rationalRealField

zeroEqualsOneImpossible : 0ℚ ≡ 1ℚ → ⊥
zeroEqualsOneImpossible ()

normSquaredNonnegative :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (mode : Z3.FourierMode) →
  0ℚ ≤ C3.normSquared I mode
normSquaredNonnegative E I mode =
  let
    x = C3.embedInteger E (Z3.kx mode)
    y = C3.embedInteger E (Z3.ky mode)
    z = C3.embedInteger E (Z3.kz mode)

    rhsNonnegative :
      0ℚ ≤ (x * x + y * y) + z * z
    rhsNonnegative =
      Rational.addNonnegative
        (Rational.addNonnegative
          (Rational.squareNonnegative x)
          (Rational.squareNonnegative y))
        (Rational.squareNonnegative z)
  in
  subst
    (λ value → 0ℚ ≤ value)
    (sym (C3.normSquaredMeaning I mode))
    rhsNonnegative

normSquaredNonzero :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  C3.normSquared I mode ≡ 0ℚ → ⊥
normSquaredNonzero E I mode modeNonzero normZero =
  let
    inverse = C3.inverseNormSquared I mode

    zeroEqualsOne : 0ℚ ≡ 1ℚ
    zeroEqualsOne =
      trans
        (sym (ℚP.*-zeroʳ inverse))
        (trans
          (sym (cong (inverse *_) normZero))
          (C3.inverseLaw I mode modeNonzero))
  in
  zeroEqualsOneImpossible zeroEqualsOne

normSquaredPositive :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  Positive (C3.normSquared I mode)
normSquaredPositive E I mode modeNonzero =
  let
    normNN : 0ℚ ≤ C3.normSquared I mode
    normNN = normSquaredNonnegative E I mode

    normNZ : C3.normSquared I mode ≡ 0ℚ → ⊥
    normNZ = normSquaredNonzero E I mode modeNonzero

    instance
      normNNI : NonNegative (C3.normSquared I mode)
      normNNI = nonNegative normNN

      normNZI = ≢-nonZero normNZ
  in
  ℚP.nonNeg∧nonZero⇒pos (C3.normSquared I mode)

decayRateNonnegative :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  Positive (Field30.viscosity physicalSystem) →
  (mode : Z3.FourierMode) →
  0ℚ ≤ R94.physicalDecayRate physicalSystem mode
decayRateNonnegative physicalSystem viscosityPositive mode =
  let
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    nu = Field30.viscosity physicalSystem
    norm = C3.normSquared I mode

    nuNN : 0ℚ ≤ nu
    nuNN = ℚP.<⇒≤ (ℚP.positive⁻¹ nu)

    normNN : 0ℚ ≤ norm
    normNN = normSquaredNonnegative E I mode

    instance
      nuNNI : NonNegative nu
      nuNNI = nonNegative nuNN
      normNNI : NonNegative norm
      normNNI = nonNegative normNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg nu norm
  in
  ℚP.nonNegative⁻¹ (nu * norm)

decayRatePositive :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  Positive (Field30.viscosity physicalSystem) →
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  Positive (R94.physicalDecayRate physicalSystem mode)
decayRatePositive physicalSystem viscosityPositive mode modeNonzero =
  let
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    nu = Field30.viscosity physicalSystem
    norm = C3.normSquared I mode

    instance
      nuPositiveI : Positive nu
      nuPositiveI = viscosityPositive
      normPositiveI : Positive norm
      normPositiveI = normSquaredPositive E I mode modeNonzero
      productPositiveI = ℚP.pos*pos⇒pos nu norm
  in
  productPositiveI

positivePlusNonnegative :
  ∀ {left right : ℚ} →
  Positive left →
  0ℚ ≤ right →
  Positive (left + right)
positivePlusNonnegative {left} {right} leftPositive rightNN =
  let
    strict : 0ℚ < left
    strict = ℚP.positive⁻¹ left

    raw : 0ℚ + 0ℚ < left + right
    raw = ℚP.+-mono-<-≤ strict rightNN

    shifted : 0ℚ < left + right
    shifted = subst (λ lower → lower < left + right)
      (ℚP.+-identityˡ 0ℚ) raw
  in
  positive shifted

module PhysicalRate
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem)) where

  module P = R389.DoubleMixedPair physicalSystem S
  module Local = R396.LocalEnumerate physicalSystem S

  cellRatePositiveFromNonzeroOutput :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.k tau ≡ output →
    Positive (P.D.Pair.cellRate tau)
  cellRatePositiveFromNonzeroOutput output outputNonzero tau kExact =
    let
      kNonzero : Z3.NonZeroMode (Physical.k tau)
      kNonzero = record
        { Z3.notZero = λ kZero →
            Z3.notZero outputNonzero (trans (sym kExact) kZero)
        }

      qNN = decayRateNonnegative physicalSystem viscosityPositive (Physical.q tau)
      pNN = decayRateNonnegative physicalSystem viscosityPositive (Physical.p tau)
    in
    caseAlternative
      (R399.triadInputAlternativeFromNonzeroOutput tau kNonzero)
      pNN qNN
    where
    caseAlternative :
      R399.Either (Z3.NonZeroMode (Physical.p tau))
                  (Z3.NonZeroMode (Physical.q tau)) →
      0ℚ ≤ P.D.Pair.rho (Physical.p tau) →
      0ℚ ≤ P.D.Pair.rho (Physical.q tau) →
      Positive (P.D.Pair.cellRate tau)
    caseAlternative (R399.left pNonzero) pNN qNN =
      positivePlusNonnegative
        (decayRatePositive physicalSystem viscosityPositive
          (Physical.p tau) pNonzero)
        qNN
    caseAlternative (R399.right qNonzero) pNN qNN =
      let
        qPositive = decayRatePositive physicalSystem viscosityPositive
          (Physical.q tau) qNonzero
        raw : 0ℚ + 0ℚ <
          P.D.Pair.rho (Physical.p tau) + P.D.Pair.rho (Physical.q tau)
        raw = ℚP.+-mono-≤-< pNN (ℚP.positive⁻¹ (P.D.Pair.rho (Physical.q tau)))
        strict = subst
          (λ lower → lower <
            P.D.Pair.rho (Physical.p tau) + P.D.Pair.rho (Physical.q tau))
          (ℚP.+-identityˡ 0ℚ) raw
      in positive strict

  pairRatePositiveFromCellRates :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Positive (P.D.Pair.cellRate alpha) →
    Positive (P.D.Pair.cellRate beta) →
    Positive (R291.pairRate (P.physicalDoubleMixedPair alpha beta))
  pairRatePositiveFromCellRates alpha beta alphaPositive betaPositive =
    positivePlusNonnegative alphaPositive
      (ℚP.<⇒≤ (ℚP.positive⁻¹ (P.D.Pair.cellRate beta)))

  occursToCube :
    ∀ {tau items} →
    tau R396.OccursIn items → tau Cube.∈ items
  occursToCube R396.here = Cube.here refl
  occursToCube (R396.there member) = Cube.there (occursToCube member)

  allElementsHaveOutput :
    (cutoff : Nat) (output : Z3.FourierMode) →
    (tau : Physical.PhysicalTriadIncidence) →
    tau R396.OccursIn Output.physicalOutputFiber cutoff output →
    Physical.k tau ≡ output
  allElementsHaveOutput cutoff output tau member =
    Output.physicalOutputFiberSound (occursToCube member)

  pairRatesPositiveOnFromOutputExact :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    Local.PairRatePositiveOn items
  pairRatesPositiveOnFromOutputExact output outputNonzero [] allOutput =
    Local.positiveNil
  pairRatesPositiveOnFromOutputExact output outputNonzero (alpha ∷ rest) allOutput =
    Local.positiveCons headPositive tailPositive
    where
    alphaPositive : Positive (P.D.Pair.cellRate alpha)
    alphaPositive = cellRatePositiveFromNonzeroOutput
      output outputNonzero alpha (allOutput alpha R396.here)

    headPositive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (R291.pairRate (P.physicalDoubleMixedPair alpha beta))
    headPositive beta betaMember =
      pairRatePositiveFromCellRates alpha beta alphaPositive
        (cellRatePositiveFromNonzeroOutput
          output outputNonzero beta
          (allOutput beta (R396.there betaMember)))

    tailPositive : Local.PairRatePositiveOn rest
    tailPositive =
      pairRatesPositiveOnFromOutputExact output outputNonzero rest
        (λ tau member → allOutput tau (R396.there member))

  physicalOutputFibrePairRatesPositive :
    (cutoff : Nat) (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    Local.PairRatePositiveOn (Output.physicalOutputFiber cutoff output)
  physicalOutputFibrePairRatesPositive cutoff output outputNonzero =
    pairRatesPositiveOnFromOutputExact output outputNonzero
      (Output.physicalOutputFiber cutoff output)
      (allElementsHaveOutput cutoff output)

round400RationalModeNormPositiveOnNonzeroMode : Bool
round400RationalModeNormPositiveOnNonzeroMode = true

round400PositiveViscosityGivesPositiveCellRateOnNonzeroOutput : Bool
round400PositiveViscosityGivesPositiveCellRateOnNonzeroOutput = true

round400SelectedFibrePairRatePositivityConstructed : Bool
round400SelectedFibrePairRatePositivityConstructed = true

round400CallerSuppliesR290PairRatePositivity : Bool
round400CallerSuppliesR290PairRatePositivity = false
