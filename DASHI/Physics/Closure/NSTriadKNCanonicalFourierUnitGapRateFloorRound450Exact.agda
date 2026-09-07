module DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact where

------------------------------------------------------------------------
-- ROUND450 / CANONICAL FOURIER NORMALIZATION -> PHYSICAL CELL-RATE FLOOR
--
-- The abstract `IntegerEmbedding` used by the finite Complex3 infrastructure
-- is intentionally scale-agnostic: it preserves zero/addition/negation but
-- does not require embed(1)=1.  Therefore the unit lattice estimate
--
--                       1 <= |k|^2   (k /= 0)
--
-- is NOT a theorem of that abstract record alone.
--
-- This file owns the exact representation boundary.  A periodic physical
-- realization supplies `CanonicalFourierUnitGap`.  R399 then says a nonzero
-- output k=p+q has p/=0 or q/=0, and R400 supplies nonnegativity of the other
-- square.  Consequently every physical cell on that output fibre obeys
--
--                 nu <= rho(p)+rho(q),
--
-- so R449 gives the uniform diagonal Cauchy ceiling 1/(2 nu).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNNonzeroOutputInputAlternativeRound399Exact as R399
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449

F : C3.RealField _
F = Rational.rationalRealField

record CanonicalFourierUnitGap
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) : Set where
  constructor canonical-fourier-unit-gap
  field
    nonzeroModeSquareAtLeastOne :
      (mode : Z3.FourierMode) →
      Z3.NonZeroMode mode →
      1ℚ ≤ C3.normSquared (Field30.physicalInverseSquare physicalSystem) mode

open CanonicalFourierUnitGap public

module PhysicalCellRateFloor
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (normalization : CanonicalFourierUnitGap physicalSystem) where

  module P = R389.DoubleMixedPair physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  nuPositive : 0ℚ < nu
  nuPositive = ℚP.positive⁻¹ nu

  nuNonnegative : 0ℚ ≤ nu
  nuNonnegative = ℚP.<⇒≤ nuPositive

  decayRateAtLeastNuOnNonzero :
    (mode : Z3.FourierMode) →
    Z3.NonZeroMode mode →
    nu ≤ P.D.Pair.rho mode
  decayRateAtLeastNuOnNonzero mode modeNonzero =
    let
      square = C3.normSquared (Field30.physicalInverseSquare physicalSystem) mode
      squareGap = nonzeroModeSquareAtLeastOne normalization mode modeNonzero
      instance
        nuNNI : NonNegative nu
        nuNNI = nonNegative nuNonnegative
      scaled : nu * 1ℚ ≤ nu * square
      scaled = ℚP.*-monoˡ-≤-nonNeg nu squareGap
    in
    subst
      (λ lower → lower ≤ P.D.Pair.rho mode)
      (ℚP.*-identityʳ nu)
      scaled

  cellRateAtLeastNuFromNonzeroOutput :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.k tau ≡ output →
    nu ≤ P.D.Pair.cellRate tau
  cellRateAtLeastNuFromNonzeroOutput output outputNonzero tau kExact =
    let
      kNonzero : Z3.NonZeroMode (Physical.k tau)
      kNonzero = record
        { Z3.notZero = λ kZero →
            Z3.notZero outputNonzero (trans (sym kExact) kZero)
        }
      pNN = R400.decayRateNonnegative physicalSystem viscosityPositive (Physical.p tau)
      qNN = R400.decayRateNonnegative physicalSystem viscosityPositive (Physical.q tau)
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
      nu ≤ P.D.Pair.cellRate tau
    caseAlternative (R399.left pNonzero) pNN qNN =
      let
        pFloor = decayRateAtLeastNuOnNonzero (Physical.p tau) pNonzero
        shifted :
          nu + 0ℚ ≤ P.D.Pair.rho (Physical.p tau) + P.D.Pair.rho (Physical.q tau)
        shifted = ℚP.+-mono-≤ pFloor qNN
      in
      subst
        (λ lower → lower ≤ P.D.Pair.cellRate tau)
        (ℚP.+-identityʳ nu)
        shifted
    caseAlternative (R399.right qNonzero) pNN qNN =
      let
        qFloor = decayRateAtLeastNuOnNonzero (Physical.q tau) qNonzero
        shifted :
          0ℚ + nu ≤ P.D.Pair.rho (Physical.p tau) + P.D.Pair.rho (Physical.q tau)
        shifted = ℚP.+-mono-≤ pNN qFloor
      in
      subst
        (λ lower → lower ≤ P.D.Pair.cellRate tau)
        (ℚP.+-identityˡ nu)
        shifted

  rateFloorCell :
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.k tau ≡ output →
    (mass : ℚ) →
    0ℚ ≤ mass →
    R449.DiagonalRateFloorCell nu
  rateFloorCell output outputNonzero tau kExact mass massNN =
    R449.diagonal-rate-floor-cell
      (P.D.Pair.cellRate tau)
      mass
      (ℚP.positive⁻¹
        (Rate.cellRatePositiveFromNonzeroOutput output outputNonzero tau kExact))
      (cellRateAtLeastNuFromNonzeroOutput output outputNonzero tau kExact)
      massNN

round450AbstractIntegerEmbeddingImpliesUnitGap : Bool
round450AbstractIntegerEmbeddingImpliesUnitGap = false

round450CanonicalUnitGapImpliesPhysicalCellRateFloor : Bool
round450CanonicalUnitGapImpliesPhysicalCellRateFloor = true

round450PhysicalFloorIsViscosity : Bool
round450PhysicalFloorIsViscosity = true

round450DiagonalCeilingBecomesOneOverTwoNu : Bool
round450DiagonalCeilingBecomesOneOverTwoNu = true

round450PackageAClosed : Bool
round450PackageAClosed = false

round450ClayPromotion : Bool
round450ClayPromotion = false

round450AbstractIntegerEmbeddingImpliesUnitGapIsFalse :
  round450AbstractIntegerEmbeddingImpliesUnitGap ≡ false
round450AbstractIntegerEmbeddingImpliesUnitGapIsFalse = refl
