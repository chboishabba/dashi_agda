module DASHI.Moonshine.JInvariantBishopLatticeDenominatorCoercivityExact where

------------------------------------------------------------------------
-- DIVISION-FREE COERCIVITY OF THE UPPER-HALF-PLANE LATTICE MAP
--
-- For tau=x+iy and z=m*tau+n, all integer coordinates are first embedded in
-- the same Bishop real carrier.  The exact identities
--
--   Im z = m y
--   y Re z - x Im z = n y
--
-- combine with the two-dimensional Cauchy identity to give
--
--   y^2 (m^2+n^2)
--     <= (1+x^2+y^2) normSq(z).
--
-- No square root, real division, or lattice-shell estimate is used here.
------------------------------------------------------------------------

open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

square : BishopReal.ℝ → BishopReal.ℝ
square = Norm.square

twoDimensionalCauchy :
  (a b u v : BishopReal.ℝ) →
  BishopReal._≤_
    (square
      (BishopReal._+_
        (BishopReal._*_ a u)
        (BishopReal._*_ b v)))
    (BishopReal._*_
      (BishopReal._+_ (square a) (square b))
      (BishopReal._+_ (square u) (square v)))
twoDimensionalCauchy a b u v =
  let
    gap =
      BishopReal._-_
        (BishopReal._*_ a v)
        (BishopReal._*_ b u)

    gapSquareNN =
      BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative gap)

    gapIdentity :
      BishopReal._≃_
        (square gap)
        (BishopReal._-_
          (BishopReal._*_
            (BishopReal._+_ (square a) (square b))
            (BishopReal._+_ (square u) (square v)))
          (square
            (BishopReal._+_
              (BishopReal._*_ a u)
              (BishopReal._*_ b v))))
    gapIdentity =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ a′ b′ u′ v′ →
          ((a′ ⊗ v′) ⊖ (b′ ⊗ u′))
            ⊗ ((a′ ⊗ v′) ⊖ (b′ ⊗ u′))
          ⊜
          (((a′ ⊗ a′) ⊕ (b′ ⊗ b′))
            ⊗ ((u′ ⊗ u′) ⊕ (v′ ⊗ v′)))
          ⊖
          (((a′ ⊗ u′) ⊕ (b′ ⊗ v′))
            ⊗ ((a′ ⊗ u′) ⊕ (b′ ⊗ v′))))
        BishopP.≃-refl a b u v
  in
  BishopP.0≤y-x⇒x≤y
    (BishopP.≤-respʳ-≃ gapIdentity gapSquareNN)

denominatorRealCoordinate :
  (point : Lattice.LatticePoint) →
  (tau : Complex.BishopComplex) →
  BishopReal._≃_
    (Complex.re (Kernel.latticeDenominator point tau))
    (BishopReal._+_
      (BishopReal._*_
        (Kernel.embedInteger (Lattice.horizontal point))
        (Complex.re tau))
      (Kernel.embedInteger (Lattice.vertical point)))
denominatorRealCoordinate point tau =
  BishopP.≃-refl

denominatorImagCoordinate :
  (point : Lattice.LatticePoint) →
  (tau : Complex.BishopComplex) →
  BishopReal._≃_
    (Complex.im (Kernel.latticeDenominator point tau))
    (BishopReal._*_
      (Kernel.embedInteger (Lattice.horizontal point))
      (Complex.im tau))
denominatorImagCoordinate point tau =
  BishopP.+-identityʳ
    (BishopReal._*_
      (Kernel.embedInteger (Lattice.horizontal point))
      (Complex.im tau))

dualCoordinateIdentity :
  (point : Lattice.LatticePoint) →
  (tau : Complex.BishopComplex) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._*_
        (Complex.im tau)
        (Complex.re (Kernel.latticeDenominator point tau)))
      (BishopReal._*_
        (Complex.re tau)
        (Complex.im (Kernel.latticeDenominator point tau))))
    (BishopReal._*_
      (Kernel.embedInteger (Lattice.vertical point))
      (Complex.im tau))
dualCoordinateIdentity point tau =
  let
    m = Kernel.embedInteger (Lattice.horizontal point)
    n = Kernel.embedInteger (Lattice.vertical point)
    x = Complex.re tau
    y = Complex.im tau

    reLaw = denominatorRealCoordinate point tau
    imLaw = denominatorImagCoordinate point tau
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.*-cong BishopP.≃-refl reLaw)
      (BishopP.-‿cong
        (BishopP.*-cong BishopP.≃-refl imLaw)))
    (let open BishopP.ℝ-Solver in
      solve 4
        (λ m′ n′ x′ y′ →
          (y′ ⊗ ((m′ ⊗ x′) ⊕ n′))
            ⊖ (x′ ⊗ (m′ ⊗ y′))
          ⊜ n′ ⊗ y′)
        BishopP.≃-refl m n x y)

horizontalCoordinateBound :
  (point : Lattice.LatticePoint) →
  (tau : Complex.BishopComplex) →
  BishopReal._≤_
    (square
      (BishopReal._*_
        (Kernel.embedInteger (Lattice.horizontal point))
        (Complex.im tau)))
    (Norm.normSqC (Kernel.latticeDenominator point tau))
horizontalCoordinateBound point tau =
  BishopP.≤-respˡ-≃
    (BishopP.*-cong
      (BishopP.≃-symm (denominatorImagCoordinate point tau))
      (BishopP.≃-symm (denominatorImagCoordinate point tau)))
    (Norm.imagSquareBelowNormSq
      (Kernel.latticeDenominator point tau))

verticalCoordinateBound :
  (point : Lattice.LatticePoint) →
  (tau : Complex.BishopComplex) →
  BishopReal._≤_
    (square
      (BishopReal._*_
        (Kernel.embedInteger (Lattice.vertical point))
        (Complex.im tau)))
    (BishopReal._*_
      (BishopReal._+_
        (square (Complex.im tau))
        (square (Complex.re tau)))
      (Norm.normSqC (Kernel.latticeDenominator point tau)))
verticalCoordinateBound point tau =
  let
    z = Kernel.latticeDenominator point tau
    x = Complex.re tau
    y = Complex.im tau
    cross =
      BishopReal._-_
        (BishopReal._*_ y (Complex.re z))
        (BishopReal._*_ x (Complex.im z))

    cauchy =
      twoDimensionalCauchy
        y (BishopReal.- x)
        (Complex.re z) (Complex.im z)

    crossAsCauchyLeft :
      BishopReal._≃_
        cross
        (BishopReal._+_
          (BishopReal._*_ y (Complex.re z))
          (BishopReal._*_
            (BishopReal.- x)
            (Complex.im z)))
    crossAsCauchyLeft =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ y′ x′ u′ v′ →
          (y′ ⊗ u′) ⊖ (x′ ⊗ v′)
          ⊜
          (y′ ⊗ u′) ⊕ ((⊝ x′) ⊗ v′))
        BishopP.≃-refl y x (Complex.re z) (Complex.im z)

    coefficientNormalize :
      BishopReal._≃_
        (BishopReal._+_
          (square y)
          (square (BishopReal.- x)))
        (BishopReal._+_ (square y) (square x))
    coefficientNormalize =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ y′ x′ →
          (y′ ⊗ y′) ⊕ ((⊝ x′) ⊗ (⊝ x′))
          ⊜
          (y′ ⊗ y′) ⊕ (x′ ⊗ x′))
        BishopP.≃-refl y x

    crossBound :
      BishopReal._≤_
        (square cross)
        (BishopReal._*_
          (BishopReal._+_ (square y) (square x))
          (Norm.normSqC z))
    crossBound =
      BishopP.≤-respʳ-≃
        (BishopP.*-cong
          coefficientNormalize
          BishopP.≃-refl)
        (BishopP.≤-respˡ-≃
          (BishopP.*-cong
            crossAsCauchyLeft
            crossAsCauchyLeft)
          cauchy)

    dualLaw = dualCoordinateIdentity point tau
  in
  BishopP.≤-respˡ-≃
    (BishopP.*-cong
      (BishopP.≃-symm dualLaw)
      (BishopP.≃-symm dualLaw))
    crossBound

coercivityFactor :
  Complex.BishopComplex →
  BishopReal.ℝ
coercivityFactor tau =
  BishopReal._+_
    BishopReal.1ℝ
    (BishopReal._+_
      (square (Complex.im tau))
      (square (Complex.re tau)))

latticeDenominatorCoercivity :
  (point : Lattice.LatticePoint) →
  (tau : Complex.BishopComplex) →
  BishopReal._≤_
    (BishopReal._*_
      (square (Complex.im tau))
      (BishopReal._+_
        (square (Kernel.embedInteger (Lattice.horizontal point)))
        (square (Kernel.embedInteger (Lattice.vertical point)))))
    (BishopReal._*_
      (coercivityFactor tau)
      (Norm.normSqC (Kernel.latticeDenominator point tau)))
latticeDenominatorCoercivity point tau =
  let
    m = Kernel.embedInteger (Lattice.horizontal point)
    n = Kernel.embedInteger (Lattice.vertical point)
    y = Complex.im tau
    norm = Norm.normSqC (Kernel.latticeDenominator point tau)
    coefficient =
      BishopReal._+_ (square y) (square (Complex.re tau))

    summed =
      BishopP.+-mono-≤
        (horizontalCoordinateBound point tau)
        (verticalCoordinateBound point tau)

    leftNormalize :
      BishopReal._≃_
        (BishopReal._+_
          (square (BishopReal._*_ m y))
          (square (BishopReal._*_ n y)))
        (BishopReal._*_
          (square y)
          (BishopReal._+_ (square m) (square n)))
    leftNormalize =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ m′ n′ y′ →
          ((m′ ⊗ y′) ⊗ (m′ ⊗ y′))
          ⊕ ((n′ ⊗ y′) ⊗ (n′ ⊗ y′))
          ⊜
          (y′ ⊗ y′)
          ⊗ ((m′ ⊗ m′) ⊕ (n′ ⊗ n′)))
        BishopP.≃-refl m n y

    rightNormalize :
      BishopReal._≃_
        (BishopReal._+_
          norm
          (BishopReal._*_ coefficient norm))
        (BishopReal._*_
          (coercivityFactor tau)
          norm)
    rightNormalize =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ c z →
          z ⊕ (c ⊗ z)
          ⊜ (Κ 1ℚᵘ ⊕ c) ⊗ z)
        BishopP.≃-refl coefficient norm
  in
  BishopP.≤-respʳ-≃ rightNormalize
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm leftNormalize)
      summed)
