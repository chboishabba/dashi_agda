module DASHI.Physics.Closure.NSTriadKNLuoStrainKernelSphericalMeanZeroExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- DASHI CONTRIBUTION
--
-- Round Twenty-One proved a coordinate cubature cancellation for the physical
-- strain-kernel angular numerator
--
--   K(r,omega) = (r cross omega) tensor r
--                + r tensor (r cross omega).
--
-- This module proves the full algebraic spherical-mean cancellation from the
-- isotropic second-moment identities
--
--   <r_i r_j> = m delta_ij.
--
-- Every one of the nine averaged matrix entries is expanded in literal second
-- moments and shown to vanish.  No value of m or surface-area normalization is
-- needed.  The remaining analytic interface is therefore sharply reduced to
-- constructing the spherical integration functional and proving its standard
-- isotropic moment law; the kernel cancellation itself is closed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact as Matrix
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact as Angular

record SecondMomentMatrix : Set where
  constructor secondMomentMatrix
  field
    xx xy xz : ℚ
    yx yy yz : ℚ
    zx zy zz : ℚ

open SecondMomentMatrix public

record IsotropicSecondMoment : Set where
  constructor isotropicSecondMoment
  field
    moments : SecondMomentMatrix
    mass : ℚ

    xxMeaning : xx moments ≡ mass
    yyMeaning : yy moments ≡ mass
    zzMeaning : zz moments ≡ mass

    xyZero : xy moments ≡ 0ℚ
    xzZero : xz moments ≡ 0ℚ
    yxZero : yx moments ≡ 0ℚ
    yzZero : yz moments ≡ 0ℚ
    zxZero : zx moments ≡ 0ℚ
    zyZero : zy moments ≡ 0ℚ

open IsotropicSecondMoment public

averagedKernelNumerator :
  IsotropicSecondMoment → Gram.Vec3 → Matrix.Matrix3
averagedKernelNumerator isotropy vorticity =
  let
    moment = moments isotropy
    wx = Gram.x vorticity
    wy = Gram.y vorticity
    wz = Gram.z vorticity
  in
  Matrix.matrix3
    (2 * (xy moment * wz - xz moment * wy))
    (yy moment * wz - yz moment * wy
      + xz moment * wx - xx moment * wz)
    (yz moment * wz - zz moment * wy
      + xx moment * wy - xy moment * wx)

    (yy moment * wz - zy moment * wy
      + zx moment * wx - xx moment * wz)
    (2 * (yz moment * wx - yx moment * wz))
    (zz moment * wx - zx moment * wz
      + yx moment * wy - yy moment * wx)

    (zy moment * wz - zz moment * wy
      + xx moment * wy - yx moment * wx)
    (zz moment * wx - xz moment * wz
      + xy moment * wy - yy moment * wx)
    (2 * (zx moment * wy - zy moment * wx))

sphericalKernelMeanZero :
  ∀ isotropy vorticity →
  averagedKernelNumerator isotropy vorticity ≡ Angular.zeroMatrix
sphericalKernelMeanZero isotropy vorticity
  rewrite xxMeaning isotropy
        | yyMeaning isotropy
        | zzMeaning isotropy
        | xyZero isotropy
        | xzZero isotropy
        | yxZero isotropy
        | yzZero isotropy
        | zxZero isotropy
        | zyZero isotropy =
  Angular.matrixExt
    (solve values) (solve values) (solve values)
    (solve values) (solve values) (solve values)
    (solve values) (solve values) (solve values)
  where
  values =
    mass isotropy
    ∷ Gram.x vorticity
    ∷ Gram.y vorticity
    ∷ Gram.z vorticity
    ∷ []

record SphericalMeanAuthorityBoundary : Set where
  constructor sphericalMeanAuthorityBoundary
  field
    allNineMomentExpansionsImplemented : Set
    isotropicMomentImpliesMeanZeroProved : Set
    sphericalIntegrationFunctionalConstructed : Set
    isotropicMomentLawProvedAnalytically : Set
    periodicPrincipalValueDistributionConstructed : Set

canonicalSphericalMeanAuthorityBoundary : SphericalMeanAuthorityBoundary
canonicalSphericalMeanAuthorityBoundary =
  sphericalMeanAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
