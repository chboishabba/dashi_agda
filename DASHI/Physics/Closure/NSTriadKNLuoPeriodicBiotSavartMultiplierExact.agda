module DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact algebraic Fourier multiplier underlying
-- the periodic Biot--Savart strain operator.  For a nonzero wavevector k and
-- transverse vorticity omega,
--
--   u_hat = i (k cross omega_hat) / |k|^2,
--
-- so after factoring out the complex convention the twice-strain symbol is
--
--   2 S_ij = - |k|^-2 (k_j c_i + k_i c_j),
--   c = k cross omega.
--
-- The symbol is proved symmetric and trace-free exactly.  The vector triple
-- product is also proved, and together with an inverse-radius witness it
-- reconstructs the transverse vorticity mode.  The zero mode is represented
-- separately and mapped to zero.
--
-- This closes the finite Fourier-symbol part of P2.  It does not yet construct
-- the periodized principal-value kernel, its smooth remainder, or the full
-- Calderon--Zygmund estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact as Sign

record NonzeroVorticityMode : Set where
  constructor nonzeroVorticityMode
  field
    wavevector vorticity : Gram.Vec3
    inverseRadiusSquared : ℚ
    inverseRadiusLaw :
      Gram.normSquared wavevector * inverseRadiusSquared ≡ 1ℚ
    transverseVorticity :
      Gram.dot wavevector vorticity ≡ 0ℚ

open NonzeroVorticityMode public

curlNumerator : NonzeroVorticityMode → Gram.Vec3
curlNumerator mode =
  Gram.cross (wavevector mode) (vorticity mode)

crossCrossGeneral :
  ∀ left right →
  Gram.cross left (Gram.cross left right)
  ≡
  Gram.vec3
    ( Gram.x left * Gram.dot left right
      - Gram.normSquared left * Gram.x right )
    ( Gram.y left * Gram.dot left right
      - Gram.normSquared left * Gram.y right )
    ( Gram.z left * Gram.dot left right
      - Gram.normSquared left * Gram.z right )
crossCrossGeneral left right =
  Physical.vec3Ext
    (solve
      ( Gram.x left ∷ Gram.y left ∷ Gram.z left
      ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right ∷ []))
    (solve
      ( Gram.x left ∷ Gram.y left ∷ Gram.z left
      ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right ∷ []))
    (solve
      ( Gram.x left ∷ Gram.y left ∷ Gram.z left
      ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right ∷ []))

crossCrossTransverse :
  ∀ mode →
  Gram.cross (wavevector mode) (curlNumerator mode)
  ≡
  Physical.scaleVec3
    (- Gram.normSquared (wavevector mode))
    (vorticity mode)
crossCrossTransverse mode
  rewrite crossCrossGeneral (wavevector mode) (vorticity mode)
        | transverseVorticity mode =
  Physical.vec3Ext
    (solve
      ( Gram.normSquared (wavevector mode)
      ∷ Gram.x (vorticity mode) ∷ []))
    (solve
      ( Gram.normSquared (wavevector mode)
      ∷ Gram.y (vorticity mode) ∷ []))
    (solve
      ( Gram.normSquared (wavevector mode)
      ∷ Gram.z (vorticity mode) ∷ []))

recoveryComponent :
  ∀ mode component →
  (- inverseRadiusSquared mode)
    * (- Gram.normSquared (wavevector mode) * component)
  ≡ component
recoveryComponent mode component =
  let
    rearranged :
      (- inverseRadiusSquared mode)
        * (- Gram.normSquared (wavevector mode) * component)
      ≡
      (Gram.normSquared (wavevector mode)
        * inverseRadiusSquared mode) * component
    rearranged =
      solve
        ( inverseRadiusSquared mode
        ∷ Gram.normSquared (wavevector mode)
        ∷ component ∷ [])

    normalized :
      (Gram.normSquared (wavevector mode)
        * inverseRadiusSquared mode) * component
      ≡ 1ℚ * component
    normalized =
      cong
        (λ factor → factor * component)
        (inverseRadiusLaw mode)

    unitClosed : 1ℚ * component ≡ component
    unitClosed = solve (component ∷ [])
  in
  trans rearranged (trans normalized unitClosed)

recoverTransverseVorticity :
  ∀ mode →
  Physical.scaleVec3
    (- inverseRadiusSquared mode)
    (Gram.cross (wavevector mode) (curlNumerator mode))
  ≡ vorticity mode
recoverTransverseVorticity mode
  rewrite crossCrossTransverse mode =
  Physical.vec3Ext
    (recoveryComponent mode (Gram.x (vorticity mode)))
    (recoveryComponent mode (Gram.y (vorticity mode)))
    (recoveryComponent mode (Gram.z (vorticity mode)))

twiceStrainSymbol : NonzeroVorticityMode → Sign.Matrix3
twiceStrainSymbol mode =
  let
    k = wavevector mode
    c = curlNumerator mode
    inv = inverseRadiusSquared mode
  in
  Sign.matrix3
    (- inv * (Gram.x k * Gram.x c + Gram.x k * Gram.x c))
    (- inv * (Gram.y k * Gram.x c + Gram.x k * Gram.y c))
    (- inv * (Gram.z k * Gram.x c + Gram.x k * Gram.z c))

    (- inv * (Gram.x k * Gram.y c + Gram.y k * Gram.x c))
    (- inv * (Gram.y k * Gram.y c + Gram.y k * Gram.y c))
    (- inv * (Gram.z k * Gram.y c + Gram.y k * Gram.z c))

    (- inv * (Gram.x k * Gram.z c + Gram.z k * Gram.x c))
    (- inv * (Gram.y k * Gram.z c + Gram.z k * Gram.y c))
    (- inv * (Gram.z k * Gram.z c + Gram.z k * Gram.z c))

strainSymbol12Symmetric :
  ∀ mode →
  Sign.a12 (twiceStrainSymbol mode)
  ≡ Sign.a21 (twiceStrainSymbol mode)
strainSymbol12Symmetric mode =
  solve
    ( inverseRadiusSquared mode
    ∷ Gram.x (wavevector mode) ∷ Gram.y (wavevector mode)
    ∷ Gram.x (curlNumerator mode) ∷ Gram.y (curlNumerator mode)
    ∷ [])

strainSymbol13Symmetric :
  ∀ mode →
  Sign.a13 (twiceStrainSymbol mode)
  ≡ Sign.a31 (twiceStrainSymbol mode)
strainSymbol13Symmetric mode =
  solve
    ( inverseRadiusSquared mode
    ∷ Gram.x (wavevector mode) ∷ Gram.z (wavevector mode)
    ∷ Gram.x (curlNumerator mode) ∷ Gram.z (curlNumerator mode)
    ∷ [])

strainSymbol23Symmetric :
  ∀ mode →
  Sign.a23 (twiceStrainSymbol mode)
  ≡ Sign.a32 (twiceStrainSymbol mode)
strainSymbol23Symmetric mode =
  solve
    ( inverseRadiusSquared mode
    ∷ Gram.y (wavevector mode) ∷ Gram.z (wavevector mode)
    ∷ Gram.y (curlNumerator mode) ∷ Gram.z (curlNumerator mode)
    ∷ [])

waveDotCurlNumeratorZero :
  ∀ mode →
  Gram.dot (wavevector mode) (curlNumerator mode) ≡ 0ℚ
waveDotCurlNumeratorZero mode =
  solve
    ( Gram.x (wavevector mode)
    ∷ Gram.y (wavevector mode)
    ∷ Gram.z (wavevector mode)
    ∷ Gram.x (vorticity mode)
    ∷ Gram.y (vorticity mode)
    ∷ Gram.z (vorticity mode)
    ∷ [])

strainSymbolTraceFree :
  ∀ mode →
  Sign.a11 (twiceStrainSymbol mode)
  + Sign.a22 (twiceStrainSymbol mode)
  + Sign.a33 (twiceStrainSymbol mode)
  ≡ 0ℚ
strainSymbolTraceFree mode =
  solve
    ( inverseRadiusSquared mode
    ∷ Gram.x (wavevector mode)
    ∷ Gram.y (wavevector mode)
    ∷ Gram.z (wavevector mode)
    ∷ Gram.x (vorticity mode)
    ∷ Gram.y (vorticity mode)
    ∷ Gram.z (vorticity mode)
    ∷ [])

zeroModeTwiceStrain : Sign.Matrix3
zeroModeTwiceStrain =
  Sign.matrix3
    0ℚ 0ℚ 0ℚ
    0ℚ 0ℚ 0ℚ
    0ℚ 0ℚ 0ℚ

data PeriodicModeKind : Set where
  zeroMode nonzeroMode : PeriodicModeKind

record PeriodicBiotSavartBoundary : Set where
  constructor periodicBiotSavartBoundary
  field
    nonzeroFourierSymbolClosed : Set
    zeroModeSeparated : Set
    symbolSymmetricAndTraceFree : Set
    principalValueKernelConstructed : Set
    calderonZygmundEstimateProved : Set

canonicalPeriodicBiotSavartBoundary : PeriodicBiotSavartBoundary
canonicalPeriodicBiotSavartBoundary =
  periodicBiotSavartBoundary ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
