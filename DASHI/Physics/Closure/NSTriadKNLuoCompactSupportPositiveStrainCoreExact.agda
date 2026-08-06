module DASHI.Physics.Closure.NSTriadKNLuoCompactSupportPositiveStrainCoreExact where

------------------------------------------------------------------------
-- PRIMARY AUDIT TARGET
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- DASHI CONTRIBUTION
--
-- The affine counterexample is embedded into an exact divergence-free cutoff
-- construction.  Start from the polynomial vector potential
--
--   A(x,y,z) = (0,-xz,xy),
--
-- whose curl is (2x,-y,-z).  For a scalar cutoff chi, define
--
--   u = curl(chi A).
--
-- The complete first-derivative jet of u is expanded below in terms of the
-- second jet of chi.  Its divergence cancels identically for every jet.
-- On a plateau where chi=1 and its first and second derivatives vanish, the
-- gradient is exactly diag(2,-1,-1), and the positive-strain density is 8.
--
-- A standard C-infinity compactly supported cutoff equal to one on a cube
-- turns this algebraic core into a smooth compactly supported divergence-free
-- field.  The repository does not yet contain a constructive-real bump
-- function library, so the analytic cutoff constructor is kept as the only
-- explicit boundary; the curl, divergence, plateau and positivity algebra are
-- fully checked here rather than assumed.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact as Sign
import DASHI.Physics.Closure.NSTriadKNLuoLocalizedProjectedKornAffineCounterexampleExact as Affine

record CutoffSecondJet : Set where
  constructor cutoffSecondJet
  field
    chi chiX chiY chiZ : ℚ
    chiXX chiXY chiXZ chiYY chiYZ chiZZ : ℚ

open CutoffSecondJet public

localizedCurlVelocityX : CutoffSecondJet → ℚ → ℚ → ℚ → ℚ
localizedCurlVelocityX jet x y z =
  2 * x * chi jet
  + x * y * chiY jet
  + x * z * chiZ jet

localizedCurlVelocityY : CutoffSecondJet → ℚ → ℚ → ℚ → ℚ
localizedCurlVelocityY jet x y z =
  - (x * y * chiX jet) - y * chi jet

localizedCurlVelocityZ : CutoffSecondJet → ℚ → ℚ → ℚ → ℚ
localizedCurlVelocityZ jet x y z =
  - (x * z * chiX jet) - z * chi jet

localizedCurlGradient :
  CutoffSecondJet → ℚ → ℚ → ℚ → Sign.Matrix3
localizedCurlGradient jet x y z =
  Sign.matrix3
    ( 2 * chi jet
    + 2 * x * chiX jet
    + y * chiY jet
    + x * y * chiXY jet
    + z * chiZ jet
    + x * z * chiXZ jet )
    ( 3 * x * chiY jet
    + x * y * chiYY jet
    + x * z * chiYZ jet )
    ( 3 * x * chiZ jet
    + x * y * chiYZ jet
    + x * z * chiZZ jet )

    ( - (2 * y * chiX jet)
    - x * y * chiXX jet )
    ( - (x * chiX jet)
    - x * y * chiXY jet
    - chi jet
    - y * chiY jet )
    ( - (x * y * chiXZ jet)
    - y * chiZ jet )

    ( - (2 * z * chiX jet)
    - x * z * chiXX jet )
    ( - (x * z * chiXY jet)
    - z * chiY jet )
    ( - (x * chiX jet)
    - x * z * chiXZ jet
    - chi jet
    - z * chiZ jet )

localizedCurlDivergence :
  CutoffSecondJet → ℚ → ℚ → ℚ → ℚ
localizedCurlDivergence jet x y z =
  let gradient = localizedCurlGradient jet x y z
  in
  Sign.a11 gradient + Sign.a22 gradient + Sign.a33 gradient

localizedCurlIsDivergenceFree :
  ∀ jet x y z →
  localizedCurlDivergence jet x y z ≡ 0ℚ
localizedCurlIsDivergenceFree jet x y z =
  solve
    ( chi jet ∷ chiX jet ∷ chiY jet ∷ chiZ jet
    ∷ chiXX jet ∷ chiXY jet ∷ chiXZ jet
    ∷ chiYY jet ∷ chiYZ jet ∷ chiZZ jet
    ∷ x ∷ y ∷ z ∷ [])

plateauJet : CutoffSecondJet
plateauJet =
  cutoffSecondJet
    1ℚ 0ℚ 0ℚ 0ℚ
    0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

matrix3Ext :
  ∀ {left right : Sign.Matrix3} →
  Sign.a11 left ≡ Sign.a11 right →
  Sign.a12 left ≡ Sign.a12 right →
  Sign.a13 left ≡ Sign.a13 right →
  Sign.a21 left ≡ Sign.a21 right →
  Sign.a22 left ≡ Sign.a22 right →
  Sign.a23 left ≡ Sign.a23 right →
  Sign.a31 left ≡ Sign.a31 right →
  Sign.a32 left ≡ Sign.a32 right →
  Sign.a33 left ≡ Sign.a33 right →
  left ≡ right
matrix3Ext
  {left = Sign.matrix3 l11 l12 l13 l21 l22 l23 l31 l32 l33}
  {right = Sign.matrix3 .l11 .l12 .l13 .l21 .l22 .l23 .l31 .l32 .l33}
  refl refl refl refl refl refl refl refl refl = refl
  where
  open import Agda.Builtin.Equality using (refl)

plateauCurlVelocity :
  ∀ x y z →
  localizedCurlVelocityX plateauJet x y z ≡ 2 * x
  × localizedCurlVelocityY plateauJet x y z ≡ - y
  × localizedCurlVelocityZ plateauJet x y z ≡ - z
plateauCurlVelocity x y z =
  solve (x ∷ y ∷ z ∷ []) ,
  solve (x ∷ y ∷ z ∷ []) ,
  solve (x ∷ y ∷ z ∷ [])
  where
  open import Data.Product.Base using (_×_; _,_)

plateauGradientEqualsAffine :
  ∀ x y z →
  localizedCurlGradient plateauJet x y z ≡ Affine.affineGradient
plateauGradientEqualsAffine x y z =
  matrix3Ext
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))
    (solve (x ∷ y ∷ z ∷ []))

plateauPositiveStrainDensity : ℚ → ℚ → ℚ → ℚ
plateauPositiveStrainDensity x y z =
  let gradient = localizedCurlGradient plateauJet x y z
  in
  2 * Sign.a11 gradient * Sign.a11 gradient

plateauPositiveStrainDensityIsEight :
  ∀ x y z → plateauPositiveStrainDensity x y z ≡ 8
plateauPositiveStrainDensityIsEight x y z =
  solve (x ∷ y ∷ z ∷ [])

record PositiveCoreLedger : Set where
  constructor positiveCoreLedger
  field
    coreMeasure collarContribution : ℚ
    coreMeasurePositive : 0ℚ < coreMeasure
    collarContributionNonnegative : 0ℚ ≤ collarContribution

open PositiveCoreLedger public

totalPositiveStrainResponse : PositiveCoreLedger → ℚ
totalPositiveStrainResponse ledger =
  8 * coreMeasure ledger + collarContribution ledger

coreResponsePositive :
  ∀ ledger → 0ℚ < totalPositiveStrainResponse ledger
coreResponsePositive ledger =
  let
    eightPositive : 0ℚ < 8
    eightPositive = ℚₚ.positive⁻¹ 8

    instance
      eightPositiveInstance = positive eightPositive
      corePositiveInstance = positive (coreMeasurePositive ledger)
      coreProductPositiveInstance =
        ℚₚ.pos*pos⇒pos 8 (coreMeasure ledger)
      collarNN = nonNegative (collarContributionNonnegative ledger)

    corePositive : 0ℚ < 8 * coreMeasure ledger
    corePositive = ℚₚ.positive⁻¹ (8 * coreMeasure ledger)

    withCollar :
      0ℚ + 0ℚ
      < 8 * coreMeasure ledger + collarContribution ledger
    withCollar =
      ℚₚ.+-mono-<-≤
        corePositive
        (collarContributionNonnegative ledger)
  in
  subst
    (λ left → left < totalPositiveStrainResponse ledger)
    (ℚₚ.+-identityˡ 0ℚ)
    withCollar

unitCoreLedger : PositiveCoreLedger
unitCoreLedger =
  positiveCoreLedger
    1ℚ
    0ℚ
    (ℚₚ.positive⁻¹ 1ℚ)
    ℚₚ.≤-refl

unitCoreResponseIsEight :
  totalPositiveStrainResponse unitCoreLedger ≡ 8
unitCoreResponseIsEight = solve []

record CompactSupportAuthorityBoundary : Set where
  constructor compactSupportAuthorityBoundary
  field
    vectorPotentialCurlExpanded : Set
    divergenceCancellationProved : Set
    plateauAffineCoreProved : Set
    positiveCoreDensityProved : Set
    constructiveSmoothBumpImplemented : Set

canonicalCompactSupportAuthorityBoundary : CompactSupportAuthorityBoundary
canonicalCompactSupportAuthorityBoundary =
  compactSupportAuthorityBoundary
    ⊤ ⊤ ⊤ ⊤ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
