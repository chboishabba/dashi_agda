module DASHI.Moonshine.EisensteinDiscriminantWeight12Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7,
-- Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Reuse the repository's theorem-derived Eisenstein transformation law to
-- construct the weight-12 modular transformation of the unnormalised modular
-- discriminant
--
--   D(tau) = E4(tau)^3 - E6(tau)^2 = 1728 Delta(tau).
--
-- This is not a new authority field for modularity.  The E4 and E6
-- transformation laws come from `eisensteinTransformation`, whose proof is
-- the explicit SL2(Z) lattice reindexing theorem already in the repository.
-- Only elementary commutative-ring/power compatibility needed to combine the
-- two transformed terms is parameterised below.
--
-- The normalization by 1/1728 and the Dedekind-eta identity Delta=eta^24 are
-- intentionally separate.  The weight-12 transformation law itself does not
-- depend on either normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein

record DiscriminantAlgebra
    (M : Eisenstein.EisensteinAnalyticModel) : Set₁ where
  field
    _-ˢ_ : Eisenstein.Scalar M → Eisenstein.Scalar M → Eisenstein.Scalar M

    squareProduct :
      (left right : Eisenstein.Scalar M) →
      Eisenstein._*ˢ_ M
        (Eisenstein._*ˢ_ M left right)
        (Eisenstein._*ˢ_ M left right)
      ≡
      Eisenstein._*ˢ_ M
        (Eisenstein._*ˢ_ M left left)
        (Eisenstein._*ˢ_ M right right)

    cubeProduct :
      (left right : Eisenstein.Scalar M) →
      Eisenstein._*ˢ_ M
        (Eisenstein._*ˢ_ M left right)
        (Eisenstein._*ˢ_ M
          (Eisenstein._*ˢ_ M left right)
          (Eisenstein._*ˢ_ M left right))
      ≡
      Eisenstein._*ˢ_ M
        (Eisenstein._*ˢ_ M left
          (Eisenstein._*ˢ_ M left left))
        (Eisenstein._*ˢ_ M right
          (Eisenstein._*ˢ_ M right right))

    fourthPowerCubedIsTwelfth :
      (value : Eisenstein.Scalar M) →
      Eisenstein._*ˢ_ M
        (Eisenstein.power M value 4)
        (Eisenstein._*ˢ_ M
          (Eisenstein.power M value 4)
          (Eisenstein.power M value 4))
      ≡ Eisenstein.power M value 12

    sixthPowerSquaredIsTwelfth :
      (value : Eisenstein.Scalar M) →
      Eisenstein._*ˢ_ M
        (Eisenstein.power M value 6)
        (Eisenstein.power M value 6)
      ≡ Eisenstein.power M value 12

    factorSubtraction :
      (factor left right : Eisenstein.Scalar M) →
      _-ˢ_
        (Eisenstein._*ˢ_ M factor left)
        (Eisenstein._*ˢ_ M factor right)
      ≡
      Eisenstein._*ˢ_ M factor (_-ˢ_ left right)

open DiscriminantAlgebra public

square :
  (M : Eisenstein.EisensteinAnalyticModel) →
  Eisenstein.Scalar M → Eisenstein.Scalar M
square M value = Eisenstein._*ˢ_ M value value

cube :
  (M : Eisenstein.EisensteinAnalyticModel) →
  Eisenstein.Scalar M → Eisenstein.Scalar M
cube M value =
  Eisenstein._*ˢ_ M value
    (Eisenstein._*ˢ_ M value value)

E4 E6 :
  (M : Eisenstein.EisensteinAnalyticModel) →
  Eisenstein.Parameter M →
  Eisenstein.Scalar M
E4 M = Eisenstein.EisensteinSeries M 4
E6 M = Eisenstein.EisensteinSeries M 6

unnormalisedDiscriminant :
  (M : Eisenstein.EisensteinAnalyticModel) →
  DiscriminantAlgebra M →
  Eisenstein.Parameter M →
  Eisenstein.Scalar M
unnormalisedDiscriminant M A tau =
  _-ˢ_ A (cube M (E4 M tau)) (square M (E6 M tau))

scaledCubeWeight4 :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : DiscriminantAlgebra M) →
  (d x : Eisenstein.Scalar M) →
  cube M (Eisenstein._*ˢ_ M (Eisenstein.power M d 4) x)
  ≡
  Eisenstein._*ˢ_ M
    (Eisenstein.power M d 12)
    (cube M x)
scaledCubeWeight4 M A d x =
  trans
    (cubeProduct A (Eisenstein.power M d 4) x)
    (cong
      (λ factor → Eisenstein._*ˢ_ M factor (cube M x))
      (fourthPowerCubedIsTwelfth A d))

scaledSquareWeight6 :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : DiscriminantAlgebra M) →
  (d x : Eisenstein.Scalar M) →
  square M (Eisenstein._*ˢ_ M (Eisenstein.power M d 6) x)
  ≡
  Eisenstein._*ˢ_ M
    (Eisenstein.power M d 12)
    (square M x)
scaledSquareWeight6 M A d x =
  trans
    (squareProduct A (Eisenstein.power M d 6) x)
    (cong
      (λ factor → Eisenstein._*ˢ_ M factor (square M x))
      (sixthPowerSquaredIsTwelfth A d))

unnormalisedDiscriminantTransformation :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : DiscriminantAlgebra M) →
  (g : Eisenstein.SL2Z) →
  (tau : Eisenstein.Parameter M) →
  unnormalisedDiscriminant M A (Eisenstein.actParameter M g tau)
  ≡
  Eisenstein._*ˢ_ M
    (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
    (unnormalisedDiscriminant M A tau)
unnormalisedDiscriminantTransformation M A g tau =
  let d = Eisenstein.denominator M g tau
  in
  trans
    (cong₂ (_-ˢ_ A)
      (cong (cube M) (Eisenstein.eisensteinTransformation M 4 g tau))
      (cong (square M) (Eisenstein.eisensteinTransformation M 6 g tau)))
    (trans
      (cong₂ (_-ˢ_ A)
        (scaledCubeWeight4 M A d (E4 M tau))
        (scaledSquareWeight6 M A d (E6 M tau)))
      (factorSubtraction A
        (Eisenstein.power M d 12)
        (cube M (E4 M tau))
        (square M (E6 M tau))))

------------------------------------------------------------------------
-- The theorem is genuinely all-SL2(Z).  In particular, any concrete S or T
-- element inhabiting `SL2Z` receives the corresponding weight-12 law without
-- a separate postulate.
------------------------------------------------------------------------

record UnnormalisedDeltaWeight12
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : DiscriminantAlgebra M) : Set₁ where
  field
    value : Eisenstein.Parameter M → Eisenstein.Scalar M
    valueIsE4CubeMinusE6Square :
      (tau : Eisenstein.Parameter M) →
      value tau ≡ unnormalisedDiscriminant M A tau
    transformsAtWeight12 :
      (g : Eisenstein.SL2Z) →
      (tau : Eisenstein.Parameter M) →
      value (Eisenstein.actParameter M g tau)
      ≡
      Eisenstein._*ˢ_ M
        (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
        (value tau)

canonicalUnnormalisedDeltaWeight12 :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : DiscriminantAlgebra M) →
  UnnormalisedDeltaWeight12 M A
canonicalUnnormalisedDeltaWeight12 M A =
  record
    { value = unnormalisedDiscriminant M A
    ; valueIsE4CubeMinusE6Square = λ tau → refl
    ; transformsAtWeight12 = unnormalisedDiscriminantTransformation M A
    }
