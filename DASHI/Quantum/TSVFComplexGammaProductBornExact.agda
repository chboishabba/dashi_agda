{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVFComplexGammaProductBornExact where

-- Complex-gamma product source for the 2017 TSVF macro-robustness cut.
-- Reuses ORIGINAL rational Cayley-Dickson complex arithmetic + conjugate,
-- norm-square and norm-multiplicativity, NOT another invented complex field.
--
-- Exact achieved:
--  * the norm-square of a finite product of complex disturbed-factor
--    amplitudes equals the product of their individual Born weights;
--  * conjugating all gamma amplitudes preserves the TOTAL Born weight;
--  * multiplying by a purely imaginary unit phase preserves total Born
--    weight. Therefore a physical gamma phase must be handled at the
--    AMPLITUDE stage, before Born probabilities, not treated as a
--    nonnegative gammaWeight without provenance.
--
-- PHYSICAL SOURCE STILL OPEN: selected 2017 pointer/environment gamma_j,
-- 2017 Eq.(25) conventions, final bra, Born normalizer, nonfactorized
-- correlations, physical N-n and original (3,1)/OS clock identity.
-- Not evidence for time travel, macro entropy decrease, worlds or YM gap.
--
-- Original authors: Aharonov/Cohen/Gruss/Landsberger 2014;
-- Aharonov/Cohen/Landsberger, Entropy 2017 Eq.25;
-- original DASHI Cayley-Dickson rational complex/quaternion theorem owners.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C

-- Actual complex amplitude product, including every accumulated phase.
complexGammaProduct : List C.RationalComplex → C.RationalComplex
complexGammaProduct [] = C.oneC
complexGammaProduct (gamma ∷ gammas) =
  C._*c_ gamma (complexGammaProduct gammas)

-- Actual Born norm-square product, not a product of raw complex amplitudes.
complexGammaBornWeight : List C.RationalComplex → ℚ
complexGammaBornWeight [] = 1ℚ
complexGammaBornWeight (gamma ∷ gammas) =
  C.complexNormSq gamma * complexGammaBornWeight gammas

-- Nontrivial general finite product proof from the ORIGINAL norm theorem.
complexGammaBornWeightIsNormOfProduct :
  (gammas : List C.RationalComplex) →
  C.complexNormSq (complexGammaProduct gammas)
  ≡ complexGammaBornWeight gammas
complexGammaBornWeightIsNormOfProduct [] = solve []
complexGammaBornWeightIsNormOfProduct (gamma ∷ gammas) =
  trans
    (C.complexNormMultiplicative gamma (complexGammaProduct gammas))
    (cong (λ x → C.complexNormSq gamma * x)
      (complexGammaBornWeightIsNormOfProduct gammas))

-- Complex conjugation, the internal phase flip relevant for antiunitary
-- time-reversal constructions, leaves individual squared Born weight fixed.
complexConjugateBornNormInvariant :
  (gamma : C.RationalComplex) →
  C.complexNormSq (C.conjugateC gamma) ≡ C.complexNormSq gamma
complexConjugateBornNormInvariant (C.complex a b) =
  solve (a ∷ b ∷ [])

gammaBornProductConjugationInvariant :
  (gammas : List C.RationalComplex) →
  complexGammaBornWeight (map C.conjugateC gammas)
  ≡ complexGammaBornWeight gammas
gammaBornProductConjugationInvariant [] = refl
gammaBornProductConjugationInvariant (gamma ∷ gammas) =
  cong₂ _*_
    (complexConjugateBornNormInvariant gamma)
    (gammaBornProductConjugationInvariant gammas)

-- Full product Born weight is invariant under componentwise conjugation
-- as a DERIVED theorem: no global physical reversal operator assumed.
complexGammaProductConjugationBornInvariant :
  (gammas : List C.RationalComplex) →
  C.complexNormSq
    (complexGammaProduct (map C.conjugateC gammas))
  ≡ C.complexNormSq (complexGammaProduct gammas)
complexGammaProductConjugationBornInvariant gammas =
  trans
    (complexGammaBornWeightIsNormOfProduct
      (map C.conjugateC gammas))
    (trans
      (gammaBornProductConjugationInvariant gammas)
      (sym (complexGammaBornWeightIsNormOfProduct gammas)))

imaginaryUnitGamma : C.RationalComplex
imaginaryUnitGamma = C.complex 0ℚ 1ℚ

imaginaryUnitBornWeightIsOne :
  C.complexNormSq imaginaryUnitGamma ≡ 1ℚ
imaginaryUnitBornWeightIsOne = solve []

-- A pure phase is not a positive disturbance bias: it changes the
-- amplitude while leaving its Born weight unchanged.
imaginaryUnitGammaDoesNotChangeBornWeight :
  (gammas : List C.RationalComplex) →
  C.complexNormSq
    (complexGammaProduct (imaginaryUnitGamma ∷ gammas))
  ≡ C.complexNormSq (complexGammaProduct gammas)
imaginaryUnitGammaDoesNotChangeBornWeight gammas =
  trans
    (complexGammaBornWeightIsNormOfProduct
      (imaginaryUnitGamma ∷ gammas))
    (trans
      (solve (complexGammaBornWeight gammas ∷ []))
      (sym (complexGammaBornWeightIsNormOfProduct gammas)))

-- The 2017 Eq.(25) gamma factors are now explicitly represented by
-- complex amplitudes with norm-squared Born weights, not freely assigned
-- positive constants. Identifying these gamma factors with a real physical
-- environment, and equating them with the Nat gamma proxies in the selected
-- k-fold model, is still a distinct true physical source/normalization cut.
