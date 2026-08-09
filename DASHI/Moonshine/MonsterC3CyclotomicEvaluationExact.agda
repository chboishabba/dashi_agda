module DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Give the balanced C3 phase fibre an exact cyclotomic evaluation carrier.
-- An element a+b*zeta is represented by the integer pair (a,b), with
-- zeta^2=-1-zeta.  The complete regular orbit 1+zeta+zeta^2 is proved equal
-- to zero by computation.  Thus evaluation cancellation is a theorem about a
-- nonempty fine fibre, not a declaration that the fibre is absent.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; _+_)
open import Data.Integer using (-_)

record Cyclotomic3 : Set where
  constructor c3
  field
    rationalCoefficient : ℤ
    zetaCoefficient : ℤ

open Cyclotomic3 public

zeroC3 : Cyclotomic3
zeroC3 = c3 (+ 0) (+ 0)

oneC3 : Cyclotomic3
oneC3 = c3 (+ 1) (+ 0)

zetaC3 : Cyclotomic3
zetaC3 = c3 (+ 0) (+ 1)

zetaSquaredC3 : Cyclotomic3
zetaSquaredC3 = c3 (- (+ 1)) (- (+ 1))

_+c3_ : Cyclotomic3 → Cyclotomic3 → Cyclotomic3
_+c3_ (c3 a b) (c3 c d) = c3 (a + c) (b + d)

zetaSquaredIsMinusOneMinusZeta :
  zetaSquaredC3 ≡ c3 (- (+ 1)) (- (+ 1))
zetaSquaredIsMinusOneMinusZeta = refl

completeRegularPhaseOrbit : Cyclotomic3
completeRegularPhaseOrbit = (oneC3 +c3 zetaC3) +c3 zetaSquaredC3

completeRegularPhaseOrbitCancels :
  completeRegularPhaseOrbit ≡ zeroC3
completeRegularPhaseOrbitCancels = refl

record C3PhaseMultiplicity : Set where
  constructor c3PhaseMultiplicity
  field
    fixedMultiplicity : ℤ
    zetaMultiplicity : ℤ
    zetaSquaredMultiplicity : ℤ

open C3PhaseMultiplicity public

identityEvaluation : C3PhaseMultiplicity → ℤ
identityEvaluation multiplicity =
  fixedMultiplicity multiplicity
  + zetaMultiplicity multiplicity
  + zetaSquaredMultiplicity multiplicity

generatorEvaluation : C3PhaseMultiplicity → Cyclotomic3
generatorEvaluation multiplicity =
  c3
    (fixedMultiplicity multiplicity
      + (- (zetaSquaredMultiplicity multiplicity)))
    (zetaMultiplicity multiplicity
      + (- (zetaSquaredMultiplicity multiplicity)))

residualPlusRegular : ℤ → ℤ → C3PhaseMultiplicity
residualPlusRegular residual regular =
  c3PhaseMultiplicity
    (residual + regular)
    regular
    regular

-- The specialization used by the certified Monster 3B restriction. Written
-- over exact integers, the generator evaluation computes to the residual 53.
monster3BPhaseMultiplicity : C3PhaseMultiplicity
monster3BPhaseMultiplicity =
  c3PhaseMultiplicity (+ 65663) (+ 65610) (+ 65610)

monster3BIdentityEvaluation :
  identityEvaluation monster3BPhaseMultiplicity ≡ + 196883
monster3BIdentityEvaluation = refl

monster3BGeneratorEvaluation :
  generatorEvaluation monster3BPhaseMultiplicity ≡ c3 (+ 53) (+ 0)
monster3BGeneratorEvaluation = refl

monster3BConjugatePhaseMultiplicitiesEqual :
  zetaMultiplicity monster3BPhaseMultiplicity
  ≡ zetaSquaredMultiplicity monster3BPhaseMultiplicity
monster3BConjugatePhaseMultiplicitiesEqual = refl
