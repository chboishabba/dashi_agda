module DASHI.Moonshine.Monster3BFiniteHeisenbergCommutantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Prove the concrete combinatorial core of finite Stone--von Neumann
-- irreducibility on X = F_3^6.  The six coordinate modulations separate every
-- pair of distinct basis states.  Hence a matrix commuting with all
-- modulations has zero off-diagonal coefficients.  Commutation with all
-- translations then makes every diagonal coefficient equal.  Therefore the
-- full Schrödinger commutant is scalar at matrix-coefficient level.
--
-- This module does not assume a 65610-dimensional Monster basis.  It proves
-- the actual 729-state Heisenberg lemma consumed by the later recognition map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; sym)
open import Relation.Nullary using (Dec; yes; no)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

------------------------------------------------------------------------
-- Decidable equality and coordinate separation on X6.
------------------------------------------------------------------------

tritDecidableEquality : (left right : Trit) → Dec (left ≡ right)
tritDecidableEquality neg neg = yes refl
tritDecidableEquality neg zer = no (λ ())
tritDecidableEquality neg pos = no (λ ())
tritDecidableEquality zer neg = no (λ ())
tritDecidableEquality zer zer = yes refl
tritDecidableEquality zer pos = no (λ ())
tritDecidableEquality pos neg = no (λ ())
tritDecidableEquality pos zer = no (λ ())
tritDecidableEquality pos pos = yes refl

coordinateSeparation :
  (left right : H.X6) →
  left ≢ right →
  Σ H.Axis6
    (λ axis → H.coordinate axis left ≢ H.coordinate axis right)
coordinateSeparation
  (H.x6 l0 l1 l2 l3 l4 l5)
  (H.x6 r0 r1 r2 r3 r4 r5)
  distinct
  with tritDecidableEquality l0 r0
... | no differs = H.axis0 , differs
... | yes refl with tritDecidableEquality l1 r1
...   | no differs = H.axis1 , differs
...   | yes refl with tritDecidableEquality l2 r2
...     | no differs = H.axis2 , differs
...     | yes refl with tritDecidableEquality l3 r3
...       | no differs = H.axis3 , differs
...       | yes refl with tritDecidableEquality l4 r4
...         | no differs = H.axis4 , differs
...         | yes refl with tritDecidableEquality l5 r5
...           | no differs = H.axis5 , differs
...           | yes refl = ⊥-elim (distinct refl)

------------------------------------------------------------------------
-- The full translation group and its simple transitivity.
------------------------------------------------------------------------

subtract3 : Trit → Trit → Trit
subtract3 target source = target H.+3 H.negate3 source

subtract3Restores :
  (target source : Trit) →
  subtract3 target source H.+3 source ≡ target
subtract3Restores neg neg = refl
subtract3Restores neg zer = refl
subtract3Restores neg pos = refl
subtract3Restores zer neg = refl
subtract3Restores zer zer = refl
subtract3Restores zer pos = refl
subtract3Restores pos neg = refl
subtract3Restores pos zer = refl
subtract3Restores pos pos = refl

translateBy : H.X6 → H.X6 → H.X6
translateBy shift state =
  H.x6
    (H.x0 shift H.+3 H.x0 state)
    (H.x1 shift H.+3 H.x1 state)
    (H.x2 shift H.+3 H.x2 state)
    (H.x3 shift H.+3 H.x3 state)
    (H.x4 shift H.+3 H.x4 state)
    (H.x5 shift H.+3 H.x5 state)

difference6 : H.X6 → H.X6 → H.X6
difference6 target source =
  H.x6
    (subtract3 (H.x0 target) (H.x0 source))
    (subtract3 (H.x1 target) (H.x1 source))
    (subtract3 (H.x2 target) (H.x2 source))
    (subtract3 (H.x3 target) (H.x3 source))
    (subtract3 (H.x4 target) (H.x4 source))
    (subtract3 (H.x5 target) (H.x5 source))

difference6Restores :
  (target source : H.X6) →
  translateBy (difference6 target source) source ≡ target
difference6Restores
  (H.x6 t0 t1 t2 t3 t4 t5)
  (H.x6 s0 s1 s2 s3 s4 s5)
  rewrite subtract3Restores t0 s0
        | subtract3Restores t1 s1
        | subtract3Restores t2 s2
        | subtract3Restores t3 s3
        | subtract3Restores t4 s4
        | subtract3Restores t5 s5 = refl

origin : H.X6
origin = H.x6 zer zer zer zer zer zer

------------------------------------------------------------------------
-- Matrix coefficient formulation of the commutant.
------------------------------------------------------------------------

record SchrodingerCommutantMatrix : Set₁ where
  field
    Scalar : Set
    zeroScalar : Scalar
    phaseAction : Trit → Scalar → Scalar
    entry : H.X6 → H.X6 → Scalar

    modulationCommutationCoefficient :
      (axis : H.Axis6) →
      (left right : H.X6) →
      phaseAction (H.modulationExponent axis left) (entry left right)
      ≡ phaseAction (H.modulationExponent axis right) (entry left right)

    distinctPhasesKillCoefficient :
      {leftPhase rightPhase : Trit} →
      {coefficient : Scalar} →
      leftPhase ≢ rightPhase →
      phaseAction leftPhase coefficient
      ≡ phaseAction rightPhase coefficient →
      coefficient ≡ zeroScalar

    translationCommutationCoefficient :
      (shift left right : H.X6) →
      entry (translateBy shift left) (translateBy shift right)
      ≡ entry left right

open SchrodingerCommutantMatrix public

offDiagonalCoefficientVanishes :
  (matrix : SchrodingerCommutantMatrix) →
  (left right : H.X6) →
  left ≢ right →
  entry matrix left right ≡ zeroScalar matrix
offDiagonalCoefficientVanishes matrix left right distinct
  with coordinateSeparation left right distinct
... | axis , phasesDiffer =
  distinctPhasesKillCoefficient matrix phasesDiffer
    (modulationCommutationCoefficient matrix axis left right)

diagonalCoefficientIsOrigin :
  (matrix : SchrodingerCommutantMatrix) →
  (state : H.X6) →
  entry matrix state state ≡ entry matrix origin origin
diagonalCoefficientIsOrigin matrix state
  rewrite difference6Restores origin state =
  sym
    (translationCommutationCoefficient matrix
      (difference6 origin state) state state)

record ScalarCommutantConclusion
  (matrix : SchrodingerCommutantMatrix) : Set where
  constructor scalar-commutant-conclusion
  field
    scalar : Scalar matrix
    everyDiagonalCoefficientIsScalar :
      (state : H.X6) → entry matrix state state ≡ scalar
    everyOffDiagonalCoefficientVanishes :
      (left right : H.X6) →
      left ≢ right →
      entry matrix left right ≡ zeroScalar matrix

open ScalarCommutantConclusion public

schrodingerCommutantIsScalar :
  (matrix : SchrodingerCommutantMatrix) →
  ScalarCommutantConclusion matrix
schrodingerCommutantIsScalar matrix =
  scalar-commutant-conclusion
    (entry matrix origin origin)
    (diagonalCoefficientIsOrigin matrix)
    (offDiagonalCoefficientVanishes matrix)

------------------------------------------------------------------------
-- The exact irreducibility bridge remains standard finite-dimensional linear
-- algebra: over an algebraically closed characteristic-zero field, a unitary
-- finite-group representation with scalar commutant is irreducible.  This
-- module supplies its previously missing concrete commutant hypothesis.
------------------------------------------------------------------------

record FiniteSchurConverseInput
  (matrix : SchrodingerCommutantMatrix) : Set₁ where
  field
    representationIsFiniteDimensional : Set
    scalarFieldAlgebraicallyClosedCharacteristicZero : Set
    representationCompletelyReducible : Set
    scalarCommutantImpliesIrreducible :
      ScalarCommutantConclusion matrix → Set

open FiniteSchurConverseInput public

schrodingerRepresentationIrreducible :
  (matrix : SchrodingerCommutantMatrix) →
  FiniteSchurConverseInput matrix → Set
schrodingerRepresentationIrreducible matrix input =
  scalarCommutantImpliesIrreducible input
    (schrodingerCommutantIsScalar matrix)
