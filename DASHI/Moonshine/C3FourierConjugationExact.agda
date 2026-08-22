module DASHI.Moonshine.C3FourierConjugationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- The repository already had the exact depth-one Z/3Z character table and
-- the Monster 3B phase-transport involution, but the familiar identities
--
--   zeta^3 = 1,
--   zeta^2 = zeta^-1 = conjugate(zeta),
--
-- and the ordered conjugate Fourier rows were only implicit.  This module
-- makes those identities theorem-level and proves that the symbolic Fourier
-- conjugation intertwines exactly with the existing Monster 3B inversion
-- transport.  No complex-number approximation is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster

------------------------------------------------------------------------
-- Canonical symbolic roots of unity.

one zeta zetaSquared : C3.C3Phase
one = C3.phase0
zeta = C3.phase1
zetaSquared = C3.phase2

inversePhase : C3.C3Phase → C3.C3Phase
inversePhase = C3.conjugatePhase

zetaSquaredIsSquareOfZeta :
  C3.multiplyPhase zeta zeta ≡ zetaSquared
zetaSquaredIsSquareOfZeta = refl

zetaSquaredIsInverseZeta :
  zetaSquared ≡ inversePhase zeta
zetaSquaredIsInverseZeta = refl

inverseZetaIsZetaSquared :
  inversePhase zeta ≡ zetaSquared
inverseZetaIsZetaSquared = refl

zetaTimesInverseZetaIsOne :
  C3.multiplyPhase zeta (inversePhase zeta) ≡ one
zetaTimesInverseZetaIsOne = refl

inverseZetaTimesZetaIsOne :
  C3.multiplyPhase (inversePhase zeta) zeta ≡ one
inverseZetaTimesZetaIsOne = refl

zetaCubedIsOne :
  C3.multiplyPhase (C3.multiplyPhase zeta zeta) zeta ≡ one
zetaCubedIsOne = refl

zetaSquaredSquaredIsZeta :
  C3.multiplyPhase zetaSquared zetaSquared ≡ zeta
zetaSquaredSquaredIsZeta = refl

inversePhaseInvolutive :
  (phase : C3.C3Phase) →
  inversePhase (inversePhase phase) ≡ phase
inversePhaseInvolutive C3.phase0 = refl
inversePhaseInvolutive C3.phase1 = refl
inversePhaseInvolutive C3.phase2 = refl

------------------------------------------------------------------------
-- Ordered C3 Fourier character rows in the conventional coordinate order
-- 0,1,2.  This is the object whose second and third rows are conjugates:
--
--   chi0 = [1,1,1]
--   chi1 = [1,zeta,zeta^2]
--   chi2 = [1,zeta^2,zeta]
--        = [1,zeta^-1,zeta^-2].

record FourierRow : Set where
  constructor fourierRow
  field
    at0 : C3.C3Phase
    at1 : C3.C3Phase
    at2 : C3.C3Phase

open FourierRow public

chi0 chi1 chi2 : FourierRow
chi0 = fourierRow one one one
chi1 = fourierRow one zeta zetaSquared
chi2 = fourierRow one zetaSquared zeta

conjugateRow : FourierRow → FourierRow
conjugateRow row =
  fourierRow
    (inversePhase (at0 row))
    (inversePhase (at1 row))
    (inversePhase (at2 row))

chi0IsFixedByConjugation : conjugateRow chi0 ≡ chi0
chi0IsFixedByConjugation = refl

chi1ConjugateIsChi2 : conjugateRow chi1 ≡ chi2
chi1ConjugateIsChi2 = refl

chi2ConjugateIsChi1 : conjugateRow chi2 ≡ chi1
chi2ConjugateIsChi1 = refl

chi2IsInverseCharacterRow :
  chi2
  ≡ fourierRow one (inversePhase zeta)
      (inversePhase zetaSquared)
chi2IsInverseCharacterRow = refl

conjugateRowInvolutive :
  (row : FourierRow) →
  conjugateRow (conjugateRow row) ≡ row
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase0 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase0 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase0 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase1 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase1 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase1 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase2 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase2 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase0 C3.phase2 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase0 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase0 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase0 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase1 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase1 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase1 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase2 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase2 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase1 C3.phase2 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase0 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase0 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase0 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase1 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase1 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase1 C3.phase2) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase2 C3.phase0) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase2 C3.phase1) = refl
conjugateRowInvolutive (fourierRow C3.phase2 C3.phase2 C3.phase2) = refl

------------------------------------------------------------------------
-- Compatibility with the pre-existing depth-one character table.  That table
-- is stored in residue order (-1,0,+1), so its positive-frequency row is
-- [zeta^2,1,zeta] and its negative-frequency row is [zeta,1,zeta^2].

positiveDepthOneRowExact :
  C3.characterRow C3.rPos
  ≡ C3.character-row zetaSquared one zeta
positiveDepthOneRowExact = C3.positiveRowExact

negativeDepthOneRowExact :
  C3.characterRow C3.rNeg
  ≡ C3.character-row zeta one zetaSquared
negativeDepthOneRowExact = C3.negativeRowExact

------------------------------------------------------------------------
-- Exact intertwining with the Monster 3B phase carrier.

phaseToMonster : C3.C3Phase → Monster.C3Phase
phaseToMonster C3.phase0 = Monster.invariantPhase
phaseToMonster C3.phase1 = Monster.zetaPhase
phaseToMonster C3.phase2 = Monster.zetaSquaredPhase

monsterInversionIntertwinesConjugation :
  (phase : C3.C3Phase) →
  phaseToMonster (inversePhase phase)
  ≡ Monster.transportPhase Monster.invertsGenerator
      (phaseToMonster phase)
monsterInversionIntertwinesConjugation C3.phase0 = refl
monsterInversionIntertwinesConjugation C3.phase1 = refl
monsterInversionIntertwinesConjugation C3.phase2 = refl

monsterZetaInverseIsZetaSquaredSector :
  phaseToMonster (inversePhase zeta) ≡ Monster.zetaSquaredPhase
monsterZetaInverseIsZetaSquaredSector = refl
