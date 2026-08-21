module DASHI.Mathematics.NumberTheory.RiemannReflectionOrbitDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Levent Alpoge, Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line"
-- (2026).
-- arXiv DOI: 10.48550/arXiv.2608.13637.
--
-- Bernhard Riemann,
-- "Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse" (1859).
-- No DOI was assigned to the original publication.
--
-- DASHI CONTRIBUTION
--
-- Reuse the exact rational critical-line reflection already formalized in
-- RiemannXiSymmetryExact and quotient away only orientation.  The centered
-- displacement alpha = Re(s) - 1/2 changes sign under critical reflection,
-- while alpha^2 is exactly invariant.  The reflected pair has zero signed
-- displacement but retains twice the nonnegative-even algebraic defect.
--
-- A generic 2 x 2 reflection block is then analysed exactly: swapping alpha to
-- -alpha exchanges the diagonal orientation, preserves trace and determinant,
-- and the determinant contains the explicit residual -alpha^2.  This is the
-- concrete algebraic experiment suggested by the reflection-pair discussion.
-- It is NOT asserted to be the actual Alpoge--Furman Weil-form block, and no
-- weighted off-line displacement bound is claimed from their theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Xi

centeredDisplacement : Xi.ComplexCoordinate → ℚ
centeredDisplacement point = Xi.realPart point - Xi.half

criticalReflectionNegatesDisplacement : ∀ point →
  centeredDisplacement (Xi.criticalReflection point)
  ≡ - centeredDisplacement point
criticalReflectionNegatesDisplacement (Xi.complexCoordinate sigma tau) =
  solve (sigma ∷ [])

reflectionDefect : Xi.ComplexCoordinate → ℚ
reflectionDefect point =
  centeredDisplacement point * centeredDisplacement point

reflectionDefectInvariant : ∀ point →
  reflectionDefect (Xi.criticalReflection point) ≡ reflectionDefect point
reflectionDefectInvariant (Xi.complexCoordinate sigma tau) =
  solve (sigma ∷ [])

pairSignedDisplacementCancels : ∀ point →
  centeredDisplacement point
  + centeredDisplacement (Xi.criticalReflection point)
  ≡ 0ℚ
pairSignedDisplacementCancels (Xi.complexCoordinate sigma tau) =
  solve (sigma ∷ [])

pairDefectMass : Xi.ComplexCoordinate → ℚ
pairDefectMass point =
  reflectionDefect point
  + reflectionDefect (Xi.criticalReflection point)

pairDefectMassIsDouble : ∀ point →
  pairDefectMass point ≡ (1ℚ + 1ℚ) * reflectionDefect point
pairDefectMassIsDouble (Xi.complexCoordinate sigma tau) =
  solve (sigma ∷ [])

criticalLineHasZeroDefect : ∀ point →
  Xi.CriticalLine point → reflectionDefect point ≡ 0ℚ
criticalLineHasZeroDefect (Xi.complexCoordinate sigma tau) sigmaIsHalf
  rewrite sigmaIsHalf = solve []

record ReflectionOrbit : Set where
  constructor reflectionOrbit
  field
    representative : Xi.ComplexCoordinate
    partner : Xi.ComplexCoordinate
    partnerLaw : partner ≡ Xi.criticalReflection representative

open ReflectionOrbit public

canonicalReflectionOrbit : Xi.ComplexCoordinate → ReflectionOrbit
canonicalReflectionOrbit point =
  reflectionOrbit point (Xi.criticalReflection point) refl

orbitDefect : ReflectionOrbit → ℚ
orbitDefect orbit = reflectionDefect (representative orbit)

orbitDefectIndependentOfRepresentative : ∀ point →
  reflectionDefect (partner (canonicalReflectionOrbit point))
  ≡ reflectionDefect (representative (canonicalReflectionOrbit point))
orbitDefectIndependentOfRepresentative = reflectionDefectInvariant

record RationalBlock2 : Set where
  constructor rationalBlock2
  field
    topLeft : ℚ
    topRight : ℚ
    bottomLeft : ℚ
    bottomRight : ℚ

open RationalBlock2 public

blockExt : ∀ {left right} →
  topLeft left ≡ topLeft right →
  topRight left ≡ topRight right →
  bottomLeft left ≡ bottomLeft right →
  bottomRight left ≡ bottomRight right →
  left ≡ right
blockExt {rationalBlock2 _ _ _ _} {rationalBlock2 _ _ _ _}
  refl refl refl refl = refl

reflectionBlock : ℚ → ℚ → ℚ → RationalBlock2
reflectionBlock center coupling alpha =
  rationalBlock2
    (center + alpha)
    coupling
    coupling
    (center - alpha)

swapDiagonalOrientation : RationalBlock2 → RationalBlock2
swapDiagonalOrientation (rationalBlock2 a b c d) =
  rationalBlock2 d c b a

reflectionBlockSignFlipSwapsOrientation : ∀ center coupling alpha →
  reflectionBlock center coupling (- alpha)
  ≡ swapDiagonalOrientation (reflectionBlock center coupling alpha)
reflectionBlockSignFlipSwapsOrientation center coupling alpha =
  blockExt
    (solve (center ∷ alpha ∷ []))
    refl
    refl
    (solve (center ∷ alpha ∷ []))

blockTrace : RationalBlock2 → ℚ
blockTrace block = topLeft block + bottomRight block

blockDeterminant : RationalBlock2 → ℚ
blockDeterminant block =
  topLeft block * bottomRight block
  - topRight block * bottomLeft block

reflectionBlockTraceExact : ∀ center coupling alpha →
  blockTrace (reflectionBlock center coupling alpha)
  ≡ (1ℚ + 1ℚ) * center
reflectionBlockTraceExact center coupling alpha =
  solve (center ∷ alpha ∷ [])

reflectionBlockDeterminantExact : ∀ center coupling alpha →
  blockDeterminant (reflectionBlock center coupling alpha)
  ≡ center * center - coupling * coupling - alpha * alpha
reflectionBlockDeterminantExact center coupling alpha =
  solve (center ∷ coupling ∷ alpha ∷ [])

reflectionBlockTraceEven : ∀ center coupling alpha →
  blockTrace (reflectionBlock center coupling (- alpha))
  ≡ blockTrace (reflectionBlock center coupling alpha)
reflectionBlockTraceEven center coupling alpha =
  solve (center ∷ alpha ∷ [])

reflectionBlockDeterminantEven : ∀ center coupling alpha →
  blockDeterminant (reflectionBlock center coupling (- alpha))
  ≡ blockDeterminant (reflectionBlock center coupling alpha)
reflectionBlockDeterminantEven center coupling alpha =
  solve (center ∷ coupling ∷ alpha ∷ [])

zetaReflectionBlock : ℚ → ℚ → Xi.ComplexCoordinate → RationalBlock2
zetaReflectionBlock center coupling point =
  reflectionBlock center coupling (centeredDisplacement point)

zetaBlockDeterminantReflectionInvariant : ∀ center coupling point →
  blockDeterminant
    (zetaReflectionBlock center coupling (Xi.criticalReflection point))
  ≡ blockDeterminant (zetaReflectionBlock center coupling point)
zetaBlockDeterminantReflectionInvariant
    center coupling (Xi.complexCoordinate sigma tau) =
  solve (center ∷ coupling ∷ sigma ∷ [])

record ReflectionDefectBoundary : Set where
  constructor reflectionDefectBoundary
  field
    genericBlockIsAlpogeFurmanWeilBlock : Set
    genericBlockIsNotIdentifiedWithAlpogeFurmanWeilBlock :
      genericBlockIsAlpogeFurmanWeilBlock → ⊥

    alpogeFurmanAlreadyBoundsSumAlphaSquared : Set
    alpogeFurmanDoesNotHereSupplySumAlphaSquaredBound :
      alpogeFurmanAlreadyBoundsSumAlphaSquared → ⊥

    finiteRationalDefectProvesRH : Set
    finiteRationalDefectDoesNotProveRH :
      finiteRationalDefectProvesRH → ⊥

canonicalReflectionDefectBoundary : ReflectionDefectBoundary
canonicalReflectionDefectBoundary =
  reflectionDefectBoundary
    ⊥ (λ impossible → impossible)
    ⊥ (λ impossible → impossible)
    ⊥ (λ impossible → impossible)
