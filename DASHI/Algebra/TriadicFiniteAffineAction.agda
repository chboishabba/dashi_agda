module DASHI.Algebra.TriadicFiniteAffineAction where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteIrrep as Irrep

------------------------------------------------------------------------
-- Unit-group action on the additive quotient.

record FiniteUnitGroupAction
  {n : Nat}
  (G : Irrep.FiniteAdditiveGroup n) : Set₁ where
  field
    Unit : Set
    oneᵘ : Unit
    _*ᵘ_ : Unit → Unit → Unit
    inverseᵘ : Unit → Unit

    actUnit :
      Unit →
      Q.Residue3Pow n →
      Q.Residue3Pow n

    unitIdentity :
      (x : Q.Residue3Pow n) →
      actUnit oneᵘ x ≡ x

    unitComposition :
      (u v : Unit) →
      (x : Q.Residue3Pow n) →
      actUnit (u *ᵘ v) x
      ≡ actUnit u (actUnit v x)

    unitInverse :
      (u : Unit) →
      (x : Q.Residue3Pow n) →
      actUnit (inverseᵘ u) (actUnit u x) ≡ x

    additiveCompatibility :
      (u : Unit) →
      (x y : Q.Residue3Pow n) →
      actUnit u (Irrep._+ᵍ_ G x y)
      ≡ Irrep._+ᵍ_ G (actUnit u x) (actUnit u y)

open FiniteUnitGroupAction public

------------------------------------------------------------------------
-- Affine semidirect carrier: translation followed by a unit action.

record AffineElement
  {n : Nat}
  {G : Irrep.FiniteAdditiveGroup n}
  (U : FiniteUnitGroupAction G) : Set where
  constructor affine-element
  field
    translationPart : Q.Residue3Pow n
    unitPart : Unit U

open AffineElement public

affineAct :
  ∀ {n : Nat}
    {G : Irrep.FiniteAdditiveGroup n} →
  (U : FiniteUnitGroupAction G) →
  AffineElement U →
  Q.Residue3Pow n →
  Q.Residue3Pow n
affineAct {G = G} U a x =
  Irrep._+ᵍ_ G
    (translationPart a)
    (actUnit U (unitPart a) x)

record AffineKernelEquivariance
  {n : Nat}
  {G : Irrep.FiniteAdditiveGroup n}
  (U : FiniteUnitGroupAction G) : Set₁ where
  field
    Coeff : Set
    Signal : Set

    evaluateSignal :
      Signal →
      Q.Residue3Pow n →
      Coeff

    transformSignal :
      AffineElement U →
      Signal →
      Signal

    kernel : Signal → Signal

    transformedSignalMatchesAffineAction :
      (a : AffineElement U) →
      (f : Signal) →
      (x : Q.Residue3Pow n) →
      evaluateSignal (transformSignal a f) x
      ≡ evaluateSignal f (affineAct U a x)

    kernelEquivariant :
      (a : AffineElement U) →
      (f : Signal) →
      kernel (transformSignal a f)
      ≡ transformSignal a (kernel f)

open AffineKernelEquivariance public

------------------------------------------------------------------------
-- Promotion boundary.

affineActionStatement : String
affineActionStatement =
  "The finite symmetry layer contains additive translations, a typed unit-group action, and their affine semidirect action on the depth-n quotient."

affineActionBoundary : String
affineActionBoundary =
  "No all-n unit-group classification or affine irrep theorem is inferred. Each unit carrier, action law, additive compatibility law, and kernel-equivariance receipt must be supplied at the chosen depth."
