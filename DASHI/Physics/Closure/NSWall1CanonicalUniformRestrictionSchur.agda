module DASHI.Physics.Closure.NSWall1CanonicalUniformRestrictionSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Analysis.FiniteWeightedKernelSums
open import DASHI.Physics.Closure.NSWall1CanonicalFiniteSchur
open import DASHI.Physics.Closure.NSWall1FourierShellInstance
open import DASHI.Physics.Closure.NSWall1CanonicalFourierRestriction

------------------------------------------------------------------------
-- Scale-uniform exact Schur constants on the canonical six-mode restriction.
--
-- Each scale must identify its actual Wall-1 Fourier entries and active lists
-- with the same canonical packet.  Under that exact representation theorem the
-- transported certificates have constants (2,4) and (4,2) at every scale.
--
-- This is genuine uniformity for the restricted carrier.  It does not assert
-- that the full physical shell has no additional modes or incidences; that
-- extension remains a separate analytic/combinatorial theorem.
------------------------------------------------------------------------

record CanonicalRestrictionScaleFamily
    {j v : Level}
    (Scale : Set j)
    (Vector : Set v) : Set (lsuc (j ⊔ v)) where
  field
    k01AtScale : Scale → Wall1FourierShellData Vector ℚ
    k10AtScale : Scale → Wall1FourierShellData Vector ℚ

    canonicalRestrictionAtScale :
      (scale : Scale) →
      Wall1CanonicalFourierRestriction
        Vector
        (k01AtScale scale)
        (k10AtScale scale)

open CanonicalRestrictionScaleFamily public

restrictedK01CertificateAtScale :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  (scale : Scale) →
  FiniteWeightedSchurCertificate
    (restrictedK01Finite
      (wall1BiotSavartKernel (k01AtScale F scale)))
restrictedK01CertificateAtScale F scale =
  wall1CanonicalRestrictedK01Certificate
    (canonicalRestrictionAtScale F scale)

restrictedK10CertificateAtScale :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  (scale : Scale) →
  FiniteWeightedSchurCertificate
    (restrictedK10Finite
      (wall1BiotSavartKernel (k10AtScale F scale)))
restrictedK10CertificateAtScale F scale =
  wall1CanonicalRestrictedK10Certificate
    (canonicalRestrictionAtScale F scale)

restrictedK01RowConstantUniform :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  (scale : Scale) →
  rowConstant (restrictedK01CertificateAtScale F scale) ≡ two
restrictedK01RowConstantUniform F scale = refl

restrictedK01ColumnConstantUniform :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  (scale : Scale) →
  columnConstant (restrictedK01CertificateAtScale F scale) ≡ four
restrictedK01ColumnConstantUniform F scale = refl

restrictedK10RowConstantUniform :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  (scale : Scale) →
  rowConstant (restrictedK10CertificateAtScale F scale) ≡ four
restrictedK10RowConstantUniform F scale = refl

restrictedK10ColumnConstantUniform :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  (scale : Scale) →
  columnConstant (restrictedK10CertificateAtScale F scale) ≡ two
restrictedK10ColumnConstantUniform F scale = refl

record CanonicalRestrictedUniformSchur
    {j v : Level}
    {Scale : Set j}
    {Vector : Set v}
    (F : CanonicalRestrictionScaleFamily Scale Vector) :
    Set (lsuc (j ⊔ v)) where
  field
    k01Certificate :
      (scale : Scale) →
      FiniteWeightedSchurCertificate
        (restrictedK01Finite
          (wall1BiotSavartKernel (k01AtScale F scale)))

    k10Certificate :
      (scale : Scale) →
      FiniteWeightedSchurCertificate
        (restrictedK10Finite
          (wall1BiotSavartKernel (k10AtScale F scale)))

    k01RowConstant :
      (scale : Scale) → rowConstant (k01Certificate scale) ≡ two

    k01ColumnConstant :
      (scale : Scale) → columnConstant (k01Certificate scale) ≡ four

    k10RowConstant :
      (scale : Scale) → rowConstant (k10Certificate scale) ≡ four

    k10ColumnConstant :
      (scale : Scale) → columnConstant (k10Certificate scale) ≡ two

open CanonicalRestrictedUniformSchur public

canonicalRestrictedUniformSchur :
  ∀ {j v}
    {Scale : Set j}
    {Vector : Set v} →
  (F : CanonicalRestrictionScaleFamily Scale Vector) →
  CanonicalRestrictedUniformSchur F
canonicalRestrictedUniformSchur F = record
  { k01Certificate = restrictedK01CertificateAtScale F
  ; k10Certificate = restrictedK10CertificateAtScale F
  ; k01RowConstant = restrictedK01RowConstantUniform F
  ; k01ColumnConstant = restrictedK01ColumnConstantUniform F
  ; k10RowConstant = restrictedK10RowConstantUniform F
  ; k10ColumnConstant = restrictedK10ColumnConstantUniform F
  }
