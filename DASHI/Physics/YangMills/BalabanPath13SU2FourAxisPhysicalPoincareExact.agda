module DASHI.Physics.YangMills.BalabanPath13SU2FourAxisPhysicalPoincareExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Lift the literal scalar L=13 four-axis Poincare theorem to the repository's
-- three real coordinates of su(2).  No hidden Lie-algebra norm convention is
-- introduced: the carrier is exactly LieCoordinate3 and the norm/energy are
-- finite sums over those three existing coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as SU2
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact as Norm
import DASHI.Physics.YangMills.BalabanNormalizedFourAxisMartingaleExact as Martingale
import DASHI.Physics.YangMills.BalabanPath13FourAxisPhysicalPoincareExact as Poincare13

PhysicalSU2SiteField13 : Set
PhysicalSU2SiteField13 = SU2.LieCoordinate3 → SiteField Side13.side13

su2SiteNormSq : PhysicalSU2SiteField13 → ℚ
su2SiteNormSq field =
  sumRational SU2.lieCoordinates3
    (λ coordinate → Norm.globalNormSq (field coordinate))

su2DirectionalEnergy : PhysicalSU2SiteField13 → ℚ
su2DirectionalEnergy field =
  sumRational SU2.lieCoordinates3
    (λ coordinate → Poincare13.globalDirectionalEnergy (field coordinate))

SU2GlobalMeanZero : PhysicalSU2SiteField13 → Set
SU2GlobalMeanZero field =
  ∀ coordinate →
    Martingale.GlobalMeanZero Side13.side13AverageData (field coordinate)

sumPointwiseBelow :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumPointwiseBelow [] left right pointwise = ℚP.≤-refl
sumPointwiseBelow (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumPointwiseBelow values left right pointwise)

componentwisePath13Poincare :
  ∀ field → SU2GlobalMeanZero field →
  sumRational SU2.lieCoordinates3
    (λ coordinate →
      LDL.oneEighteenth * Norm.globalNormSq (field coordinate))
  ≤ su2DirectionalEnergy field
componentwisePath13Poincare field meanZero =
  sumPointwiseBelow SU2.lieCoordinates3
    (λ coordinate →
      LDL.oneEighteenth * Norm.globalNormSq (field coordinate))
    (λ coordinate → Poincare13.globalDirectionalEnergy (field coordinate))
    (λ coordinate →
      Poincare13.path13GlobalPoincare
        (field coordinate) (meanZero coordinate))

scaledSU2NormIsComponentFold : ∀ field →
  LDL.oneEighteenth * su2SiteNormSq field
  ≡ sumRational SU2.lieCoordinates3
      (λ coordinate →
        LDL.oneEighteenth * Norm.globalNormSq (field coordinate))
scaledSU2NormIsComponentFold field =
  sym
    (sumRationalScale LDL.oneEighteenth SU2.lieCoordinates3
      (λ coordinate → Norm.globalNormSq (field coordinate)))

path13SU2FourAxisPhysicalPoincare :
  ∀ field → SU2GlobalMeanZero field →
  LDL.oneEighteenth * su2SiteNormSq field
  ≤ su2DirectionalEnergy field
path13SU2FourAxisPhysicalPoincare field meanZero =
  subst
    (λ left → left ≤ su2DirectionalEnergy field)
    (scaledSU2NormIsComponentFold field)
    (componentwisePath13Poincare field meanZero)

path13SU2FourAxisPhysicalPoincareLevel : ProofLevel
path13SU2FourAxisPhysicalPoincareLevel = machineChecked
