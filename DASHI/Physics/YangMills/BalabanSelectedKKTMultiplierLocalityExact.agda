module DASHI.Physics.YangMills.BalabanSelectedKKTMultiplierLocalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Convert multiplier-Gram kernel decay into the exact estimate actually used
-- at Gate I.  For s=Lg and lambda_0=K+ s, finite weighted row summation gives
--
--   |lambda_0(x)| <= M_s R_K w(x).
--
-- Summing only over the plaquette collar gives a collar L1 bound.  This avoids
-- a global norm on the repaired 3072-coordinate state and keeps the source,
-- Green kernel and collar geometry visible in the theorem statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as Row
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt

sumImplementationsAgree :
  ∀ {Site : Set}
    (sites : List Site)
    (value : Site → ℚ) →
  Row.sumKernel sites value ≡ Sums.sumRational sites value
sumImplementationsAgree [] value = refl
sumImplementationsAgree (site ∷ sites) value
  rewrite sumImplementationsAgree sites value = refl

pseudoApplyIsKernelApply :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    source row →
  Pseudo.pseudoApply pseudoData source row
  ≡ Row.kernelApply
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (Pseudo.gramPseudoinverse pseudoData)
      source row
pseudoApplyIsKernelApply pseudoData source row =
  sym
    (sumImplementationsAgree
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (λ column →
        Pseudo.gramPseudoinverse pseudoData row column
          * source column))

record CanonicalMultiplierLocalityData
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (source : Pseudo.MultiplierVector Multiplier) : Set₁ where
  field
    weight : Multiplier → ℚ
    sourceMajorant greenWeightedRowMajorant : ℚ

    weightNonnegative : ∀ row → 0ℚ ≤ weight row
    sourceMajorantNonnegative : 0ℚ ≤ sourceMajorant
    greenMajorantNonnegative : 0ℚ ≤ greenWeightedRowMajorant

    sourceLocalized : ∀ row →
      ∣ source row ∣ ≤ sourceMajorant * weight row

    greenWeightedRowBound : ∀ left →
      Row.weightedRowSum
        (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
        (Pseudo.gramPseudoinverse pseudoData)
        weight left
      ≤ greenWeightedRowMajorant * weight left

open CanonicalMultiplierLocalityData public

selectedCanonicalMultiplierLocality :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {source : Pseudo.MultiplierVector Multiplier} →
  (locality : CanonicalMultiplierLocalityData pseudoData source) →
  ∀ left →
  ∣ Pseudo.pseudoApply pseudoData source left ∣
  ≤ greenWeightedRowMajorant locality
      * sourceMajorant locality * weight locality left
selectedCanonicalMultiplierLocality
    {pseudoData = pseudoData} {source = source} locality left =
  subst
    (λ selected →
      ∣ selected ∣
      ≤ greenWeightedRowMajorant locality
          * sourceMajorant locality * weight locality left)
    (sym (pseudoApplyIsKernelApply pseudoData source left))
    (Row.weightedKernelContraction
      record
        { Row.FiniteWeightedRowContraction.sites =
            Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)
        ; Row.FiniteWeightedRowContraction.kernel =
            Pseudo.gramPseudoinverse pseudoData
        ; Row.FiniteWeightedRowContraction.weight = weight locality
        ; Row.FiniteWeightedRowContraction.contractionFactor =
            greenWeightedRowMajorant locality
        ; Row.FiniteWeightedRowContraction.weightNonnegative =
            weightNonnegative locality
        ; Row.FiniteWeightedRowContraction.contractionNonnegative =
            greenMajorantNonnegative locality
        ; Row.FiniteWeightedRowContraction.rowBound =
            greenWeightedRowBound locality }
      source
      (sourceMajorant locality)
      (sourceMajorantNonnegative locality)
      (sourceLocalized locality)
      left)

restrictScalarToCollar :
  ∀ {Multiplier} →
  (Multiplier → Bool) → (Multiplier → ℚ) → Multiplier → ℚ
restrictScalarToCollar collar value row with collar row
... | false = 0ℚ
... | true = value row

multiplierCollarL1 :
  ∀ {Multiplier} →
  Matrix.FiniteRationalCoordinates Multiplier →
  (Multiplier → Bool) → (Multiplier → ℚ) → ℚ
multiplierCollarL1 carrier collar multiplier =
  Sums.sumRational (Matrix.coordinates carrier)
    (λ row → ∣ restrictScalarToCollar collar multiplier row ∣)

collarWeightMass :
  ∀ {Multiplier} →
  Matrix.FiniteRationalCoordinates Multiplier →
  (Multiplier → Bool) → (Multiplier → ℚ) → ℚ
collarWeightMass carrier collar weight =
  Sums.sumRational (Matrix.coordinates carrier)
    (restrictScalarToCollar collar weight)

restrictedMultiplierPointwiseBound :
  ∀ {Multiplier}
    (collar : Multiplier → Bool)
    multiplier weight majorant →
  0ℚ ≤ majorant →
  (∀ row → 0ℚ ≤ weight row) →
  (∀ row → ∣ multiplier row ∣ ≤ majorant * weight row) →
  ∀ row →
  ∣ restrictScalarToCollar collar multiplier row ∣
  ≤ majorant * restrictScalarToCollar collar weight row
restrictedMultiplierPointwiseBound
    collar multiplier weight majorant majorantNonnegative
    weightNonnegative pointwise row with collar row
... | true = pointwise row
... | false = ℚP.≤-refl

selectedMultiplierCollarNormUpper :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {source : Pseudo.MultiplierVector Multiplier}
    (locality : CanonicalMultiplierLocalityData pseudoData source)
    (collar : Multiplier → Bool) →
  multiplierCollarL1
    (Pseudo.multiplierCarrier pseudoData) collar
    (Pseudo.pseudoApply pseudoData source)
  ≤ (greenWeightedRowMajorant locality * sourceMajorant locality)
      * collarWeightMass
          (Pseudo.multiplierCarrier pseudoData) collar
          (weight locality)
selectedMultiplierCollarNormUpper
    {pseudoData = pseudoData} {source = source} locality collar =
  let
    majorant =
      greenWeightedRowMajorant locality * sourceMajorant locality

    instance
      greenNN : NonNegative (greenWeightedRowMajorant locality)
      greenNN = ℚ.nonNegative (greenMajorantNonnegative locality)

      sourceNN : NonNegative (sourceMajorant locality)
      sourceNN = ℚ.nonNegative (sourceMajorantNonnegative locality)

      majorantNN : NonNegative majorant
      majorantNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (greenWeightedRowMajorant locality)
        (sourceMajorant locality)

    majorantNonnegative : 0ℚ ≤ majorant
    majorantNonnegative = ℚP.nonNegative⁻¹ majorant

    pointwise = restrictedMultiplierPointwiseBound
      collar
      (Pseudo.pseudoApply pseudoData source)
      (weight locality)
      majorant majorantNonnegative
      (weightNonnegative locality)
      (selectedCanonicalMultiplierLocality locality)
  in
  subst
    (λ upper →
      multiplierCollarL1
        (Pseudo.multiplierCarrier pseudoData) collar
        (Pseudo.pseudoApply pseudoData source)
      ≤ upper)
    (Sums.sumRationalScale
      majorant
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (restrictScalarToCollar collar (weight locality)))
    (Tilt.sumPointwiseBelow
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (λ row →
        ∣ restrictScalarToCollar collar
            (Pseudo.pseudoApply pseudoData source) row ∣)
      (λ row →
        majorant * restrictScalarToCollar collar (weight locality) row)
      pointwise)

selectedKKTMultiplierPointwiseLocalityLevel : ProofLevel
selectedKKTMultiplierPointwiseLocalityLevel = machineChecked

selectedMultiplierCollarNormLevel : ProofLevel
selectedMultiplierCollarNormLevel = machineChecked

selectedPhysicalSourceMajorantProducerLevel : ProofLevel
selectedPhysicalSourceMajorantProducerLevel = conditional
