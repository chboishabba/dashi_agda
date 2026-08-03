module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Venue/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
-- Relationship: Luo's proof controls the high-frequency energy flux by a
-- weighted shell-energy expression multiplied by ||nabla u_{<p}||_infinity.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Construct the exact algebraic theorem shape needed at the physical flux
-- boundary:
--
--   signed physical triad flux
--     <= absolute Hermitian pair-incidence majorant
--     <= weighted-Schur shell-energy majorant
--           * low-pass gradient L-infinity quantity.
--
-- The module deliberately proves domination, not equality of the signed,
-- phase-sensitive convection operator with a positive Gram surrogate.
-- Complex Fourier phases are represented by the conjugate-symmetric norm
-- |z_s-z_t|^2 = (Re_s-Re_t)^2 + (Im_s-Im_t)^2.
--
-- It also records multiplicity by equality of complete incidence fibres;
-- source/target injectivity is neither assumed nor required.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Rational.Base
  using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound as Direct
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as PositiveKernel
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray

------------------------------------------------------------------------
-- Finite rational sums.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

sumAppend :
  (left right : List ℚ) →
  sumℚ (left ++ right) ≡ sumℚ left + sumℚ right
sumAppend [] right = sym (ℚₚ.+-identityˡ (sumℚ right))
sumAppend (value ∷ left) right =
  trans
    (cong (value +_) (sumAppend left right))
    (sym (ℚₚ.+-assoc value (sumℚ left) (sumℚ right)))

------------------------------------------------------------------------
-- Hermitian pair-incidence atom.
------------------------------------------------------------------------

complexDifferenceNormSquared :
  ℚ → ℚ → ℚ → ℚ → ℚ
complexDifferenceNormSquared sourceReal sourceImag targetReal targetImag =
  L2.square (sourceReal - targetReal)
  + L2.square (sourceImag - targetImag)

complexDifferenceNormSquaredNonnegative :
  (sourceReal sourceImag targetReal targetImag : ℚ) →
  0ℚ ≤ complexDifferenceNormSquared
    sourceReal sourceImag targetReal targetImag
complexDifferenceNormSquaredNonnegative sourceReal sourceImag targetReal targetImag =
  ℚₚ.+-mono-≤
    (L2.squareNonnegative (sourceReal - targetReal))
    (L2.squareNonnegative (sourceImag - targetImag))

record HermitianPairIncidenceAtom : Set where
  constructor incidence-atom
  field
    sourceReal sourceImag : ℚ
    targetReal targetImag : ℚ

    nonnegativeCoefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ nonnegativeCoefficient

    signedPhysicalTriadTerm : ℚ
    absolutePhysicalTriadTerm : ℚ
    absolutePhysicalTermNonnegative : 0ℚ ≤ absolutePhysicalTriadTerm

    signedTermUpper :
      signedPhysicalTriadTerm
        ≤ nonnegativeCoefficient
          * complexDifferenceNormSquared
              sourceReal sourceImag targetReal targetImag

    signedTermLower :
      0ℚ -
        (nonnegativeCoefficient
          * complexDifferenceNormSquared
              sourceReal sourceImag targetReal targetImag)
        ≤ signedPhysicalTriadTerm

    absoluteTermBound :
      absolutePhysicalTriadTerm
        ≤ nonnegativeCoefficient
          * complexDifferenceNormSquared
              sourceReal sourceImag targetReal targetImag

open HermitianPairIncidenceAtom public

incidenceMajorant : HermitianPairIncidenceAtom → ℚ
incidenceMajorant atom =
  nonnegativeCoefficient atom
  * complexDifferenceNormSquared
      (sourceReal atom)
      (sourceImag atom)
      (targetReal atom)
      (targetImag atom)

incidenceMajorantNonnegative :
  (atom : HermitianPairIncidenceAtom) →
  0ℚ ≤ incidenceMajorant atom
incidenceMajorantNonnegative atom =
  let
    differenceNN =
      complexDifferenceNormSquaredNonnegative
        (sourceReal atom)
        (sourceImag atom)
        (targetReal atom)
        (targetImag atom)
    instance
      coefficientNN = nonNegative (coefficientNonnegative atom)
      normNN = nonNegative differenceNN
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (nonnegativeCoefficient atom)
          (complexDifferenceNormSquared
            (sourceReal atom)
            (sourceImag atom)
            (targetReal atom)
            (targetImag atom))
  in
  ℚₚ.nonNegative⁻¹ (incidenceMajorant atom)

physicalTriadTermDominatedByIncidenceMajorant :
  (atom : HermitianPairIncidenceAtom) →
  absolutePhysicalTriadTerm atom ≤ incidenceMajorant atom
physicalTriadTermDominatedByIncidenceMajorant = absoluteTermBound

------------------------------------------------------------------------
-- Finite flux and incidence sums.
------------------------------------------------------------------------

absoluteFluxTerms : List HermitianPairIncidenceAtom → List ℚ
absoluteFluxTerms [] = []
absoluteFluxTerms (atom ∷ atoms) =
  absolutePhysicalTriadTerm atom ∷ absoluteFluxTerms atoms

incidenceMajorants : List HermitianPairIncidenceAtom → List ℚ
incidenceMajorants [] = []
incidenceMajorants (atom ∷ atoms) =
  incidenceMajorant atom ∷ incidenceMajorants atoms

sumAbsoluteFluxTerms : List HermitianPairIncidenceAtom → ℚ
sumAbsoluteFluxTerms atoms = sumℚ (absoluteFluxTerms atoms)

sumIncidenceMajorants : List HermitianPairIncidenceAtom → ℚ
sumIncidenceMajorants atoms = sumℚ (incidenceMajorants atoms)

sumIncidenceMajorantsAppend :
  (left right : List HermitianPairIncidenceAtom) →
  sumIncidenceMajorants (left ++ right)
    ≡ sumIncidenceMajorants left + sumIncidenceMajorants right
sumIncidenceMajorantsAppend [] right =
  sym (ℚₚ.+-identityˡ (sumIncidenceMajorants right))
sumIncidenceMajorantsAppend (atom ∷ left) right =
  trans
    (cong (incidenceMajorant atom +_)
      (sumIncidenceMajorantsAppend left right))
    (sym
      (ℚₚ.+-assoc
        (incidenceMajorant atom)
        (sumIncidenceMajorants left)
        (sumIncidenceMajorants right)))

finitePhysicalFluxAtomsDominatedByIncidenceMajorants :
  (atoms : List HermitianPairIncidenceAtom) →
  sumAbsoluteFluxTerms atoms ≤ sumIncidenceMajorants atoms
finitePhysicalFluxAtomsDominatedByIncidenceMajorants [] = ℚₚ.≤-refl
finitePhysicalFluxAtomsDominatedByIncidenceMajorants (atom ∷ atoms) =
  ℚₚ.+-mono-≤
    (physicalTriadTermDominatedByIncidenceMajorant atom)
    (finitePhysicalFluxAtomsDominatedByIncidenceMajorants atoms)

------------------------------------------------------------------------
-- Multiplicity-safe fibre agreement.
------------------------------------------------------------------------

record PairIncidenceMultiplicityCertificate
    {ℓK ℓI : Level} : Set (lsuc (ℓK ⊔ ℓI)) where
  constructor multiplicity-certificate
  field
    PairKey : Set ℓK
    Incidence : Set ℓI

    projectedConvolutionFibre : PairKey → List Incidence
    physicalPairIncidenceFibre : PairKey → List Incidence

    fibreMultiplicityAgreement :
      (key : PairKey) →
      physicalPairIncidenceFibre key
        ≡ projectedConvolutionFibre key

open PairIncidenceMultiplicityCertificate public

fiberMultiplicityMatchesConvolutionMultiplicity :
  ∀ {ℓK ℓI}
    (certificate : PairIncidenceMultiplicityCertificate {ℓK} {ℓI}) →
    (key : PairKey certificate) →
  length (physicalPairIncidenceFibre certificate key)
    ≡ length (projectedConvolutionFibre certificate key)
fiberMultiplicityMatchesConvolutionMultiplicity certificate key =
  cong length (fibreMultiplicityAgreement certificate key)

------------------------------------------------------------------------
-- Four-profile partition.  Multiplicity is retained because each profile is
-- a list of incidence records rather than a set of source/target images.
------------------------------------------------------------------------

record FourProfilePhysicalFluxPartition : Set where
  constructor four-profile-partition
  field
    allAtoms : List HermitianPairIncidenceAtom
    forcedTailAtoms : List HermitianPairIncidenceAtom
    adversarialAtoms : List HermitianPairIncidenceAtom
    transitionAtoms : List HermitianPairIncidenceAtom
    residualAtoms : List HermitianPairIncidenceAtom

    allAtomsAreProfileConcatenation :
      allAtoms
        ≡ forcedTailAtoms
          ++ (adversarialAtoms ++ (transitionAtoms ++ residualAtoms))

open FourProfilePhysicalFluxPartition public

physicalMajorantEqualsProfileSum :
  (partition : FourProfilePhysicalFluxPartition) →
  sumIncidenceMajorants (allAtoms partition)
    ≡ sumIncidenceMajorants (forcedTailAtoms partition)
      + (sumIncidenceMajorants (adversarialAtoms partition)
        + (sumIncidenceMajorants (transitionAtoms partition)
          + sumIncidenceMajorants (residualAtoms partition)))
physicalMajorantEqualsProfileSum partition
  rewrite allAtomsAreProfileConcatenation partition
        | sumIncidenceMajorantsAppend
            (forcedTailAtoms partition)
            (adversarialAtoms partition
              ++ (transitionAtoms partition ++ residualAtoms partition))
        | sumIncidenceMajorantsAppend
            (adversarialAtoms partition)
            (transitionAtoms partition ++ residualAtoms partition)
        | sumIncidenceMajorantsAppend
            (transitionAtoms partition)
            (residualAtoms partition) = refl

------------------------------------------------------------------------
-- Weighted-Schur flux bridge.
------------------------------------------------------------------------

record PhysicalCutoffFluxWeightedSchurBridge : Set₁ where
  constructor weighted-flux-bridge
  field
    atoms : List HermitianPairIncidenceAtom
    profilePartition : FourProfilePhysicalFluxPartition

    absoluteCutoffFlux : ℚ
    absoluteCutoffFluxNonnegative : 0ℚ ≤ absoluteCutoffFlux

    cutoffEnergyMajorant : ℚ
    lowPassGradientInfinity : ℚ
    profileSchurConstant : ℚ

    cutoffEnergyNonnegative : 0ℚ ≤ cutoffEnergyMajorant
    lowPassGradientNonnegative : 0ℚ ≤ lowPassGradientInfinity
    schurConstantNonnegative : 0ℚ ≤ profileSchurConstant

    partitionUsesBridgeAtoms : allAtoms profilePartition ≡ atoms

    physicalFluxTriangleBound :
      absoluteCutoffFlux ≤ sumAbsoluteFluxTerms atoms

    physicalPairIncidenceMajorantSchurBound :
      sumIncidenceMajorants atoms
        ≤ profileSchurConstant
          * (cutoffEnergyMajorant * lowPassGradientInfinity)

open PhysicalCutoffFluxWeightedSchurBridge public

physicalCutoffFluxDominatedByPairIncidenceFold :
  (bridge : PhysicalCutoffFluxWeightedSchurBridge) →
  absoluteCutoffFlux bridge
    ≤ sumIncidenceMajorants (atoms bridge)
physicalCutoffFluxDominatedByPairIncidenceFold bridge =
  ℚₚ.≤-trans
    (physicalFluxTriangleBound bridge)
    (finitePhysicalFluxAtomsDominatedByIncidenceMajorants (atoms bridge))

physicalCutoffFluxDominatedByWeightedSchurMajorant :
  (bridge : PhysicalCutoffFluxWeightedSchurBridge) →
  absoluteCutoffFlux bridge
    ≤ profileSchurConstant bridge
      * (cutoffEnergyMajorant bridge * lowPassGradientInfinity bridge)
physicalCutoffFluxDominatedByWeightedSchurMajorant bridge =
  ℚₚ.≤-trans
    (physicalCutoffFluxDominatedByPairIncidenceFold bridge)
    (physicalPairIncidenceMajorantSchurBound bridge)

luoCutoffFluxEstimate :
  (bridge : PhysicalCutoffFluxWeightedSchurBridge) →
  absoluteCutoffFlux bridge
    ≤ profileSchurConstant bridge
      * (cutoffEnergyMajorant bridge * lowPassGradientInfinity bridge)
luoCutoffFluxEstimate =
  physicalCutoffFluxDominatedByWeightedSchurMajorant

------------------------------------------------------------------------
-- Existing theorem reuse receipt.
------------------------------------------------------------------------

record PhysicalFluxExistingInfrastructureReceipt : Set where
  constructor infrastructure-receipt
  field
    finiteDirectConvolutionAlgebraClosed :
      Direct.finiteDirectConvolutionAlgebraClosed ≡ true

    positiveKernelCutoffUniformlySummable :
      PositiveKernel.outputRelocationPositiveKernelCutoffUniformlySummable
        ≡ true

    lerayProjectedModeSquaredBoundClosed :
      Leray.rationalProjectedModeSquaredBoundClosed ≡ true

open PhysicalFluxExistingInfrastructureReceipt public

physicalFluxExistingInfrastructureReceipt :
  PhysicalFluxExistingInfrastructureReceipt
physicalFluxExistingInfrastructureReceipt = infrastructure-receipt
  Direct.finiteDirectConvolutionAlgebraClosedIsTrue
  PositiveKernel.outputRelocationPositiveKernelCutoffUniformlySummableIsTrue
  Leray.rationalProjectedModeSquaredBoundClosedIsTrue

hermitianPairIncidenceAtomConstructed : Bool
hermitianPairIncidenceAtomConstructed = true

multiplicitySafeFibreTheoremConstructed : Bool
multiplicitySafeFibreTheoremConstructed = true

finiteFluxToIncidenceMajorantConstructed : Bool
finiteFluxToIncidenceMajorantConstructed = true

weightedSchurToLuoFluxCompositionConstructed : Bool
weightedSchurToLuoFluxCompositionConstructed = true

exactPhysicalProjectedConvolutionEnumerationClosed : Bool
exactPhysicalProjectedConvolutionEnumerationClosed = false

physicalTriadCoefficientDominationClosed : Bool
physicalTriadCoefficientDominationClosed = false

physicalWeightedSchurBridgeInhabited : Bool
physicalWeightedSchurBridgeInhabited = false

hermitianPairIncidenceAtomConstructedIsTrue :
  hermitianPairIncidenceAtomConstructed ≡ true
hermitianPairIncidenceAtomConstructedIsTrue = refl

multiplicitySafeFibreTheoremConstructedIsTrue :
  multiplicitySafeFibreTheoremConstructed ≡ true
multiplicitySafeFibreTheoremConstructedIsTrue = refl

finiteFluxToIncidenceMajorantConstructedIsTrue :
  finiteFluxToIncidenceMajorantConstructed ≡ true
finiteFluxToIncidenceMajorantConstructedIsTrue = refl

weightedSchurToLuoFluxCompositionConstructedIsTrue :
  weightedSchurToLuoFluxCompositionConstructed ≡ true
weightedSchurToLuoFluxCompositionConstructedIsTrue = refl

exactPhysicalProjectedConvolutionEnumerationClosedIsFalse :
  exactPhysicalProjectedConvolutionEnumerationClosed ≡ false
exactPhysicalProjectedConvolutionEnumerationClosedIsFalse = refl

physicalTriadCoefficientDominationClosedIsFalse :
  physicalTriadCoefficientDominationClosed ≡ false
physicalTriadCoefficientDominationClosedIsFalse = refl

physicalWeightedSchurBridgeInhabitedIsFalse :
  physicalWeightedSchurBridgeInhabited ≡ false
physicalWeightedSchurBridgeInhabitedIsFalse = refl
