module DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Eliminate the remaining scalar equality receipt between the physical
-- selected variation and the correlated owner ledger.  A literal raw-
-- localization atom reconstruction and the exact pair-indexed Green expansion
-- canonically generate the residual family and prove
--
--   residual = RawLocalization - <Lg,K+Lw>.
--
-- The owner maps classify terms only; they cannot alter their values.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _-_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as GreenExpansion
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

record CorrelatedResidualAuthority
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (firstVariationCovector rawExtractor : KKT.StateVector) : Set₁ where
  field
    rawLocalization : ℚ
    rawLocalizationAtom : Cube.Subset4 → ℚ
    rawLocalizationReconstruct :
      Sums.sumRational Cube.nonemptySubsets4 rawLocalizationAtom
      ≡ rawLocalization

    constraintAtoms :
      Atoms.SelectedConstraintAtomData
        pseudoData firstVariationCovector rawExtractor

    rawOwnerOf : Cube.Subset4 → Ownership.CorrelatedResidualOwner
    greenOwnerOf :
      Cube.Subset4 → Cube.Subset4 → Ownership.MultiplierGreenAtomOwner

open CorrelatedResidualAuthority public

canonicalCorrelatedResidualFamily :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  CorrelatedResidualAuthority
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Ownership.CorrelatedResidualFamily
canonicalCorrelatedResidualFamily authority = record
  { Ownership.CorrelatedResidualFamily.rawLocalizationAtom =
      rawLocalizationAtom authority
  ; Ownership.CorrelatedResidualFamily.multiplierGreenAtom =
      GreenExpansion.greenAtomPairContraction
        (constraintAtoms authority)
  ; Ownership.CorrelatedResidualFamily.rawOwnerOf =
      rawOwnerOf authority
  ; Ownership.CorrelatedResidualFamily.greenOwnerOf =
      greenOwnerOf authority }

canonicalMultiplierGreenPairing :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    firstVariationCovector rawExtractor → ℚ
canonicalMultiplierGreenPairing pseudoData firstVariationCovector rawExtractor =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    (Pseudo.constraintApply pseudoData firstVariationCovector)
    (Pseudo.pseudoApply pseudoData
      (Pseudo.constraintApply pseudoData rawExtractor))

canonicalCorrelatedResidualExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (authority : CorrelatedResidualAuthority
      {Multiplier} pseudoData firstVariationCovector rawExtractor) →
  Ownership.correlatedResidualTotal
    (canonicalCorrelatedResidualFamily authority)
  ≡ rawLocalization authority
    - canonicalMultiplierGreenPairing
        pseudoData firstVariationCovector rawExtractor
canonicalCorrelatedResidualExact
    {pseudoData = pseudoData}
    {firstVariationCovector = firstVariationCovector}
    {rawExtractor = rawExtractor}
    authority =
  cong₂ _-_
    (rawLocalizationReconstruct authority)
    (sym
      (GreenExpansion.constraintAtomGreenExpansionExact
        (constraintAtoms authority)))

canonicalCorrelatedResidualIsProjectedSpillover :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (authority : CorrelatedResidualAuthority
      {Multiplier} pseudoData firstVariationCovector rawExtractor) →
  Ownership.correlatedResidualTotal
    (canonicalCorrelatedResidualFamily authority)
  ≡ Sign.canonicalProjectedSpillover
      (rawLocalization authority)
      (canonicalMultiplierGreenPairing
        pseudoData firstVariationCovector rawExtractor)
canonicalCorrelatedResidualIsProjectedSpillover authority =
  canonicalCorrelatedResidualExact authority

correlatedResidualAuthorityLevel : ProofLevel
correlatedResidualAuthorityLevel = machineChecked
