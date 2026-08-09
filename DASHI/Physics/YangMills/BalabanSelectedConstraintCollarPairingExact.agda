module DASHI.Physics.YangMills.BalabanSelectedConstraintCollarPairingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Turn row locality of delta_(p,h)=Lw_(p,h) into an exact finite theorem while
-- retaining redundant constraint rows.  A Boolean collar mask and a proof that
-- the literal raw defect vanishes outside it imply
--
--   <lambda,delta> = <chi_C lambda,delta>.
--
-- A multiplier supported outside the collar annihilates the defect exactly.
-- No norm estimate or absolute value is used in this localization step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms

record RawExtractorConstraintCollar
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₁ where
  field
    collarMask : Multiplier → Bool
    defectOutsideCollarZero : ∀ row →
      collarMask row ≡ false →
      Atoms.rawExtractorConstraintDefect
        pseudoData bondField plaquette row
      ≡ 0ℚ

open RawExtractorConstraintCollar public

restrictMultiplierToCollar :
  ∀ {Multiplier pseudoData bondField plaquette} →
  RawExtractorConstraintCollar
    {Multiplier} pseudoData bondField plaquette →
  (Multiplier → ℚ) → Multiplier → ℚ
restrictMultiplierToCollar collar multiplier row
  with collarMask collar row
... | false = 0ℚ
... | true = multiplier row

rawExtractorDefectSupportedOnConstraintCollar :
  ∀ {Multiplier pseudoData bondField plaquette}
    (collar : RawExtractorConstraintCollar
      {Multiplier} pseudoData bondField plaquette)
    row →
  collarMask collar row ≡ false →
  Atoms.rawExtractorConstraintDefect
    pseudoData bondField plaquette row
  ≡ 0ℚ
rawExtractorDefectSupportedOnConstraintCollar collar =
  defectOutsideCollarZero collar

collarRestrictionPreservesPairingTerm :
  ∀ {Multiplier pseudoData bondField plaquette}
    (collar : RawExtractorConstraintCollar
      {Multiplier} pseudoData bondField plaquette)
    multiplier row →
  multiplier row
    * Atoms.rawExtractorConstraintDefect
        pseudoData bondField plaquette row
  ≡ restrictMultiplierToCollar collar multiplier row
    * Atoms.rawExtractorConstraintDefect
        pseudoData bondField plaquette row
collarRestrictionPreservesPairingTerm collar multiplier row
  with collarMask collar row
... | true = refl
... | false
  rewrite defectOutsideCollarZero collar row refl =
  ℚRing.solve []

multiplierPairingRestrictsToConstraintCollar :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    bondField plaquette
    (collar : RawExtractorConstraintCollar
      pseudoData bondField plaquette)
    multiplier →
  Rect.finiteDot (Pseudo.multiplierCarrier pseudoData) multiplier
    (Atoms.rawExtractorConstraintDefect
      pseudoData bondField plaquette)
  ≡ Rect.finiteDot (Pseudo.multiplierCarrier pseudoData)
      (restrictMultiplierToCollar collar multiplier)
      (Atoms.rawExtractorConstraintDefect
        pseudoData bondField plaquette)
multiplierPairingRestrictsToConstraintCollar
    pseudoData bondField plaquette collar multiplier =
  Sums.sumRationalCong
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (λ row →
      multiplier row
        * Atoms.rawExtractorConstraintDefect
            pseudoData bondField plaquette row)
    (λ row →
      restrictMultiplierToCollar collar multiplier row
        * Atoms.rawExtractorConstraintDefect
            pseudoData bondField plaquette row)
    (collarRestrictionPreservesPairingTerm collar multiplier)

record OutsideCollarMultiplier
    {Multiplier : Set}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {bondField : Coordinates.PhysicalSU2BondField4}
    {plaquette : Physical.Plaquette4}
    (collar : RawExtractorConstraintCollar
      pseudoData bondField plaquette)
    (multiplier : Multiplier → ℚ) : Set where
  field
    zeroOnCollar : ∀ row →
      collarMask collar row ≡ true →
      multiplier row ≡ 0ℚ

open OutsideCollarMultiplier public

outsideCollarTermZero :
  ∀ {Multiplier pseudoData bondField plaquette}
    {collar : RawExtractorConstraintCollar
      {Multiplier} pseudoData bondField plaquette}
    {multiplier : Multiplier → ℚ} →
  OutsideCollarMultiplier collar multiplier →
  ∀ row →
  multiplier row
    * Atoms.rawExtractorConstraintDefect
        pseudoData bondField plaquette row
  ≡ 0ℚ
outsideCollarTermZero {collar = collar} {multiplier = multiplier}
    outside row with collarMask collar row
... | true
  rewrite zeroOnCollar outside row refl =
  ℚRing.solve []
... | false
  rewrite defectOutsideCollarZero collar row refl =
  ℚRing.solve []

outsideCollarMultiplierAnnihilatesDefect :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    bondField plaquette
    (collar : RawExtractorConstraintCollar
      pseudoData bondField plaquette)
    multiplier →
  OutsideCollarMultiplier collar multiplier →
  Rect.finiteDot (Pseudo.multiplierCarrier pseudoData) multiplier
    (Atoms.rawExtractorConstraintDefect
      pseudoData bondField plaquette)
  ≡ 0ℚ
outsideCollarMultiplierAnnihilatesDefect
    pseudoData bondField plaquette collar multiplier outside =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (λ row →
        multiplier row
          * Atoms.rawExtractorConstraintDefect
              pseudoData bondField plaquette row)
      (λ _ → 0ℚ)
      (outsideCollarTermZero outside))
    (Fubini.sumRationalZero
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)))

constraintCollarLocalizationLevel : ProofLevel
constraintCollarLocalizationLevel = machineChecked

selectedPhysicalConstraintCollarProducerLevel : ProofLevel
selectedPhysicalConstraintCollarProducerLevel = conditional
