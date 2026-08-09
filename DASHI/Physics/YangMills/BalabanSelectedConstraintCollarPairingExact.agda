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
-- DASHI CONTRIBUTION
--
-- Turn the row-locality observation for delta_(p,h)=Lw_(p,h) into an exact
-- finite theorem.  A Boolean constraint-collar mask and a proof that the raw
-- defect vanishes outside it imply
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
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectExact as RawDefect

record RawExtractorConstraintCollar
    {Multiplier : Set}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₁ where
  field
    collarMask : Multiplier → Bool
    defectOutsideCollarZero : ∀ row →
      collarMask row ≡ false →
      RawDefect.rawExtractorConstraintDefect
        projectorData bondField plaquette row
      ≡ 0ℚ

open RawExtractorConstraintCollar public

restrictMultiplierToCollar :
  ∀ {Multiplier projectorData bondField plaquette} →
  RawExtractorConstraintCollar
    {Multiplier} projectorData bondField plaquette →
  (Multiplier → ℚ) → Multiplier → ℚ
restrictMultiplierToCollar collar multiplier row
  with collarMask collar row
... | false = 0ℚ
... | true = multiplier row

rawExtractorDefectSupportedOnConstraintCollar :
  ∀ {Multiplier projectorData bondField plaquette}
    (collar : RawExtractorConstraintCollar
      {Multiplier} projectorData bondField plaquette)
    row →
  collarMask collar row ≡ false →
  RawDefect.rawExtractorConstraintDefect
    projectorData bondField plaquette row
  ≡ 0ℚ
rawExtractorDefectSupportedOnConstraintCollar collar =
  defectOutsideCollarZero collar

collarRestrictionPreservesPairingTerm :
  ∀ {Multiplier projectorData bondField plaquette}
    (collar : RawExtractorConstraintCollar
      {Multiplier} projectorData bondField plaquette)
    multiplier row →
  multiplier row
    * RawDefect.rawExtractorConstraintDefect
        projectorData bondField plaquette row
  ≡ restrictMultiplierToCollar collar multiplier row
    * RawDefect.rawExtractorConstraintDefect
        projectorData bondField plaquette row
collarRestrictionPreservesPairingTerm collar multiplier row
  with collarMask collar row
... | true = refl
... | false
  rewrite defectOutsideCollarZero collar row refl =
  ℚRing.solve []

multiplierPairingRestrictsToConstraintCollar :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    bondField plaquette
    (collar : RawExtractorConstraintCollar
      projectorData bondField plaquette)
    multiplier →
  KKT.multiplierDot projectorData multiplier
    (RawDefect.rawExtractorConstraintDefect
      projectorData bondField plaquette)
  ≡ KKT.multiplierDot projectorData
      (restrictMultiplierToCollar collar multiplier)
      (RawDefect.rawExtractorConstraintDefect
        projectorData bondField plaquette)
multiplierPairingRestrictsToConstraintCollar
    projectorData bondField plaquette collar multiplier =
  Sums.sumRationalCong
    (Matrix.coordinates (KKT.multiplierCarrier projectorData))
    (λ row →
      multiplier row
        * RawDefect.rawExtractorConstraintDefect
            projectorData bondField plaquette row)
    (λ row →
      restrictMultiplierToCollar collar multiplier row
        * RawDefect.rawExtractorConstraintDefect
            projectorData bondField plaquette row)
    (collarRestrictionPreservesPairingTerm collar multiplier)

record OutsideCollarMultiplier
    {Multiplier : Set}
    {projectorData : KKT.FiniteKKTProjectorData Multiplier}
    {bondField : Coordinates.PhysicalSU2BondField4}
    {plaquette : Physical.Plaquette4}
    (collar : RawExtractorConstraintCollar
      projectorData bondField plaquette)
    (multiplier : Multiplier → ℚ) : Set where
  field
    zeroOnCollar : ∀ row →
      collarMask collar row ≡ true →
      multiplier row ≡ 0ℚ

open OutsideCollarMultiplier public

outsideCollarTermZero :
  ∀ {Multiplier projectorData bondField plaquette}
    {collar : RawExtractorConstraintCollar
      {Multiplier} projectorData bondField plaquette}
    {multiplier : Multiplier → ℚ} →
  OutsideCollarMultiplier collar multiplier →
  ∀ row →
  multiplier row
    * RawDefect.rawExtractorConstraintDefect
        projectorData bondField plaquette row
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
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    bondField plaquette
    (collar : RawExtractorConstraintCollar
      projectorData bondField plaquette)
    multiplier →
  OutsideCollarMultiplier collar multiplier →
  KKT.multiplierDot projectorData multiplier
    (RawDefect.rawExtractorConstraintDefect
      projectorData bondField plaquette)
  ≡ 0ℚ
outsideCollarMultiplierAnnihilatesDefect
    projectorData bondField plaquette collar multiplier outside =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates (KKT.multiplierCarrier projectorData))
      (λ row →
        multiplier row
          * RawDefect.rawExtractorConstraintDefect
              projectorData bondField plaquette row)
      (λ _ → 0ℚ)
      (outsideCollarTermZero outside))
    (Fubini.sumRationalZero
      (Matrix.coordinates (KKT.multiplierCarrier projectorData)))

constraintCollarLocalizationLevel : ProofLevel
constraintCollarLocalizationLevel = machineChecked

selectedPhysicalConstraintCollarProducerLevel : ProofLevel
selectedPhysicalConstraintCollarProducerLevel = conditional
