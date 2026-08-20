module DASHI.Algebra.ResidueDetectedUnitValuationExact where

------------------------------------------------------------------------
-- GENERIC RESIDUE -> UNIT-DEPTH BRIDGE
--
-- In a discretely valued local ring, an element has valuation zero exactly when
-- its residue is nonzero.  The Dwork/Legendre lane only needs the forward
-- direction:
--
--   nonzero residue  ->  valuation zero.
--
-- This module packages that implication without constructing Q_p, a residue
-- field, or a local ring.  A domain adapter supplies its genuine residue map
-- and the source-native theorem connecting residue nonvanishing to valuation.
--
-- This is useful for the exceptional Legendre factors because their
-- complementary-factor nonvanishing can be checked in the finite residue
-- geometry, while the valuation algebra consumes a depth-zero unit.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import DASHI.Core.Prelude

record ResidueDetectedUnitValuation
    {ℓA ℓR : Level}
    (A : Set ℓA)
    (R : Set ℓR) : Set (lsuc (ℓA ⊔ ℓR)) where
  field
    residueZero : R
    residue : A → R
    valuation : A → Nat

    residueNonzeroImpliesValuationZero :
      (x : A) →
      ¬ (residue x ≡ residueZero) →
      valuation x ≡ 0

open ResidueDetectedUnitValuation public

record ResidueUnitWitness
    {ℓA ℓR : Level}
    {A : Set ℓA}
    {R : Set ℓR}
    (V : ResidueDetectedUnitValuation A R)
    (x : A) : Set ℓR where
  field
    residueNonzero : ¬ (residue V x ≡ residueZero V)

open ResidueUnitWitness public

residueUnitHasDepthZero :
  {ℓA ℓR : Level} →
  {A : Set ℓA} → {R : Set ℓR} →
  (V : ResidueDetectedUnitValuation A R) →
  (x : A) →
  ResidueUnitWitness V x →
  valuation V x ≡ 0
residueUnitHasDepthZero V x witness =
  residueNonzeroImpliesValuationZero V x (residueNonzero witness)

record ResidueDetectedUnitValuationBoundary : Set where
  field
    residueCarrierAbstract : Bool
    residueNonzeroWitnessProofRelevant : Bool
    valuationZeroDerived : Bool
    QpConstructedHere : Bool
    residueFieldConstructedHere : Bool
    localRingUnitTheoremFabricatedWithoutAdapter : Bool

canonicalResidueDetectedUnitValuationBoundary :
  ResidueDetectedUnitValuationBoundary
canonicalResidueDetectedUnitValuationBoundary = record
  { residueCarrierAbstract = true
  ; residueNonzeroWitnessProofRelevant = true
  ; valuationZeroDerived = true
  ; QpConstructedHere = false
  ; residueFieldConstructedHere = false
  ; localRingUnitTheoremFabricatedWithoutAdapter = false
  }
