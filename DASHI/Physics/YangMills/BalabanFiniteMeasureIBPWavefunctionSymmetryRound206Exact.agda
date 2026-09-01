{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteMeasureIBPWavefunctionSymmetryRound206Exact where

------------------------------------------------------------------------
-- ROUND206 BIDI: SELECTED FINITE IBP -> SAME-MEASURE WAVEFUNCTION SYMMETRY.
--
-- R205 puts gauge-invariant wavefunctions on a theorem-bearing finite-measure
-- pairing.  The repository already owns the strict selected discrete IBP law
--
--   delta S = <EL , delta A> + boundary.
--
-- A sample-level bridge is useful diagnostically, but it is not the physical
-- target.  This owner compiles the existing IBP equality directly into
--
--   <H psi , phi>_mu = <psi , H phi>_mu
--
-- on the SAME finite-measure pairing from R205.  The only remaining physical
-- payments are same-object identifications of the two IBP sides with those
-- pairings (including the boundary convention) and the actual Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact as R205
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as IBP
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs

record FiniteMeasureIBPWavefunctionSymmetryWeld
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (Measure : Set)
    (semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure) : Set₁ where
  field
    operator : R202.GaugeInvariantWavefunctionOperator group base

    connectionFor :
      R202.BasedGaugeInvariantWavefunction group base →
      R202.BasedGaugeInvariantWavefunction group base →
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier

    variationFor :
      R202.BasedGaugeInvariantWavefunction group base →
      R202.BasedGaugeInvariantWavefunction group base →
      YMObs.YMSFGCUserSuppliedVariationCarrier

    scalarValue :
      YMObs.YMSFGCUserSuppliedActionScalarCarrier → ℚ

    leftMeasurePairingIsSelectedActionVariation :
      ∀ left right →
      R205.finiteMeasureWavefunctionPairing semantics
        (R202.act operator left) right
      ≡ scalarValue
          (IBP.strictSelectedActionVariation
            (connectionFor left right)
            (variationFor left right))

    selectedIBPRightSideIsRightMeasurePairing :
      ∀ left right →
      scalarValue
        (IBP.strictActionScalarCombine
          (IBP.strictSelectedHodgeVariationPairing
            (connectionFor left right)
            (variationFor left right))
          (IBP.strictSelectedBoundaryTerm
            (connectionFor left right)
            (variationFor left right)))
      ≡ R205.finiteMeasureWavefunctionPairing semantics
          left (R202.act operator right)

open FiniteMeasureIBPWavefunctionSymmetryWeld public

selectedIBPImpliesSameMeasureWavefunctionSymmetry :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    (weld : FiniteMeasureIBPWavefunctionSymmetryWeld
      group base Measure semantics) →
  ∀ left right →
  R205.finiteMeasureWavefunctionPairing semantics
    (R202.act (operator weld) left) right
  ≡ R205.finiteMeasureWavefunctionPairing semantics
      left (R202.act (operator weld) right)
selectedIBPImpliesSameMeasureWavefunctionSymmetry weld left right =
  trans
    (leftMeasurePairingIsSelectedActionVariation weld left right)
    (trans
      (cong (scalarValue weld)
        (IBP.strictSelectedDiscreteIBPLaw
          (connectionFor weld left right)
          (variationFor weld left right)))
      (selectedIBPRightSideIsRightMeasurePairing weld left right))

finiteMeasureIBPWavefunctionSymmetryRound206Level : ProofLevel
finiteMeasureIBPWavefunctionSymmetryRound206Level = machineChecked

-- Exact physical leaves after the algebraic IBP compiler is removed.
literalPhysicalYMHamiltonianAsSelectedActionVariationRound206Level : ProofLevel
literalPhysicalYMHamiltonianAsSelectedActionVariationRound206Level = conditional

literalSelectedIBPRightSideAsFiniteMeasurePairingRound206Level : ProofLevel
literalSelectedIBPRightSideAsFiniteMeasurePairingRound206Level = conditional

literalPhysicalBoundaryConventionRound206Level : ProofLevel
literalPhysicalBoundaryConventionRound206Level = conditional

-- Symmetry is not self-adjointness.  The latter additionally needs the completed
-- L2 carrier, an operator domain and the relevant closure/essential-self-adjoint
-- theorem on that same measure.
literalFiniteMeasureHamiltonianSelfAdjointnessRound206Level : ProofLevel
literalFiniteMeasureHamiltonianSelfAdjointnessRound206Level = conditional
