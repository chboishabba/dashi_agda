{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedIBPWavefunctionSymmetryWeldRound205Exact where

------------------------------------------------------------------------
-- ROUND205 BIDI: CONSUME THE EXISTING SELECTED FINITE IBP LAW ON THE CORRECT
-- WAVEFUNCTION HAMILTONIAN CARRIER.
--
-- The repository already owns an exact selected finite integration-by-parts
-- equation
--
--   delta S = <EL , delta A> + boundary.
--
-- R202--R204 put the terminal Hamiltonian on gauge-invariant wavefunctions and
-- reduce symmetry to
--
--   <H f , g> = <f , H g>.
--
-- This module does not pretend those two pairings are definitionally the same.
-- Instead it isolates the two SAME-OBJECT realization payments that make the
-- existing IBP theorem usable:
--
--   (1) the selected action variation evaluates to <H f , g>;
--   (2) the complete selected IBP right-hand side (including the physical
--       boundary convention) evaluates to <f , H g>.
--
-- Once those identifications are supplied, symmetry is a three-step equality;
-- gauge-quotient descent is already automatic from R202.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFiniteRootedGaugeQuotientL2Round197Exact as R197
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact as R203
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionSymmetricOperatorRound204Exact as R204
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as IBP
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs

record SelectedIBPWavefunctionSymmetryWeld
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (ensemble : R197.FiniteRootedQuotientEnsemble group base paths) : Set₁ where
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

    -- Interpret the selected finite action-scalar carrier in the exact rational
    -- pairing carrier used by R197/R203.  No algebraic laws are silently assumed
    -- here; the complete RHS realization below carries the required boundary
    -- convention and scalar-combination semantics.
    scalarValue :
      YMObs.YMSFGCUserSuppliedActionScalarCarrier → ℚ

    leftPairingIsSelectedActionVariation :
      ∀ left right →
      R203.finiteWavefunctionPairing ensemble
        (R202.act operator left) right
      ≡ scalarValue
          (IBP.strictSelectedActionVariation
            (connectionFor left right)
            (variationFor left right))

    selectedIBPRightSideIsRightPairing :
      ∀ left right →
      scalarValue
        (IBP.strictActionScalarCombine
          (IBP.strictSelectedHodgeVariationPairing
            (connectionFor left right)
            (variationFor left right))
          (IBP.strictSelectedBoundaryTerm
            (connectionFor left right)
            (variationFor left right)))
      ≡ R203.finiteWavefunctionPairing ensemble
          left (R202.act operator right)

open SelectedIBPWavefunctionSymmetryWeld public

selectedIBPImpliesWavefunctionSymmetry :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {ensemble : R197.FiniteRootedQuotientEnsemble group base paths}
    (weld : SelectedIBPWavefunctionSymmetryWeld
      group base paths ensemble) →
  ∀ left right →
  R203.finiteWavefunctionPairing ensemble
    (R202.act (operator weld) left) right
  ≡ R203.finiteWavefunctionPairing ensemble
      left (R202.act (operator weld) right)
selectedIBPImpliesWavefunctionSymmetry weld left right =
  trans
    (leftPairingIsSelectedActionVariation weld left right)
    (trans
      (cong (scalarValue weld)
        (IBP.strictSelectedDiscreteIBPLaw
          (connectionFor weld left right)
          (variationFor weld left right)))
      (selectedIBPRightSideIsRightPairing weld left right))

compileSelectedIBPToSymmetricWavefunctionOperator :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {ensemble : R197.FiniteRootedQuotientEnsemble group base paths} →
  SelectedIBPWavefunctionSymmetryWeld group base paths ensemble →
  R204.FiniteSymmetricGaugeInvariantOperator group base paths ensemble
compileSelectedIBPToSymmetricWavefunctionOperator weld = record
  { R204.FiniteSymmetricGaugeInvariantOperator.operator = operator weld
  ; R204.FiniteSymmetricGaugeInvariantOperator.symmetric =
      selectedIBPImpliesWavefunctionSymmetry weld
  }

selectedIBPWavefunctionSymmetryCompilerRound205Level : ProofLevel
selectedIBPWavefunctionSymmetryCompilerRound205Level = machineChecked

-- The old generic "missing symmetric finite form" blocker has now been reduced
-- to these physical same-object producers on the R202/R203 carrier.
literalFiniteYMHamiltonianAsSelectedActionVariationRound205Level : ProofLevel
literalFiniteYMHamiltonianAsSelectedActionVariationRound205Level = conditional

literalSelectedIBPRightSideAsWavefunctionPairingRound205Level : ProofLevel
literalSelectedIBPRightSideAsWavefunctionPairingRound205Level = conditional

literalPhysicalBoundaryCancellationRound205Level : ProofLevel
literalPhysicalBoundaryCancellationRound205Level = conditional
