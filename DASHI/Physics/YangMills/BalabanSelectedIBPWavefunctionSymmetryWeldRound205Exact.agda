{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedIBPWavefunctionSymmetryWeldRound205Exact where

------------------------------------------------------------------------
-- ROUND205 BIDI: SELECTED FINITE IBP -> SAMPLE-LOCAL WAVEFUNCTION SYMMETRY.
--
-- The repository owns the theorem-bearing selected finite IBP equation
--
--   delta S = <EL , delta A> + boundary.
--
-- R202 supplies the correct Hamiltonian carrier (gauge-invariant
-- wavefunctions); R203B/R204 use only an explicitly finite sample of rooted
-- quotient points.  This owner isolates the SAME-OBJECT realization payments
-- needed to consume the selected IBP theorem without claiming that the sample
-- is exhaustive or that its pairing is the physical Haar/Gibbs L2 pairing.
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
import DASHI.Physics.YangMills.BalabanFiniteSampleObservablePairingRound203Exact as Sample
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact as R203
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionSymmetricOperatorRound204Exact as R204
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as IBP
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs

record SelectedIBPWavefunctionSampleSymmetryWeld
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (sample : Sample.FiniteSample
      (R203.RootedQuotient {group = group} {base = base} {paths = paths})) : Set₁ where
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

    leftSamplePairingIsSelectedActionVariation :
      ∀ left right →
      R203.finiteWavefunctionSamplePairing sample
        (R202.act operator left) right
      ≡ scalarValue
          (IBP.strictSelectedActionVariation
            (connectionFor left right)
            (variationFor left right))

    selectedIBPRightSideIsRightSamplePairing :
      ∀ left right →
      scalarValue
        (IBP.strictActionScalarCombine
          (IBP.strictSelectedHodgeVariationPairing
            (connectionFor left right)
            (variationFor left right))
          (IBP.strictSelectedBoundaryTerm
            (connectionFor left right)
            (variationFor left right)))
      ≡ R203.finiteWavefunctionSamplePairing sample
          left (R202.act operator right)

open SelectedIBPWavefunctionSampleSymmetryWeld public

selectedIBPImpliesWavefunctionSampleSymmetry :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {sample : Sample.FiniteSample
      (R203.RootedQuotient {group = group} {base = base} {paths = paths})}
    (weld : SelectedIBPWavefunctionSampleSymmetryWeld
      group base paths sample) →
  ∀ left right →
  R203.finiteWavefunctionSamplePairing sample
    (R202.act (operator weld) left) right
  ≡ R203.finiteWavefunctionSamplePairing sample
      left (R202.act (operator weld) right)
selectedIBPImpliesWavefunctionSampleSymmetry weld left right =
  trans
    (leftSamplePairingIsSelectedActionVariation weld left right)
    (trans
      (cong (scalarValue weld)
        (IBP.strictSelectedDiscreteIBPLaw
          (connectionFor weld left right)
          (variationFor weld left right)))
      (selectedIBPRightSideIsRightSamplePairing weld left right))

compileSelectedIBPToSampleSymmetricWavefunctionOperator :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {sample : Sample.FiniteSample
      (R203.RootedQuotient {group = group} {base = base} {paths = paths})} →
  SelectedIBPWavefunctionSampleSymmetryWeld group base paths sample →
  R204.FiniteSampleSymmetricGaugeInvariantOperator group base paths sample
compileSelectedIBPToSampleSymmetricWavefunctionOperator weld = record
  { R204.FiniteSampleSymmetricGaugeInvariantOperator.operator = operator weld
  ; R204.FiniteSampleSymmetricGaugeInvariantOperator.symmetricOnSample =
      selectedIBPImpliesWavefunctionSampleSymmetry weld
  }

selectedIBPWavefunctionSampleSymmetryCompilerRound205Level : ProofLevel
selectedIBPWavefunctionSampleSymmetryCompilerRound205Level = machineChecked

-- Genuine physical leaves: these require a real YM Hamiltonian and physical
-- measure/pairing, not merely the sample-local compiler above.
literalPhysicalYMHamiltonianAsSelectedActionVariationRound205Level : ProofLevel
literalPhysicalYMHamiltonianAsSelectedActionVariationRound205Level = conditional

literalSelectedIBPRightSideAsPhysicalL2PairingRound205Level : ProofLevel
literalSelectedIBPRightSideAsPhysicalL2PairingRound205Level = conditional

literalPhysicalBoundaryCancellationRound205Level : ProofLevel
literalPhysicalBoundaryCancellationRound205Level = conditional
