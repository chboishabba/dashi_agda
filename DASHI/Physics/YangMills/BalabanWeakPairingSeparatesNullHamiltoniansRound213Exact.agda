{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWeakPairingSeparatesNullHamiltoniansRound213Exact where

------------------------------------------------------------------------
-- ROUND213 BIDI: WEAK PAIRING EQUALITY DETERMINES THE SAME NULL-QUOTIENT H.
--
-- R212 already constructs the unique descended Hamiltonian once a raw
-- gauge-invariant-wavefunction operator preserves the R205 measure-null
-- relation.  The remaining Stone/YM seam should not be attacked by building
-- two unrelated quotient operators and comparing their implementations.
--
-- The least consumer-relevant uniqueness hypothesis is separation of null
-- classes by the SAME R205 finite-measure pairing.  Under that hypothesis,
-- equality of all weak matrix elements
--
--      < H1 psi , phi >_mu = < H2 psi , phi >_mu
--
-- forces H1 psi and H2 psi into the same measure-null class, hence R212's
-- quotient projection identifies their descended actions pointwise.
--
-- This is the exact weak-form compiler needed before using the already-owned
-- Stone generator-uniqueness route.  It does not manufacture a Hilbert
-- completion, dense domain, self-adjointness, strong continuity, or physical
-- equality of the Stone/YM weak matrix elements.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact as R205
import DASHI.Physics.YangMills.BalabanNullQuotientHamiltonianDescentRound209Exact as R209
import DASHI.Physics.YangMills.BalabanMeasureNullCanonicalQuotientHamiltonianRound212Exact as R212

record PairingSeparatesMeasureNullClasses
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (Measure : Set)
    (semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure) : Set₁ where
  field
    separates :
      ∀ {left right} →
      (∀ test →
        R205.finiteMeasureWavefunctionPairing semantics left test
        ≡ R205.finiteMeasureWavefunctionPairing semantics right test) →
      R205.NullEquivalent semantics left right

open PairingSeparatesMeasureNullClasses public

-- Weak equality on every admitted test wavefunction is already enough for the
-- physical quotient consumer: the outputs lie in the same null class.
weakPairingEqualityImpliesNullEquivalentOutputs :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure} →
  PairingSeparatesMeasureNullClasses group base Measure semantics →
  (left right : R209.NullRespectingWavefunctionOperator group base Measure semantics) →
  (∀ wavefunction test →
    R205.finiteMeasureWavefunctionPairing semantics
      (R202.act (R209.operator left) wavefunction) test
    ≡ R205.finiteMeasureWavefunctionPairing semantics
      (R202.act (R209.operator right) wavefunction) test) →
  ∀ wavefunction →
  R205.NullEquivalent semantics
    (R202.act (R209.operator left) wavefunction)
    (R202.act (R209.operator right) wavefunction)
weakPairingEqualityImpliesNullEquivalentOutputs separation left right weakEqual wavefunction =
  separates separation (weakEqual wavefunction)

-- Main compiler: two null-preserving raw operators with the same weak pairings
-- induce the SAME pointwise operator on the canonical R212 measure-null
-- quotient.  No function extensionality is used.
weakPairingEqualityImpliesSameDescendedHamiltonian :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    {Q : Set₁}
    (quotient : R212.CanonicalMeasureNullQuotient group base Measure semantics Q) →
  PairingSeparatesMeasureNullClasses group base Measure semantics →
  (left right : R209.NullRespectingWavefunctionOperator group base Measure semantics) →
  (∀ wavefunction test →
    R205.finiteMeasureWavefunctionPairing semantics
      (R202.act (R209.operator left) wavefunction) test
    ≡ R205.finiteMeasureWavefunctionPairing semantics
      (R202.act (R209.operator right) wavefunction) test) →
  ∀ q →
  R212.descendedHamiltonian quotient left q
  ≡ R212.descendedHamiltonian quotient right q
weakPairingEqualityImpliesSameDescendedHamiltonian
    quotient separation left right weakEqual q =
  R212.nullSound quotient
    (weakPairingEqualityImpliesNullEquivalentOutputs
      separation left right weakEqual (R212.section quotient q))

weakPairingSeparatesNullHamiltoniansRound213Level : ProofLevel
weakPairingSeparatesNullHamiltoniansRound213Level = machineChecked

weakPairingDeterminesDescendedHamiltonianRound213Level : ProofLevel
weakPairingDeterminesDescendedHamiltonianRound213Level = machineChecked

-- Same-object physical leaves.  The first must be inhabited for the literal
-- R205 Balaban measure semantics (or obtained from an already-owned stronger
-- definiteness theorem on that same carrier).  The second is the actual
-- Stone/YM weak generator identity on the common invariant domain.  Once both
-- are available, quotient-level operator equality is the theorem above rather
-- than a separate construction problem.
literalBalabanPairingSeparatesMeasureNullClassesRound213Level : ProofLevel
literalBalabanPairingSeparatesMeasureNullClassesRound213Level = conditional

literalPhysicalStoneYMWeakGeneratorPairingEqualityRound213Level : ProofLevel
literalPhysicalStoneYMWeakGeneratorPairingEqualityRound213Level = conditional

-- Standard Stone uniqueness remains downstream after completion/domain/strong
-- continuity: same strongly continuous unitary group -> same self-adjoint
-- generator.  R213 only removes an avoidable pre-completion operator-identity
-- payment.
stoneYMGeneratorIdentificationAfterSameActionRound213Level : ProofLevel
stoneYMGeneratorIdentificationAfterSameActionRound213Level = standardImported
