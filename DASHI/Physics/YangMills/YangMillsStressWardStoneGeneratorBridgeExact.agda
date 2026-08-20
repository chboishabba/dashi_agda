module DASHI.Physics.YangMills.YangMillsStressWardStoneGeneratorBridgeExact where

------------------------------------------------------------------------
-- ROUND84: TRANSLATION WARD CHARGE -> SAME OS HAMILTONIAN BY STONE UNIQUENESS
--
-- PRIMARY SOURCES
--
-- Marshall H. Stone,
-- "On One-Parameter Unitary Groups in Hilbert Space",
-- Annals of Mathematics 33 (1932), 643--648.
-- DOI: 10.2307/1968538.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Sergio Caracciolo, Giuseppe Curci, Pietro Menotti and Andrea Pelissetto,
-- "The Energy-Momentum Tensor for Lattice Gauge Theories",
-- Annals of Physics 197 (1990), 119--153.
-- DOI: 10.1016/0003-4916(90)90203-Z.
--
-- MATHEMATICAL CUTSET CORRECTION
--
-- The old Clay cutset counted two stress lemmas:
--
--   C2a  construct T_{mu nu} and prove the translation Ward identity;
--   C2b  prove integral T_00 equals the OS Hamiltonian.
--
-- This double-counts standard functional analysis if C2a is stated at the
-- strength actually required.  The physical theorem must prove that the
-- renormalized smeared charge built from T_{0 nu} generates the SAME strongly
-- continuous translation group on a common invariant dense core.  Once that is
-- true, Stone's theorem gives uniqueness of the self-adjoint generator.  No
-- second four-dimensional Yang--Mills estimate remains.
--
-- IMPORTANT: mere local conservation d^mu T_{mu nu}=0 is NOT promoted to this
-- conclusion.  Smearing, removal of spatial cutoffs, common-core/domain control,
-- absence of an anomalous translation term, and equality of the generated
-- translation action are all retained in the physical Ward-generator premise.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact

-- Standard theorem: a strongly continuous one-parameter unitary group has a
-- unique self-adjoint infinitesimal generator.
stoneSelfAdjointGeneratorUniquenessLevel : ProofLevel
stoneSelfAdjointGeneratorUniquenessLevel = standardImported

-- Standard corollary: if two self-adjoint operators generate the same strongly
-- continuous unitary group, they are the same operator (hence same domain and
-- spectral gap).
sameUnitaryTranslationGroupImpliesSameGeneratorLevel : ProofLevel
sameUnitaryTranslationGroupImpliesSameGeneratorLevel = standardImported

-- OS reconstruction already supplies the physical time-translation semigroup /
-- unitary group and its positive self-adjoint Hamiltonian on the reconstructed
-- Hilbert space once the continuum OS axioms are available.
osReconstructedTranslationGeneratorLevel : ProofLevel
osReconstructedTranslationGeneratorLevel = standardImported

-- The ONE remaining Yang--Mills stress theorem must be strong enough to feed
-- Stone uniqueness.  This combines what the old C2a/C2b split had separated:
--
--   * construct/renormalize symmetric local T_{mu nu} on the same continuum;
--   * establish the translation Ward identity;
--   * define spatially-cutoff smeared charges and remove the cutoff;
--   * prove the limiting charge is self-adjoint/essentially self-adjoint on a
--     common invariant local core;
--   * prove its exponentials implement the SAME reconstructed translations.
--
-- After these physical statements there is no independent theorem
-- `integral T00 = H_OS`; it is the standard uniqueness conclusion above.
physicalStressWardGeneratesSameOSTranslationsLevel : ProofLevel
physicalStressWardGeneratesSameOSTranslationsLevel = conditional

stressChargeEqualsOSHamiltonianAfterGeneratorIdentificationLevel : ProofLevel
stressChargeEqualsOSHamiltonianAfterGeneratorIdentificationLevel = standardImported
