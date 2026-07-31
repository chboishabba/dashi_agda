module DASHI.Physics.YangMills.BalabanClayGate4Attachment254ResearchAuditExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source and authority audit for the July 2026 attachment.
--
-- Empirical corroboration (not theorem authority for the RG construction):
--
-- M. Nauenberg, T. Schalk, and R. Brower,
-- "Finite-size scaling and asymptotic freedom of the SU(2) lattice gauge
-- model", Physical Review D 24 (1981), 548--551.
-- DOI: 10.1103/PhysRevD.24.548.
--
-- The Monte Carlo fit reports gamma_0 = 0.041 and compares it with the paper's
-- SU(2) perturbative convention gamma_0 = 11/(24 pi^2) = 0.046....  This is
-- independent numerical corroboration of asymptotic freedom.  It is not a
-- direct numerical confirmation of DASHI's inverse-coupling coefficient
-- 11 C_A/(24 pi^2): at C_A = 2 that coefficient is 11/(12 pi^2).  A typed
-- convention map is therefore required before the two constants may be
-- identified.
--
-- Primary and peer-reviewed methodological provenance:
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban, I. Small Fields",
-- Reviews in Mathematical Physics 25 (2013), 1330010.
-- DOI: 10.1142/S0129055X13300100; arXiv:1108.1335.
-- Dimock is an expository scalar-phi^4 implementation of Bałaban's method.  It
-- is admissible as methodological provenance, not as a physical Yang--Mills
-- identification theorem.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
-- Corollary 2.14 gives the exact finite relative-determinant difference bound;
-- the exponential multiplier is a separately derived weakening.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
-- This supplies the finite Hermitian Rayleigh/min--max and inverse-spectrum
-- facts used below.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- This supplies the standard SU(2) exponential/principal-log chart theorem.
-- The literal radius pi depends on the selected Lie-algebra norm convention and
-- therefore still requires a physical normalization proof.
--
-- Hans Koch and Peter Wittwer,
-- "On the Renormalization Group Transformation for Scalar Hierarchical
-- Models", Communications in Mathematical Physics 138 (1991), 537--568.
-- DOI: 10.1007/BF02102041.
-- This is methodological precedent for controlled correction/slack sequences;
-- it is not authority for the numerical Q-star bounds in lattice Yang--Mills.
------------------------------------------------------------------------

nauenbergSchalkBrowerMetadataLevel : ProofLevel
nauenbergSchalkBrowerMetadataLevel = standardImported

monteCarloAsymptoticFreedomCorroborationLevel : ProofLevel
monteCarloAsymptoticFreedomCorroborationLevel = standardImported

monteCarloGammaConventionEqualsRepositoryInverseCouplingConvention : ProofLevel
monteCarloGammaConventionEqualsRepositoryInverseCouplingConvention = conjectural

monteCarloCorroborationProvesPhysicalBalabanCoefficient : ProofLevel
monteCarloCorroborationProvesPhysicalBalabanCoefficient = conjectural

balabanQuadraticExpansionArchitectureLevel : ProofLevel
balabanQuadraticExpansionArchitectureLevel = standardImported

dimockSmallFieldMethodologicalProvenanceLevel : ProofLevel
dimockSmallFieldMethodologicalProvenanceLevel = standardImported

dimockScalarFlowProvesYangMillsFlowLevel : ProofLevel
dimockScalarFlowProvesYangMillsFlowLevel = conjectural

su2PrincipalLogBallTheoremLevel : ProofLevel
su2PrincipalLogBallTheoremLevel = standardImported

selfAdjointRayleighNormTheoremLevel : ProofLevel
selfAdjointRayleighNormTheoremLevel = standardImported

finiteHermitianMinMaxTheoremLevel : ProofLevel
finiteHermitianMinMaxTheoremLevel = standardImported

ipsenRehmanCorollary214Level : ProofLevel
ipsenRehmanCorollary214Level = standardImported

kochWittwerSlackMethodologyLevel : ProofLevel
kochWittwerSlackMethodologyLevel = standardImported

physicalSU2ChartNormalizationInputsLevel : ProofLevel
physicalSU2ChartNormalizationInputsLevel = conditional

physicalRestrictedRemainderSelfAdjointInputsLevel : ProofLevel
physicalRestrictedRemainderSelfAdjointInputsLevel = conditional

physicalQstarSlackSequenceInputsLevel : ProofLevel
physicalQstarSlackSequenceInputsLevel = conditional

physicalBetaConventionMapInputsLevel : ProofLevel
physicalBetaConventionMapInputsLevel = conditional

physicalBetaRemainderAndAdmissibilityInputsLevel : ProofLevel
physicalBetaRemainderAndAdmissibilityInputsLevel = conditional
