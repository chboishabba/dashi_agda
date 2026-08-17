module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound60FirstVariationGreenSurvivalValidation where

------------------------------------------------------------------------
-- ROUND 60 FOCUSED VALIDATION ROOT
--
-- Round60 returns to the shortest physical Clay cutset after Round59.  A1 is
-- closed on the literal Wilson first variation.  For A2/G2, the same finite
-- KKT Moore--Penrose inverse is proved PSD; polarization converts sixteen
-- signed Green cells to eight diagonal energies; and the finite symmetric
-- Schur theorem converts those eight energies to ONE common K+ row-mass bound
-- plus four source/four defect degree-vector norm-square bounds.  These are
-- compiled directly into the existing selected-minimizer endpoint theorem.
--
-- The continuum boundary also no longer forces reversibility when the
-- nonreversible/killed Lawler--Sokal regime is the literal one, records the
-- Chen--Wang general symmetric-form alternative with the 2000 full-paper
-- attribution, and keeps asymptotic freedom upstream of but distinct from
-- interacting continuum survival.
--
-- No theorem here promotes the still-open selected-region quantitative G2
-- endpoints, literal Wilson/ghost/Haar one-loop coefficient, five physical
-- g^4 channels, continuum Schwinger construction, OS passage, interacting
-- survival, physical clustering, or reconstruction.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound59PositiveRGGeometryValidation

-- A1.
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact

-- A2/G2 exact reductions.
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact
import DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact
import DASHI.Physics.YangMills.BalabanSelectedGreenDiagonalEndpointAdapterExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact
import DASHI.Physics.YangMills.BalabanUniformCanonicalDiagonalG2EnvelopeExact
import DASHI.Physics.YangMills.BalabanUniformCanonicalSchurNormG2EnvelopeExact

-- F1/F2 theorem selection.
import DASHI.Physics.YangMills.BalabanReversibleRGCheegerSpectralGapExact
import DASHI.Physics.YangMills.BalabanRGChenGeneralSymmetricFormBoundaryExact

-- B/C -> E3 quantitative gate, without beta>0 => non-Gaussian promotion.
import DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact
