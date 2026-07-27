module DASHI.Physics.YangMills.BalabanClayLiteralFrontierProducerBundle where

-- One import surface for the literal T2--T5 producer tranche.  The individual
-- modules keep their remaining local analytic hypotheses explicit; this bundle
-- performs no proof-level promotion by import alone.

-- Canonical authors/title/venue/DOI/arXiv/section/relationship metadata.
import DASHI.Physics.YangMills.BalabanClayLiteralFrontierVerifiedLiteratureExact

-- T3: reference coercivity, literal five-remainder decomposition, and physical
-- small-field Green/Schur reduction.
import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact
import DASHI.Physics.YangMills.BalabanClayT3LiteralPhysicalCoercivityProducerExact
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact

-- T2: action gain, all five non-action losses, rooted physical encoding, and
-- the exact Fernández--Procacci clique reduction.
import DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact
import DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact
import DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact
import DASHI.Physics.YangMills.BalabanClayT2PhysicalRootedPolymerEncodingExact

-- T4: localized projector plus literal Wilson/background one-loop and lattice
-- Brillouin-zone reduction.
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact
import DASHI.Physics.YangMills.BalabanClayT4LiteralVacuumPolarizationIntegralExact

-- T5: staged thermodynamic/continuum tails, exponential moments, uniform
-- integrability, complete Gram forms, and OS positivity transport.
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact

-- User-run authoritative typecheck receipt surface.
import DASHI.Physics.YangMills.BalabanClayBranchHeadReceiptSurface
