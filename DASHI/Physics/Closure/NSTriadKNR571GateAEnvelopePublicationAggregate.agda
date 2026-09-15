module DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopePublicationAggregate where

-- Focused post-PR #920 check surface.
--
-- Existing publication spine:
--   R571 -> opposite shifts -> paired second order -> scoped second moment.
--
-- This tranche adds only the physical-envelope crosswalk boundary:
--   A1 reverse-triangle/radius donor,
--   G2 finite path/gradient donor,
--   G1 modal-energy donor,
--   preferred radial linearization with R+ = 0,
--   isolated A2 centered radial-curvature leaf.
--
-- No inner-fibre, R568 or Clay promotion is introduced here.

import DASHI.Physics.Closure.NSTriadKNR571PairedSecondMomentPublicationAggregate
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkRegression
