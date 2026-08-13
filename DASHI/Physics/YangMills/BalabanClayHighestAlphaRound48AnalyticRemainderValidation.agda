module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound48AnalyticRemainderValidation where

------------------------------------------------------------------------
-- Focused Round-48 validation root.
--
-- No GitHub Actions workflow is added or modified.  This extends the merged
-- Round-47 source-producer root with Bałaban CMP98 equation-(38)'s explicit
-- quadratic principal-log remainder, the quantitative nonidentity remainder
-- estimates and same-object equation-(0.11) transfer, the canonical kernel-
-- curve o(t) estimate, and the certified owner-enclosure plaquette path.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound47PhysicalProducerValidation
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityRemainderQuadraticExact
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityQuantitativeProducerExact
import DASHI.Physics.YangMills.BalabanCMP109Federbush011NonidentityRemainderTransferExact
import DASHI.Physics.YangMills.BalabanCMP109SelectedKernelCurveLittleOExact
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCertifiedOwnerPlaquetteExact
