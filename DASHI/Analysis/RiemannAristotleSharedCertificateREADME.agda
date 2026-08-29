module DASHI.Analysis.RiemannAristotleSharedCertificateREADME where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Import-only aggregation/navigation root for the post-#622 Aristotle return.
--
-- The earlier shared-window endpoint cutset is now closed in Lean.  The current
-- returned state includes the inhabited exact two-zero / three-taper theorem and
-- the corrected far-tail-only residual frontier.
------------------------------------------------------------------------

import DASHI.Analysis.RiemannAristotleSharedWindowCertificateExact
import DASHI.Analysis.CertifiedFiniteCarrierReindexExact
import DASHI.Analysis.RiemannAristotleSharedCertificateReturnExact
import DASHI.Analysis.RiemannAristotleSharedCertificateReturnRegression
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnRegression
import DASHI.Analysis.ExactSelectedEliminationFarTailCompilerExact
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact
import DASHI.Analysis.RiemannAristotleCurrentFrontierRegression
