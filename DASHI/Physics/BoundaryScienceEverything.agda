module DASHI.Physics.BoundaryScienceEverything where

-- Reusable scientific cores extracted from the missing/deceased/open-science
-- investigation.  These are domain owners; person-specific fixtures should
-- refine/import them rather than own the underlying science.

import DASHI.Core.ScientificMechanismEvidenceBidiExact
import DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact
import DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact
import DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact
import DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact
import DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact
import DASHI.Physics.POAMSScientificMechanismBoundaryExact

-- Case-specific adapters currently available on this continuation branch.
import DASHI.Physics.RezaBurnResistantAlloyScienceExact
import DASHI.Physics.LeBlancFissionInstrumentationControlScienceExact
import DASHI.Physics.Plasma.LoureiroViriatoNumericsScienceExact
import DASHI.Physics.ScorpiusRadiographicAcceleratorScienceExact
import DASHI.Physics.MaiwaldActionSpectroscopyScienceExact

-- Explicit dependency-direction bridges: generic domain science first,
-- bounded source/case refinements second.
import DASHI.Physics.BoundaryScienceGeneralisationBridgesExact
