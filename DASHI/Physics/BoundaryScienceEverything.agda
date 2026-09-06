module DASHI.Physics.BoundaryScienceEverything where

-- Reusable scientific cores extracted from the missing/deceased/open-science
-- investigation.  These are domain owners; person-specific fixtures should
-- refine/import them rather than own the underlying science.

import DASHI.Core.ScientificMechanismEvidenceBidiExact

-- Materials: nominal alloy chemistry -> process state -> microstructure -> properties.
import DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact
import DASHI.Physics.Materials.NickelBaseSuperalloyProcessStateDepthExact

-- Space fission instrumentation and controls: architecture -> harsh-environment
-- degradation -> qualification -> reliability/fault-tolerant autonomous control.
import DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact
import DASHI.Physics.Nuclear.FissionICQualificationReliabilityDepthExact

-- Reduced fluid-kinetic plasma computation: asymptotic model -> Hermite/numerical
-- representation -> closure/resolution -> physical validity.
import DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact
import DASHI.Physics.Plasma.ReducedKineticValidityClosureDepthExact

-- High-energy flash radiography: accelerator/source -> transmission imaging ->
-- calibrated forward model -> ill-posed inverse problem + uncertainty.
import DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact
import DASHI.Physics.Accelerators.FlashRadiographyForwardInverseUncertaintyExact

-- Cryogenic messenger-tag action spectroscopy: ion preparation -> tagging/action
-- response -> structural assignment, including explicit tag/conformer perturbation.
import DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact
import DASHI.Chemistry.Spectroscopy.CryogenicTagPerturbationAndAssignmentDepthExact

-- Source-proposed anomalous-force case retained with its own evidence boundary.
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
