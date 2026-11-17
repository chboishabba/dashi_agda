module DASHI.Physics.Motors.SmithFilsingerSpatialSourceBoundaryWeldExact where

-- Dependent field-to-spatial-chain bridge, reusing the original-source
-- and original-geometry owner rather than identifying a synthetic LC chain
-- with Filsinger's apparatus by matching a name or phase readout.
--
-- Source-first all-N theorem imported; physical field mapping is an
-- explicit independent obligation. No Maxwell PDE/solar source solved.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact as Spatial
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- This is indexed by the selected original source configuration, already
-- rigorously distinguished as Smith compiled, Filsinger filmed Earth,
-- or the Filsinger portable proposal.
--
-- The two physical boundary identifications are NOT inferred from
-- symbolic E/B fields; they require calibrated work across the same
-- boundaries, with controller ports, stored states and return geometry.
record SpatialToOriginalSourcePort
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b) : Set₂ where
  field
    entry exit : Nat
    cells : Spatial.SpatialChain entry exit

    spatialInputIsSameOriginalPort :
      entry + (Spatial.sumDrive cells + Spatial.sumInitialStorage cells)
      ≡ (Port.MidpointTwoPortWorkWindow.naturalIncident
          (Weld.FormalFieldToPort.portWindow f)
       + Port.MidpointTwoPortWorkWindow.controllerIncident
          (Weld.FormalFieldToPort.portWindow f))
       + Port.MidpointTwoPortWorkWindow.initialStored
          (Weld.FormalFieldToPort.portWindow f)

    spatialOutputIsSameOriginalPort :
      exit + (Spatial.sumUsefulLoad cells
        + (Spatial.sumDissipation cells + Spatial.sumFinalStorage cells))
      ≡ (Port.MidpointTwoPortWorkWindow.naturalOutgoing
          (Weld.FormalFieldToPort.portWindow f)
       + Port.MidpointTwoPortWorkWindow.controllerOutgoing
          (Weld.FormalFieldToPort.portWindow f))
       + (Port.MidpointTwoPortWorkWindow.usefulWork
          (Weld.FormalFieldToPort.portWindow f)
       + (Port.MidpointTwoPortWorkWindow.internalLoss
          (Weld.FormalFieldToPort.portWindow f)
       + Port.MidpointTwoPortWorkWindow.finalStored
          (Weld.FormalFieldToPort.portWindow f)))

    -- A single physical source/readback already belongs to f.
    -- No second unlicensed natural-source input is introduced.

-- Derived original-port conservation, not a new independently asserted
-- whole-system energy balance. This is the actual weld: selected
-- source-indexed physical port mapping + all-N local energy laws.
spatialEnergyClosesSelectedPort :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (w : SpatialToOriginalSourcePort b f) →
  (Port.MidpointTwoPortWorkWindow.naturalIncident
      (Weld.FormalFieldToPort.portWindow f)
   + Port.MidpointTwoPortWorkWindow.controllerIncident
      (Weld.FormalFieldToPort.portWindow f))
   + Port.MidpointTwoPortWorkWindow.initialStored
      (Weld.FormalFieldToPort.portWindow f)
  ≡ (Port.MidpointTwoPortWorkWindow.naturalOutgoing
      (Weld.FormalFieldToPort.portWindow f)
   + Port.MidpointTwoPortWorkWindow.controllerOutgoing
      (Weld.FormalFieldToPort.portWindow f))
   + (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f)
   + (Port.MidpointTwoPortWorkWindow.internalLoss
      (Weld.FormalFieldToPort.portWindow f)
   + Port.MidpointTwoPortWorkWindow.finalStored
      (Weld.FormalFieldToPort.portWindow f)))
spatialEnergyClosesSelectedPort b f w =
  trans (sym (SpatialToOriginalSourcePort.spatialInputIsSameOriginalPort w))
    (trans (Spatial.spatialChainWorkBalance
             (SpatialToOriginalSourcePort.cells w))
      (SpatialToOriginalSourcePort.spatialOutputIsSameOriginalPort w))
