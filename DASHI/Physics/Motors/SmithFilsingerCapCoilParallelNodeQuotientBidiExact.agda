module DASHI.Physics.Motors.SmithFilsingerCapCoilParallelNodeQuotientBidiExact where

-- Original source language owned by Filsinger's earlier user-supplied
-- midpoint/coil/capacitor transcript. Four diode packages are said to
-- come as two from a capacitor and two from "here"/the coil, "all
-- forward-facing" with positives ganged and return to "midpoint,
-- earth, ground". The source ALSO calls the capacitor "across" the coil.
--
-- Source-first inverse distinction: "two devices" is NOT "two electrically
-- independent ports". IF the capacitor is truly across a selected coil,
-- its two terminal nodes are exactly the coil's two terminal nodes.
-- This is a finite quotient of terminal labels, not a verified photo
-- readback. The rest of the open system, source power and Maxwell
-- boundary are governed by the existing original-work owners.
--
-- Algebraic physical companion:
-- scripts/check_filsinger_parallel_lc_node_bidi_sympy_20261122.py
-- The local SymPy result is NOT Agda kernel acceptance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact as Source
import DASHI.Physics.Motors.SmithFilsingerMidpointReturnClampBacksolveExact as Earlier

data PhysicalTerminal : Set where
  capacitorFirst capacitorSecond : PhysicalTerminal
  coilFirst coilSecond : PhysicalTerminal

data ElectricalNode : Set where
  firstNode secondNode positiveBus midpointReturn : ElectricalNode

-- This case represents a capacitor physically ACROSS the selected coil.
-- It must not be interpreted as source-admitted original continuity.
parallelNode : PhysicalTerminal → ElectricalNode
parallelNode capacitorFirst = firstNode
parallelNode capacitorSecond = secondNode
parallelNode coilFirst = firstNode
parallelNode coilSecond = secondNode

capFirstEqualsCoilFirst :
  parallelNode capacitorFirst ≡ parallelNode coilFirst
capFirstEqualsCoilFirst = refl

capSecondEqualsCoilSecond :
  parallelNode capacitorSecond ≡ parallelNode coilSecond
capSecondEqualsCoilSecond = refl

-- The two components' *terminal labels* remain different despite
-- equality in the electrical-node quotient.
capFirstAndCoilFirstAreDifferentLabels :
  capacitorFirst ≡ coilFirst → ⊥
capFirstAndCoilFirstAreDifferentLabels ()

capSecondAndCoilSecondAreDifferentLabels :
  capacitorSecond ≡ coilSecond → ⊥
capSecondAndCoilSecondAreDifferentLabels ()

-- Strong finite BIDI obstruction: observing an electrical node U alone
-- cannot recover which component terminal the narrated diode was "off".
noUniqueComponentTerminalFromObservedNode :
  (reverse : ElectricalNode → PhysicalTerminal) →
  ((p : PhysicalTerminal) → reverse (parallelNode p) ≡ p) → ⊥
noUniqueComponentTerminalFromObservedNode reverse agrees =
  capFirstAndCoilFirstAreDifferentLabels
    (trans (sym (agrees capacitorFirst)) (agrees coilFirst))

-- The identity of the input *electrical nodes* depends on which end of
-- each component physically supplies its diode packages.
data DiodePackage : Set where
  diodeCapOne diodeCapTwo diodeCoilOne diodeCoilTwo : DiodePackage

data PhysicalSourceSide : Set where
  fromCapacitor fromCoil : PhysicalSourceSide

sourceSide : DiodePackage → PhysicalSourceSide
sourceSide diodeCapOne = fromCapacitor
sourceSide diodeCapTwo = fromCapacitor
sourceSide diodeCoilOne = fromCoil
sourceSide diodeCoilTwo = fromCoil

-- Two equally source-compatible circuit interpretations:
-- opposite terminals: capacitor group from first node, coil from second;
-- same terminals: both groups from first node.
data DiodeLandingCase : Set where
  fromOppositeParallelEnds fromSameParallelEnd : DiodeLandingCase

physicalInputTerminal : DiodeLandingCase → DiodePackage → PhysicalTerminal
physicalInputTerminal fromOppositeParallelEnds diodeCapOne = capacitorFirst
physicalInputTerminal fromOppositeParallelEnds diodeCapTwo = capacitorFirst
physicalInputTerminal fromOppositeParallelEnds diodeCoilOne = coilSecond
physicalInputTerminal fromOppositeParallelEnds diodeCoilTwo = coilSecond
physicalInputTerminal fromSameParallelEnd diodeCapOne = capacitorFirst
physicalInputTerminal fromSameParallelEnd diodeCapTwo = capacitorFirst
physicalInputTerminal fromSameParallelEnd diodeCoilOne = coilFirst
physicalInputTerminal fromSameParallelEnd diodeCoilTwo = coilFirst

electricalInput : DiodeLandingCase → DiodePackage → ElectricalNode
electricalInput l d = parallelNode (physicalInputTerminal l d)

oppositeCaseHasTwoInputs :
  electricalInput fromOppositeParallelEnds diodeCapOne
    ≡ firstNode
oppositeCaseHasTwoInputs = refl

oppositeCaseHasOtherInput :
  electricalInput fromOppositeParallelEnds diodeCoilOne
    ≡ secondNode
oppositeCaseHasOtherInput = refl

sameCaseCollapsesInputs :
  electricalInput fromSameParallelEnd diodeCapOne
    ≡ electricalInput fromSameParallelEnd diodeCoilOne
sameCaseCollapsesInputs = refl

oppositeCaseSeparatesInputs :
  electricalInput fromOppositeParallelEnds diodeCapOne
    ≡ electricalInput fromOppositeParallelEnds diodeCoilOne → ⊥
oppositeCaseSeparatesInputs ()

-- Positive diode-OR is only one candidate. For this candidate, all
-- packages point to the SAME positive bus and do not establish a bridge
-- negative bus. The return remains a separate physical circuit question.
candidateForwardCathode : DiodePackage → ElectricalNode
candidateForwardCathode d = positiveBus

candidateAllPositiveBus :
  (d : DiodePackage) → candidateForwardCathode d ≡ positiveBus
candidateAllPositiveBus d = refl

midpointIsNotPositiveBus :
  midpointReturn ≡ positiveBus → ⊥
midpointIsNotPositiveBus ()

-- The previous four-package count already belongs to the literal
-- source inventory, but cannot determine input node grouping.
sourceSaysFourDiodes :
  Source.numberMagnitude Source.midpointFourDiodes ≡ 4
sourceSaysFourDiodes = refl

noUniqueLandingCaseFromFourPackages :
  (infer : Nat → DiodeLandingCase) →
  ((c : DiodeLandingCase) → infer 4 ≡ c) → ⊥
noUniqueLandingCaseFromFourPackages infer agrees =
  differentCases (trans (sym (agrees fromOppositeParallelEnds))
                         (agrees fromSameParallelEnd))
  where
    differentCases :
      fromOppositeParallelEnds ≡ fromSameParallelEnd → ⊥
    differentCases ()

-- A capacitor electrically PARALLEL to a coil has admittance
-- Y=G+i*(omega*C-1/(omega*L)), NOT the earlier series-LC impedance
-- Z=Rs+i*(omega*L-1/(omega*C)). The latter belongs to a DIFFERENT
-- candidate circuit. Both obey signed energy conservation; neither
-- establishes a natural work port from the names "coil"/"capacitor".
-- Analytical source/work proofs are kept in SymPy and existing original
-- SmithFilsingerOriginalMaxwellMeterIntervalWeldExact producers.
