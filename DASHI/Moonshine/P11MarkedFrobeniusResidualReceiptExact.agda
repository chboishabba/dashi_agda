module DASHI.Moonshine.P11MarkedFrobeniusResidualReceiptExact where

-- Betina & Lecouturier, "Congruence formulae for Legendre modular
-- polynomials", JNT 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.

open import DASHI.Core.Prelude

import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.ProvenanceFibreDynamicsReceiptExact as ReceiptDynamics
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11Fine5PNFProvenanceQuotientBridgeExact as PNFQuotient
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as Marked

fine5PNFCore =
  Sectioned.sectionedProjectionCore PNFQuotient.fine5SectionedProjection

markedFrobeniusEndomorphism : Dynamics.FibreEndomorphism fine5PNFCore
markedFrobeniusEndomorphism =
  Dynamics.fibreEndomorphism
    Marked.markedFrobenius
    Marked.markedFrobeniusPreservesJClass

markedFrobeniusMovesA0 : Marked.markedFrobenius Fine.a0 ≡ Fine.a0 → ⊥
markedFrobeniusMovesA0 ()

markedFrobeniusA0HiddenTransition :
  Dynamics.HiddenTransition fine5PNFCore Marked.markedFrobenius Fine.a0
markedFrobeniusA0HiddenTransition =
  Dynamics.fibreEndomorphismHiddenWhenNontrivial
    markedFrobeniusEndomorphism Fine.a0 markedFrobeniusMovesA0

markedFrobeniusMustChangeFine5Residual :
  PNFQuotient.fine5Residual (Marked.markedFrobenius Fine.a0)
    ≡ PNFQuotient.fine5Residual Fine.a0 → ⊥
markedFrobeniusMustChangeFine5Residual =
  ReceiptDynamics.hiddenTransitionChangesReceipt
    PNFQuotient.fine5PNFProvenanceQuotient
    markedFrobeniusA0HiddenTransition

markedFrobeniusResidualChangeComputes :
  PNFQuotient.r1 ≡ PNFQuotient.r0 → ⊥
markedFrobeniusResidualChangeComputes ()
