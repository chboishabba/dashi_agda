module DASHI.Physics.YangMills.BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Martin Lüscher and Peter Weisz,
-- "Efficient Numerical Techniques for Perturbative Lattice Gauge Theory
-- Computations", Nuclear Physics B 266 (1986), 309--354.
-- DOI: 10.1016/0550-3213(86)90094-5.
--
-- Stefano Capitani,
-- "Lattice Perturbation Theory", Physics Reports 382 (2003), 113--302.
-- DOI: 10.1016/S0370-1573(03)00211-4. arXiv:hep-lat/0211036.
--
-- CARRIER WARNING
--
-- The side-four torus used by the finite physical Faddeev--Popov module and
-- the generated 4^4 Brillouin *box partition* used by the one-loop interval
-- proof are not identified.  Equal cardinality would be a false bridge.
--
-- The safe bridge is local/symbolic.  The flat nearest-neighbour FP stencil
-- already proved on the finite carrier is
--
--     (2 omega(x) - omega(x+mu) - omega(x-mu))_mu.
--
-- Its Fourier symbol is 2 - 2 cos(k_mu).  The Wilson denominator uses
-- 4 sin^2(k_mu/2).  This module strengthens the existing physical trig-box
-- carrier with the SAME-momentum half-angle identity and proves that the sum
-- of the ghost symbols is exactly the already-used Wilson hat{k}^2 value.
--
-- Thus the remaining B1 source theorem is not "guess the ghost denominator":
-- it is the source-specific Fourier identification of the literal infinite-
-- lattice/background FP operator with this coherent symbol, followed by the
-- gauge-zero-mode reduction and determinant/log-det expansion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import Real as Bishop

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4LiteralWilsonHatMomentumBishopIdentificationExact as Hat
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FiniteFP

record CoherentGhostTrigBoxData : Set₁ where
  field
    trig : Canonical.PhysicalTrigBoxData

    -- Standard half-angle identity on the SAME physical momentum value.
    -- This coherence was not previously present in PhysicalTrigBoxData, whose
    -- sine-half and cosine-full leaves could otherwise be supplied independently.
    halfAngleExact : ∀ role axis →
      Canonical.twoValue Bishop.-
        (Canonical.twoValue Bishop.*
          Canonical.cosineFullValue trig role axis)
      ≡ Canonical.scaledSineSquareValue trig role axis
open CoherentGhostTrigBoxData public

ghostAxisSymbol :
  CoherentGhostTrigBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
ghostAxisSymbol dataSet role axis =
  Canonical.twoValue Bishop.-
    (Canonical.twoValue Bishop.*
      Canonical.cosineFullValue (trig dataSet) role axis)

freeGhostSymbol :
  CoherentGhostTrigBoxData → Eval.MomentumRole → Bishop.ℝ
freeGhostSymbol dataSet role =
  ghostAxisSymbol dataSet role Eval.axis0 Bishop.+
  ghostAxisSymbol dataSet role Eval.axis1 Bishop.+
  ghostAxisSymbol dataSet role Eval.axis2 Bishop.+
  ghostAxisSymbol dataSet role Eval.axis3

ghostAxisSymbolIsWilsonSineSquare : ∀ dataSet role axis →
  ghostAxisSymbol dataSet role axis
  ≡ Canonical.scaledSineSquareValue (trig dataSet) role axis
ghostAxisSymbolIsWilsonSineSquare dataSet role axis =
  halfAngleExact dataSet role axis

freeGhostSymbolIsWilsonHatMomentum : ∀ dataSet role →
  freeGhostSymbol dataSet role
  ≡ Hat.literalWilsonHatMomentum (trig dataSet) role
freeGhostSymbolIsWilsonHatMomentum dataSet role
  rewrite ghostAxisSymbolIsWilsonSineSquare dataSet role Eval.axis0
        | ghostAxisSymbolIsWilsonSineSquare dataSet role Eval.axis1
        | ghostAxisSymbolIsWilsonSineSquare dataSet role Eval.axis2
        | ghostAxisSymbolIsWilsonSineSquare dataSet role Eval.axis3 = refl

freeGhostSymbolIsCanonicalHatMomentumAtom : ∀ dataSet role →
  freeGhostSymbol dataSet role
  ≡ Canonical.canonicalAtomValue (trig dataSet)
      (Eval.hatMomentumSquared role)
freeGhostSymbolIsCanonicalHatMomentumAtom dataSet role =
  let
    toLiteral = freeGhostSymbolIsWilsonHatMomentum dataSet role
    atomExact = Hat.hatMomentumAtomValueIsLiteralWilson (trig dataSet) role
  in
  Relation.Binary.PropositionalEquality.trans toLiteral
    (Relation.Binary.PropositionalEquality.sym atomExact)

------------------------------------------------------------------------
-- Proof/source boundary.
------------------------------------------------------------------------

-- Exact once the coherent trig values are on the carrier.
freeGhostWilsonHatSymbolBridgeLevel : ProofLevel
freeGhostWilsonHatSymbolBridgeLevel = machineChecked

-- Standard Fourier fact for the nearest-neighbour stencil; source-specific
-- work must still instantiate it on the literal Bałaban/Wilson ghost carrier.
nearestNeighbourStencilFourierSymbolLevel : ProofLevel
nearestNeighbourStencilFourierSymbolLevel = standardImported

-- Existing finite P33 theorem supplies a literal source witness for the local
-- stencil, but does not by itself identify the infinite-lattice one-loop
-- determinant with the Brillouin-box evaluator.
finiteP33FaddeevPopovStencilLevel : ProofLevel
finiteP33FaddeevPopovStencilLevel = FiniteFP.physicalFaddeevPopovOperatorLevel

literalOneLoopFaddeevPopovFourierIdentificationLevel : ProofLevel
literalOneLoopFaddeevPopovFourierIdentificationLevel = conditional

-- The actual physical trig producer should now establish one coherent record,
-- not unrelated sine-half and cosine-full receipts.
coherentPhysicalTrigBoxProducerLevel : ProofLevel
coherentPhysicalTrigBoxProducerLevel = conditional
