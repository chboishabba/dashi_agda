module DASHI.Physics.YangMills.BalabanP0FourOriginalDiagramMixedTwoJetWeldExact where

-- SOURCE-PRESERVING FOUR-DIAGRAM WELD to the CMP109 *correct* beta extractor.
--
-- The selected SU2 Wilson bubble/tadpole, reduced FP ghost and Haar
-- off-diagonal second jets are NOT the second derivative of a scalar
-- function Π_scalar. The CMP109 consumer extracts beta from the NEGATIVE
-- mixed derivative of the full off-diagonal Π_mu,nu tensor component.
--
-- Every source jet below must come from the actual indexed physical
-- diagram, not an invented numerical 11/24 coefficient. This module
-- proves the complete four-term finite jet assembly and the exact
-- CMP109 extraction once the SAME-SOURCE tensor jet identity is paid.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as CMP

fourDiagramTwoJet :
  (bubble tadpole ghost haar : CMP.OffDiagonalTwoJet) →
  CMP.OffDiagonalTwoJet
fourDiagramTwoJet bubble tadpole ghost haar =
  CMP.addTwoJet bubble
    (CMP.addTwoJet tadpole (CMP.addTwoJet ghost haar))

fourDiagramMixedCoefficientExact :
  ∀ bubble tadpole ghost haar →
  CMP.mixedDerivativeCoefficient
    (fourDiagramTwoJet bubble tadpole ghost haar)
  ≡
    CMP.mixedDerivativeCoefficient bubble
    + (CMP.mixedDerivativeCoefficient tadpole
      + (CMP.mixedDerivativeCoefficient ghost
        + CMP.mixedDerivativeCoefficient haar))
fourDiagramMixedCoefficientExact bubble tadpole ghost haar = refl

-- The ORIGINAL mixed tensor jet, not a freely selected scalar.
record OriginalFourPhysicalTwoJetReceipt : Set where
  field
    gaugeBubbleOffDiagonalTwoJet : CMP.OffDiagonalTwoJet
    gaugeTadpoleOffDiagonalTwoJet : CMP.OffDiagonalTwoJet
    ghostOffDiagonalTwoJet : CMP.OffDiagonalTwoJet
    haarOffDiagonalTwoJet : CMP.OffDiagonalTwoJet

    -- Physically identify the exact sum with the genuine CMP109
    -- transverse projection and third-order remainder.  Merely
    -- knowing the universal color factor does not construct this.
    balabanSource : CMP.CMP109OffDiagonalSecondJetData
    fourJetIsOriginalSourceJet :
      fourDiagramTwoJet
        gaugeBubbleOffDiagonalTwoJet
        gaugeTadpoleOffDiagonalTwoJet
        ghostOffDiagonalTwoJet
        haarOffDiagonalTwoJet
      ≡ CMP.fullOffDiagonalTwoJet balabanSource

open OriginalFourPhysicalTwoJetReceipt public

sourceFourJets : OriginalFourPhysicalTwoJetReceipt → CMP.OffDiagonalTwoJet
sourceFourJets src = fourDiagramTwoJet
  (gaugeBubbleOffDiagonalTwoJet src)
  (gaugeTadpoleOffDiagonalTwoJet src)
  (ghostOffDiagonalTwoJet src)
  (haarOffDiagonalTwoJet src)

sourceFourJetsMixedCoefficientExact :
  ∀ src →
  CMP.mixedDerivativeCoefficient (sourceFourJets src)
  ≡
    CMP.mixedDerivativeCoefficient (gaugeBubbleOffDiagonalTwoJet src)
    + (CMP.mixedDerivativeCoefficient (gaugeTadpoleOffDiagonalTwoJet src)
      + (CMP.mixedDerivativeCoefficient (ghostOffDiagonalTwoJet src)
        + CMP.mixedDerivativeCoefficient (haarOffDiagonalTwoJet src)))
sourceFourJetsMixedCoefficientExact src =
  fourDiagramMixedCoefficientExact
    (gaugeBubbleOffDiagonalTwoJet src)
    (gaugeTadpoleOffDiagonalTwoJet src)
    (ghostOffDiagonalTwoJet src)
    (haarOffDiagonalTwoJet src)

-- This is the actual four physical diagram-to-CMP109 consumer.
-- It reduces the beta matching to the exact SAME-SOURCE
-- fourJetIsOriginalSourceJet proof; no second generic coefficient.
fourOriginalDiagramJetsExtractBeta :
  (src : OriginalFourPhysicalTwoJetReceipt) →
  (- CMP.mixedDerivativeCoefficient (sourceFourJets src))
    ≡ CMP.beta (balabanSource src)
fourOriginalDiagramJetsExtractBeta src =
  trans
    (cong (λ jet → - CMP.mixedDerivativeCoefficient jet)
      (fourJetIsOriginalSourceJet src))
    (CMP.cmp109MixedDerivativeExtractsBeta (balabanSource src))

-- The assertion that beta is the mixed derivative of Π_scalar is FALSE
-- already for a CONSTANT scalar beta: that scalar has zero derivative,
-- while the transverse off-diagonal tensor has coefficient -beta.
-- The theorem above uses the already-verified correct tensor producer.
