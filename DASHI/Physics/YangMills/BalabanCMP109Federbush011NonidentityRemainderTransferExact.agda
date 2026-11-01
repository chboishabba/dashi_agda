module DASHI.Physics.YangMills.BalabanCMP109Federbush011NonidentityRemainderTransferExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Paul Federbush,
-- "A Phase Cell Approach to Yang-Mills Theory. IV. The Choice of Variables",
-- Communications in Mathematical Physics 114 (1988), 317--343.
-- DOI: 10.1007/BF01225039.
--
-- DASHI CONTRIBUTION
--
-- Feed the quantitative nonidentity principal-log source remainder into the
-- SAME equation-(0.11) Frechet reopening object.  The literal sourceRemainder
-- l1 magnitude is identified once; the existing 4/3 reopening then proves the
-- nonlinear averaging error is little-o with no new Abar/J_j/T_j selection.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact as Frechet
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityRemainderQuadraticExact as LogR

record Federbush011NonidentitySourceData
    (Index : Set)
    (equation : Frechet.FederbushFrechetErrorEquation Index)
    (inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude : ℚ)
    : Set₁ where
  field
    logMeanValueData :
      LogR.PrincipalLogMeanValueRemainderData
        inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude
    sourceMagnitudeIsLiteral :
      sourceMagnitude
      ≡ L1.vectorL1
          (Frechet.coordinates equation)
          (Frechet.sourceRemainder equation)

open Federbush011NonidentitySourceData public

federbush011LiteralSourceLittleO :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon →
  Federbush011NonidentitySourceData
    Index equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude →
  lipschitzConstant * inputMagnitude ≤ epsilon →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.sourceRemainder equation)
    ≤ epsilon * inputMagnitude
federbush011LiteralSourceLittleO
    equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
    data small =
  subst
    (λ magnitude → magnitude ≤ epsilon * inputMagnitude)
    (sourceMagnitudeIsLiteral data)
    (LogR.principalLogNonidentityRemainderLittleOEpsilon
      inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
      (logMeanValueData data) small)

federbush011NonidentityErrorLittleO :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon →
  Federbush011NonidentitySourceData
    Index equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude →
  lipschitzConstant * inputMagnitude ≤ epsilon →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.error equation)
    ≤ (Quarter.fourThirds * epsilon) * inputMagnitude
federbush011NonidentityErrorLittleO
    equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
    data small =
  Frechet.federbushFrechetLittleOTransfer equation epsilon inputMagnitude
    (federbush011LiteralSourceLittleO
      equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
      data small)

cmp109Federbush011NonidentitySourceTransferLevel : ProofLevel
cmp109Federbush011NonidentitySourceTransferLevel = machineChecked

cmp109Federbush011NonidentityErrorLittleOLevel : ProofLevel
cmp109Federbush011NonidentityErrorLittleOLevel = machineChecked
