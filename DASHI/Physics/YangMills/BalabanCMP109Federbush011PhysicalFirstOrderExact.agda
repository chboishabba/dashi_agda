module DASHI.Physics.YangMills.BalabanCMP109Federbush011PhysicalFirstOrderExact where

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
-- Close the quantitative bridge between the nonidentity principal-log
-- remainder and the literal equation-(0.11) reopening.  The source remainder
-- is not replaced by a fresh object: its l1 magnitude is identified with the
-- sourceRemainder field of the same FederbushFrechetErrorEquation that owns
-- the nonlinear error e.  Therefore
--
--   ||r_source|| <= epsilon ||dU||
--
-- feeds the existing exact 4/3 reopening and gives
--
--   ||e|| <= (4/3 epsilon) ||dU||.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact as Frechet
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityFirstOrderExact as Log

record Federbush011PhysicalSourceRemainderData
    (Index : Set)
    (equation : Frechet.FederbushFrechetErrorEquation Index)
    (inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude : ℚ)
    : Set₁ where
  field
    principalLogRemainder :
      Log.NonidentityPrincipalLogRemainderData
        inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude
    sourceMagnitudeIsLiteral :
      sourceMagnitude
      ≡ L1.vectorL1
          (Frechet.coordinates equation)
          (Frechet.sourceRemainder equation)

open Federbush011PhysicalSourceRemainderData public

federbush011LiteralSourceLittleO :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon →
  Federbush011PhysicalSourceRemainderData
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
    (λ literalMagnitude → literalMagnitude ≤ epsilon * inputMagnitude)
    (sourceMagnitudeIsLiteral data)
    (Log.principalLogNonidentityLittleOEpsilon
      inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
      (principalLogRemainder data) small)

federbush011PhysicalErrorLittleO :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon →
  Federbush011PhysicalSourceRemainderData
    Index equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude →
  lipschitzConstant * inputMagnitude ≤ epsilon →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.error equation)
    ≤ (Quarter.fourThirds * epsilon) * inputMagnitude
federbush011PhysicalErrorLittleO
    equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
    data small =
  Frechet.federbushFrechetLittleOTransfer equation epsilon inputMagnitude
    (federbush011LiteralSourceLittleO
      equation inputMagnitude lipschitzConstant jacobianVariation sourceMagnitude epsilon
      data small)

cmp109Federbush011LiteralSourceLittleOLevel : ProofLevel
cmp109Federbush011LiteralSourceLittleOLevel = machineChecked

cmp109Federbush011PhysicalFirstOrderLevel : ProofLevel
cmp109Federbush011PhysicalFirstOrderLevel = machineChecked
