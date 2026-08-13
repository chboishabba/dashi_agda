module DASHI.Physics.YangMills.BalabanCMP109Federbush011Equation38PhysicalFirstOrderExact where

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
-- This is the source-shortest G1 route.  Bałaban CMP98 equation (38) supplies
-- a quadratic principal-log remainder on the regular chart.  We identify the
-- magnitude of that SAME remainder with the literal sourceRemainder in the
-- already-owned equation-(0.11) Federbush error equation, then use the existing
-- one-quarter reopening:
--
--   ||r_source|| <= 24 ||dU||^2,
--   24 ||dU|| <= epsilon
--       => ||r_source|| <= epsilon ||dU||
--       => ||e|| <= (4/3 epsilon) ||dU||.
--
-- No generic implicit-function theorem and no independently selectable
-- derivative/remainder object appears in this chain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact as Frechet
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

record Equation38FederbushSourceData
    (Index : Set)
    (equation : Frechet.FederbushFrechetErrorEquation Index)
    (inputMagnitude sourceMagnitude : ℚ) : Set₁ where
  field
    sourceQuadratic :
      Eq38.Equation38QuadraticRemainder inputMagnitude sourceMagnitude
    sourceMagnitudeIsLiteral :
      sourceMagnitude
      ≡ L1.vectorL1
          (Frechet.coordinates equation)
          (Frechet.sourceRemainder equation)

open Equation38FederbushSourceData public

equation38FederbushLiteralSourceLittleO :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude sourceMagnitude epsilon →
  Equation38FederbushSourceData Index equation inputMagnitude sourceMagnitude →
  Eq38.sourceQuadraticConstant * inputMagnitude ≤ epsilon →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.sourceRemainder equation)
    ≤ epsilon * inputMagnitude
equation38FederbushLiteralSourceLittleO
    equation inputMagnitude sourceMagnitude epsilon data small =
  subst
    (λ magnitude → magnitude ≤ epsilon * inputMagnitude)
    (sourceMagnitudeIsLiteral data)
    (Eq38.equation38RemainderLittleOEpsilon
      inputMagnitude sourceMagnitude epsilon (sourceQuadratic data) small)

equation38FederbushPhysicalErrorLittleO :
  ∀ {Index} (equation : Frechet.FederbushFrechetErrorEquation Index)
    inputMagnitude sourceMagnitude epsilon →
  Equation38FederbushSourceData Index equation inputMagnitude sourceMagnitude →
  Eq38.sourceQuadraticConstant * inputMagnitude ≤ epsilon →
  L1.vectorL1
      (Frechet.coordinates equation)
      (Frechet.error equation)
    ≤ (Quarter.fourThirds * epsilon) * inputMagnitude
equation38FederbushPhysicalErrorLittleO
    equation inputMagnitude sourceMagnitude epsilon data small =
  Frechet.federbushFrechetLittleOTransfer equation epsilon inputMagnitude
    (equation38FederbushLiteralSourceLittleO
      equation inputMagnitude sourceMagnitude epsilon data small)

cmp109Federbush011Equation38SourceLittleOLevel : ProofLevel
cmp109Federbush011Equation38SourceLittleOLevel = machineChecked

cmp109Federbush011Equation38PhysicalErrorLevel : ProofLevel
cmp109Federbush011Equation38PhysicalErrorLevel = machineChecked
