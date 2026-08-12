module DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Paul Federbush,
-- "A Phase Cell Approach to Yang-Mills Theory. IV. The Choice of Variables",
-- Communications in Mathematical Physics 87 (1982), 529--545.
-- DOI: 10.1007/BF01208273.
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
-- DASHI CONTRIBUTION
--
-- Reuse the literal one-quarter reopening theorem to prove the exact error
-- estimate needed for differentiability of the Federbush average, rather than
-- introducing a generic implicit-function theorem.
--
-- After inserting the already-owned linear response
--
--   v = Abar^{-1} b(delta U)
--
-- into the exact perturbed equation, the nonlinear error e has the same
-- identity-plus-residual shape already used by the normal solver:
--
--   e + R(e) = r(delta U,v,e),
--   ||R(e)||_1 <= (1/4)||e||_1.
--
-- Hence the SAME reopening proof gives
--
--   ||e||_1 <= (4/3)||r||_1.
--
-- A little-o bound on the source remainder therefore transfers immediately to
-- e, preserving the literal J_j, T_j, Abar and b objects of equation (0.11).
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record FederbushFrechetErrorEquation (Index : Set) : Set₁ where
  field
    coordinates : List Index
    nonlinearResidual : Reopen.Vector Index → Reopen.Vector Index
    error : Reopen.Vector Index
    sourceRemainder : Reopen.Vector Index

    exactErrorEquation :
      Reopen.IdentityPlusResidualEquation
        nonlinearResidual error sourceRemainder

    quarterErrorRemainder :
      L1.vectorL1 coordinates (nonlinearResidual error)
      ≤ Quarter.oneQuarter * L1.vectorL1 coordinates error

open FederbushFrechetErrorEquation public

federbushFrechetErrorFourThirdsBound :
  ∀ {Index} (equation : FederbushFrechetErrorEquation Index) →
  L1.vectorL1 (coordinates equation) (error equation)
  ≤ Quarter.fourThirds
      * L1.vectorL1 (coordinates equation) (sourceRemainder equation)
federbushFrechetErrorFourThirdsBound equation =
  Quarter.oneQuarterReopeningBound
    (coordinates equation)
    (nonlinearResidual equation)
    (error equation)
    (sourceRemainder equation)
    (exactErrorEquation equation)
    (quarterErrorRemainder equation)

federbushFrechetLittleOTransfer :
  ∀ {Index} (equation : FederbushFrechetErrorEquation Index)
    epsilon inputMagnitude →
  L1.vectorL1 (coordinates equation) (sourceRemainder equation)
    ≤ epsilon * inputMagnitude →
  L1.vectorL1 (coordinates equation) (error equation)
    ≤ (Quarter.fourThirds * epsilon) * inputMagnitude
federbushFrechetLittleOTransfer equation epsilon inputMagnitude sourceUpper =
  let
    reopeningUpper = federbushFrechetErrorFourThirdsBound equation
    scaled = Norm.scaleNonnegative Quarter.fourThirds
      (ℚP.nonNegative⁻¹ Quarter.fourThirds) sourceUpper
  in
  ℚP.≤-trans reopeningUpper scaled

cmp109FederbushFrechetSameReopeningLevel : ProofLevel
cmp109FederbushFrechetSameReopeningLevel = machineChecked

cmp109FederbushFrechetLittleOTransferLevel : ProofLevel
cmp109FederbushFrechetLittleOTransferLevel = machineChecked
