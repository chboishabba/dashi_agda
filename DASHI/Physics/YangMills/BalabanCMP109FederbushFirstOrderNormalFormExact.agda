module DASHI.Physics.YangMills.BalabanCMP109FederbushFirstOrderNormalFormExact where

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
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Package equation (0.11) in the exact nonlinear form consumed by equation
-- (0.12).  The linear response is not an anonymous derivative: it is the
-- already-selected Abar^{-1} b response.  The remainder is literally the same
-- error vector appearing in the reopened Federbush equation.
--
-- Thus one object owns
--
--   M(U+dU) = M(U) + Abar^{-1} b_U(dU) + r_M(dU)
--
-- together with the same-reopening estimate
--
--   ||r_M||_1 <= (4/3) ||sourceRemainder||_1.
--
-- Consequently any little-o estimate proved for the literal substituted
-- equation transfers directly to the nonlinear averaging remainder without a
-- generic implicit-function theorem and without losing J_j/T_j/Abar/b
-- provenance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanCMP109FederbushFrechetReopeningExact as Frechet

record FederbushFirstOrderNormalFormData (Index : Set) : Set₁ where
  field
    baseAverage : Reopen.Vector Index
    perturbedAverage : Reopen.Vector Index

    -- This field is intended to be instantiated by the literal solution of
    -- Abar v = b assembled from the equation-(0.11) J_j/T_j components.
    inverseAbarSourceResponse : Reopen.Vector Index

    frechetErrorEquation : Frechet.FederbushFrechetErrorEquation Index

    -- Exact same-object decomposition of the selected average.  The nonlinear
    -- remainder here is definitionally the `error` of the reopening equation,
    -- so a caller cannot prove differentiability with one remainder and use a
    -- different remainder in the printed map.
    perturbedAverageExact : ∀ row →
      perturbedAverage row
      ≡ baseAverage row
        + inverseAbarSourceResponse row
        + Frechet.error frechetErrorEquation row

open FederbushFirstOrderNormalFormData public

federbushFirstOrderNormalFormExact :
  ∀ {Index} (data : FederbushFirstOrderNormalFormData Index) row →
  perturbedAverage data row
  ≡ baseAverage data row
    + inverseAbarSourceResponse data row
    + Frechet.error (frechetErrorEquation data) row
federbushFirstOrderNormalFormExact data row =
  perturbedAverageExact data row

federbushFirstOrderRemainderFourThirds :
  ∀ {Index} (data : FederbushFirstOrderNormalFormData Index) →
  L1.vectorL1
      (Frechet.coordinates (frechetErrorEquation data))
      (Frechet.error (frechetErrorEquation data))
  ≤ Quarter.fourThirds
      * L1.vectorL1
          (Frechet.coordinates (frechetErrorEquation data))
          (Frechet.sourceRemainder (frechetErrorEquation data))
federbushFirstOrderRemainderFourThirds data =
  Frechet.federbushFrechetErrorFourThirdsBound
    (frechetErrorEquation data)

-- Epsilon-form little-o transfer.  The same inputMagnitude is deliberately
-- left abstract so the physical equation-(0.11) instantiation can use the
-- literal selected perturbation norm rather than a replacement norm.
federbushFirstOrderRemainderLittleOTransfer :
  ∀ {Index} (data : FederbushFirstOrderNormalFormData Index)
    epsilon inputMagnitude →
  L1.vectorL1
      (Frechet.coordinates (frechetErrorEquation data))
      (Frechet.sourceRemainder (frechetErrorEquation data))
    ≤ epsilon * inputMagnitude →
  L1.vectorL1
      (Frechet.coordinates (frechetErrorEquation data))
      (Frechet.error (frechetErrorEquation data))
    ≤ (Quarter.fourThirds * epsilon) * inputMagnitude
federbushFirstOrderRemainderLittleOTransfer data =
  Frechet.federbushFrechetLittleOTransfer (frechetErrorEquation data)

cmp109FederbushFirstOrderNormalFormLevel : ProofLevel
cmp109FederbushFirstOrderNormalFormLevel = machineChecked

cmp109FederbushSameRemainderAuthorityLevel : ProofLevel
cmp109FederbushSameRemainderAuthorityLevel = machineChecked
