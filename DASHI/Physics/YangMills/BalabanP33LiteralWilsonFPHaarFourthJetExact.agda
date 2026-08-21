module DASHI.Physics.YangMills.BalabanP33LiteralWilsonFPHaarFourthJetExact where

------------------------------------------------------------------------
-- SAME-CARRIER WILSON / REDUCED-FP / HAAR SECOND AND FOURTH JETS
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10
-- (1974), 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- L. D. Faddeev and V. N. Popov, "Feynman Diagrams for the Yang--Mills
-- Field", Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", 2nd ed., Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- MATHEMATICAL CONTENT
--
-- At the common flat chart base, the gauge-fixed action is
-- S_W - log det(M_red) - log(J_Haar).  This module combines only coefficients
-- already produced from that SAME side-four rational carrier: the literal
-- Wilson fourth derivative, the explicit reduced-FP trace-log coefficient,
-- and the local SU(2) Haar fourth derivative.  In particular the ghost sign
-- and the 4! conversion from a g^4 trace-log coefficient to a fourth
-- derivative are visible here rather than being hidden in a later one-loop
-- box input.
--
-- The quadratic Haar and determinant coefficients are *not* silently folded
-- into the free fluctuation covariance: under U=exp(g q), they are order-g^2
-- interaction insertions.  The free contraction continues to use the literal
-- Wilson-plus-background-gauge Green operator.  Keeping this distinction is
-- necessary for the one-loop tadpole bookkeeping.
--
-- This is still a bare finite-volume action jet, not the contracted
-- vacuum-polarization mixed two-jet.  Propagator contraction, Fourier
-- transformation, and cutoff-uniform enclosure remain separate physical work.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Background
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteFourthJetExact as Wilson
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovPhysicalFourthJetExact as FP
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovTraceLogJetExact as TraceJet
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanLiteralSU2HaarFourthJetExact as Haar
import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact as Configured
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenExact as FreeGreen
import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact as GreenCoordinates
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)

------------------------------------------------------------------------
-- Exact coordinate identification between the existing P33 field and the
-- arbitrary-side physical field specialized at L=4.
------------------------------------------------------------------------

p33AsPhysicalField :
  P33.PhysicalSU2BondField4 → Physical.PhysicalSU2BondField Path4.side4
p33AsPhysicalField field Physical.coordinateX (pair axis site) =
  field P33.coordinateX (pair site axis)
p33AsPhysicalField field Physical.coordinateY (pair axis site) =
  field P33.coordinateY (pair site axis)
p33AsPhysicalField field Physical.coordinateZ (pair axis site) =
  field P33.coordinateZ (pair site axis)

-- The configured Green is expressed with the older component names; these
-- two pointwise maps make its domain exactly the P33 source-native tangent
-- field.  They are used below only for the free Wilson-plus-gauge covariance.
p33AsConfiguredTangent :
  P33.PhysicalSU2BondField4 → Configured.PhysicalSU2Tangent4
p33AsConfiguredTangent field Configured.component1 bond = field P33.coordinateX bond
p33AsConfiguredTangent field Configured.component2 bond = field P33.coordinateY bond
p33AsConfiguredTangent field Configured.component3 bond = field P33.coordinateZ bond

configuredAsP33Tangent :
  Configured.PhysicalSU2Tangent4 → P33.PhysicalSU2BondField4
configuredAsP33Tangent field P33.coordinateX bond = field Configured.component1 bond
configuredAsP33Tangent field P33.coordinateY bond = field Configured.component2 bond
configuredAsP33Tangent field P33.coordinateZ bond = field Configured.component3 bond

-- This is the literal side-four free fluctuation covariance.  The Haar and
-- reduced-FP terms below are insertions contracted against this Green; they do
-- not alter it at leading order in the right-trivialized g expansion.
literalFlatFluctuationGreen :
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4
literalFlatFluctuationGreen field =
  configuredAsP33Tangent
    (FreeGreen.configuredPhysicalGreen (p33AsConfiguredTangent field))

------------------------------------------------------------------------
-- First literal one-loop contraction: the local Haar quadratic insertion.
--
-- In exponential coordinates, -log J_Haar(g q) has quadratic Taylor
-- coefficient (g^2 / 3) sum_i q_i^2.  Contracting this insertion against
-- the fixed free Green matrix gives (1 / 3) Tr G.  The sum below is not an
-- abstract Gaussian interface: it is the diagonal sum of the exact rational
-- side-four inverse already constructed by FreeGreen, over its literal
-- 3 x (4^4 x 4) coordinate enumeration.
--
-- It is intentionally a raw finite-volume contraction.  Identifying it with
-- the Haar contribution to a background-dependent vacuum-polarization
-- two-jet still requires the background insertion and Wick/diagram argument;
-- this scalar trace neither assumes nor supplies that missing calculation.
------------------------------------------------------------------------

literalHaarQuadraticTadpoleTrace : ℚ
literalHaarQuadraticTadpoleTrace =
  (+ 1 / 3) *
  sumRational
    (GreenCoordinates.coordinates
      GreenCoordinates.physicalFiniteRationalCoordinates)
    (λ coordinate →
      FreeGreen.configuredGreenOperatorMatrix coordinate coordinate)

literalHaarQuadraticTadpoleTraceLevel : ProofLevel
literalHaarQuadraticTadpoleTraceLevel = conditional

------------------------------------------------------------------------
-- Wilson AAqq contraction on the same carrier.
--
-- `physicalWilsonFourthDerivative` is a diagonal fourth derivative.  The
-- following alternating formula is its literal four-direction polarization.
-- It is then contracted in its two fluctuation slots against the exact Green
-- matrix.  No diagrammatic factor is concealed here: this is the raw
-- AAqq--Green tensor contraction, before the convention-dependent one-loop
-- effective-action normalization and the Fourier/mixed-momentum extraction.
------------------------------------------------------------------------

zeroP33Tangent : P33.PhysicalSU2BondField4
zeroP33Tangent coordinate bond = 0ℚ

addP33Tangent : P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4
addP33Tangent left right coordinate bond =
  left coordinate bond + right coordinate bond

sum3P33Tangent : P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4
sum3P33Tangent first second third =
  addP33Tangent (addP33Tangent first second) third

sum4P33Tangent : P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4
sum4P33Tangent first second third fourth =
  addP33Tangent (sum3P33Tangent first second third) fourth

p33WilsonQuarticMixedVertex :
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 → ℚ
p33WilsonQuarticMixedVertex first second third fourth =
  (+ 1 / 24) *
  ( Wilson.physicalWilsonQuarticVertex Background.identityBackground
      (sum4P33Tangent first second third fourth)
    - ( Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (sum3P33Tangent first second third)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (sum3P33Tangent first second fourth)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (sum3P33Tangent first third fourth)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (sum3P33Tangent second third fourth))
    + ( Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (addP33Tangent first second)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (addP33Tangent first third)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (addP33Tangent first fourth)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (addP33Tangent second third)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (addP33Tangent second fourth)
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground
        (addP33Tangent third fourth))
    - ( Wilson.physicalWilsonQuarticVertex Background.identityBackground first
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground second
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground third
      + Wilson.physicalWilsonQuarticVertex Background.identityBackground fourth)
    + Wilson.physicalWilsonQuarticVertex Background.identityBackground zeroP33Tangent )

p33ConfiguredCoordinateTangent :
  GreenCoordinates.PhysicalSU2Coordinate4 → P33.PhysicalSU2BondField4
p33ConfiguredCoordinateTangent coordinate =
  configuredAsP33Tangent
    (GreenCoordinates.coordinateBasisTangent coordinate)

literalWilsonAAqqGreenContraction :
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 → ℚ
literalWilsonAAqqGreenContraction externalLeft externalRight =
  sumRational
    (GreenCoordinates.coordinates
      GreenCoordinates.physicalFiniteRationalCoordinates)
    (λ row →
      sumRational
        (GreenCoordinates.coordinates
          GreenCoordinates.physicalFiniteRationalCoordinates)
        (λ column →
          p33WilsonQuarticMixedVertex
            externalLeft externalRight
            (p33ConfiguredCoordinateTangent row)
            (p33ConfiguredCoordinateTangent column)
          * FreeGreen.configuredGreenOperatorMatrix row column))

literalWilsonAAqqGreenContractionLevel : ProofLevel
literalWilsonAAqqGreenContractionLevel = conditional

------------------------------------------------------------------------
-- Wilson bubble: two explicit Aqq cubic vertices and two Green entries.
------------------------------------------------------------------------

p33WilsonCubicMixedVertex :
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 →
  P33.PhysicalSU2BondField4 → ℚ
p33WilsonCubicMixedVertex first second third =
  (+ 1 / 6) *
  ( Wilson.physicalWilsonCubicVertex Background.identityBackground
      (sum3P33Tangent first second third)
    - ( Wilson.physicalWilsonCubicVertex Background.identityBackground
        (addP33Tangent first second)
      + Wilson.physicalWilsonCubicVertex Background.identityBackground
        (addP33Tangent first third)
      + Wilson.physicalWilsonCubicVertex Background.identityBackground
        (addP33Tangent second third))
    + ( Wilson.physicalWilsonCubicVertex Background.identityBackground first
      + Wilson.physicalWilsonCubicVertex Background.identityBackground second
      + Wilson.physicalWilsonCubicVertex Background.identityBackground third)
    - Wilson.physicalWilsonCubicVertex Background.identityBackground
        zeroP33Tangent )

literalWilsonCubicBubbleGreenContraction :
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 → ℚ
literalWilsonCubicBubbleGreenContraction externalLeft externalRight =
  sumRational
    (GreenCoordinates.coordinates
      GreenCoordinates.physicalFiniteRationalCoordinates)
    (λ firstRow →
      sumRational
        (GreenCoordinates.coordinates
          GreenCoordinates.physicalFiniteRationalCoordinates)
        (λ secondRow →
          sumRational
            (GreenCoordinates.coordinates
              GreenCoordinates.physicalFiniteRationalCoordinates)
            (λ firstColumn →
              sumRational
                (GreenCoordinates.coordinates
                  GreenCoordinates.physicalFiniteRationalCoordinates)
                (λ secondColumn →
                  p33WilsonCubicMixedVertex
                    externalLeft
                    (p33ConfiguredCoordinateTangent firstRow)
                    (p33ConfiguredCoordinateTangent secondRow)
                  * FreeGreen.configuredGreenOperatorMatrix firstRow firstColumn
                  * FreeGreen.configuredGreenOperatorMatrix secondRow secondColumn
                  * p33WilsonCubicMixedVertex
                      externalRight
                      (p33ConfiguredCoordinateTangent firstColumn)
                      (p33ConfiguredCoordinateTangent secondColumn)))))

literalWilsonCubicBubbleGreenContractionLevel : ProofLevel
literalWilsonCubicBubbleGreenContractionLevel = conditional

------------------------------------------------------------------------
-- Second and fourth derivatives of the same finite gauge-fixed action.
------------------------------------------------------------------------

physicalWilsonSecondDerivative :
  Background.RationalSU2Background4 → P33.PhysicalSU2BondField4 → ℚ
physicalWilsonSecondDerivative = Background.physicalWilsonSecondVariation

physicalHaarSecondDerivative : P33.PhysicalSU2BondField4 → ℚ
physicalHaarSecondDerivative field =
  Haar.physicalHaarSecondDerivative (p33AsPhysicalField field)

physicalReducedFaddeevPopovSecondDerivative :
  P33.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 → ℚ
physicalReducedFaddeevPopovSecondDerivative field anchor =
  - ((+ 2 / 1) * TraceJet.jetCoefficient2
    (FP.physicalGhostTraceLogJet field anchor))

-- The reduced trace-log has already performed the ghost contraction against
-- the exact reduced ghost inverse.  This is its external AA coefficient by
-- the ordinary two-direction polarization; no second, fictitious ghost
-- propagator is introduced here.
literalReducedFaddeevPopovAATwoJet :
  P33.PhysicalSU2BondField4 → P33.PhysicalSU2BondField4 →
  Block.PhysicalBlockL Path4.side4 → ℚ
literalReducedFaddeevPopovAATwoJet externalLeft externalRight anchor =
  (+ 1 / 2) *
  ( physicalReducedFaddeevPopovSecondDerivative
      (addP33Tangent externalLeft externalRight) anchor
    - physicalReducedFaddeevPopovSecondDerivative externalLeft anchor
    - physicalReducedFaddeevPopovSecondDerivative externalRight anchor
    + physicalReducedFaddeevPopovSecondDerivative zeroP33Tangent anchor )

literalReducedFaddeevPopovAATwoJetLevel : ProofLevel
literalReducedFaddeevPopovAATwoJetLevel = conditional

literalGaugeFixedFlatSecondActionJet :
  P33.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 → ℚ
literalGaugeFixedFlatSecondActionJet field anchor =
  physicalWilsonSecondDerivative Background.identityBackground field
  + physicalHaarSecondDerivative field
  + physicalReducedFaddeevPopovSecondDerivative field anchor

physicalWilsonFourthDerivative :
  Background.RationalSU2Background4 → P33.PhysicalSU2BondField4 → ℚ
physicalWilsonFourthDerivative = Wilson.physicalWilsonQuarticVertex

physicalHaarFourthDerivative : P33.PhysicalSU2BondField4 → ℚ
physicalHaarFourthDerivative field =
  Haar.physicalHaarFourthDerivative (p33AsPhysicalField field)

physicalReducedFaddeevPopovFourthDerivative :
  P33.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 → ℚ
physicalReducedFaddeevPopovFourthDerivative field anchor =
  - ((+ 24 / 1) * TraceJet.jetCoefficient4
    (FP.physicalGhostTraceLogJet field anchor))

literalGaugeFixedFlatFourthDerivative :
  P33.PhysicalSU2BondField4 → Block.PhysicalBlockL Path4.side4 → ℚ
literalGaugeFixedFlatFourthDerivative field anchor =
  physicalWilsonFourthDerivative Background.identityBackground field
  + physicalHaarFourthDerivative field
  + physicalReducedFaddeevPopovFourthDerivative field anchor

-- The three vertices are definitionally present on one carrier.  This status
-- remains conditional until the focused source check and the exact
-- finite-volume determinant/Haar chart identification are completed.
literalWilsonFPHaarFourthJetSameCarrierLevel : ProofLevel
literalWilsonFPHaarFourthJetSameCarrierLevel = conditional

literalWilsonFPHaarSecondDerivativeLevel : ProofLevel
literalWilsonFPHaarSecondDerivativeLevel = conditional

literalFlatFluctuationGreenIdentificationLevel : ProofLevel
literalFlatFluctuationGreenIdentificationLevel = conditional

literalWilsonFPHaarFourthDerivativeLevel : ProofLevel
literalWilsonFPHaarFourthDerivativeLevel = conditional
