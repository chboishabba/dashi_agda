{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CCTouchedSignedRowsRound822Exact where

------------------------------------------------------------------------
-- R822: CC-touched orbit rows with an *attached* comparable certificate.
--
-- R818 can select a comparable p/q/base representative of each CC-touched
-- original incidence. Do not replace the original residual scalar by a
-- residual evaluated at the representative: that would require a distinct
-- signed orbit-transport theorem and can change its output mode.
--
-- This owner preserves both original incidence and its literal R760 paired
-- signed scalar, while giving each selected row R204's localized comparable
-- witness.  Selection is exact, with no Gram/positivity estimate, no
-- additional multiplicity, and no absolute values.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650CCTouchedComparableRepresentativeRound818Exact as R818
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204

F : C3.RealField _
F = Rational.rationalRealField

data SignedComparableRow : Set where
  signedComparableRow :
    (beta : Physical.PhysicalTriadIncidence) →
    R781.ccTouched beta ≡ true →
    SignedComparableRow

originalIncidence : SignedComparableRow → Physical.PhysicalTriadIncidence
originalIncidence (signedComparableRow beta proof) = beta

selectedRepresentative :
  (row : SignedComparableRow) →
  R818.CCTouchedRepresentative (originalIncidence row)
selectedRepresentative (signedComparableRow beta proof) =
  R818.ccTouchedSelectsComparableRepresentative beta proof

localizedRepresentative :
  (row : SignedComparableRow) →
  R204.LocalizedComparableIncidence
localizedRepresentative row =
  R818.representativeLocalized (selectedRepresentative row)

selectComparableRows :
  List Physical.PhysicalTriadIncidence → List SignedComparableRow
selectComparableRows [] = []
selectComparableRows (beta ∷ xs)
  with R781.ccTouched beta in touched
... | true =
  signedComparableRow beta touched ∷ selectComparableRows xs
... | false = selectComparableRows xs

signedRowFold :
  (cell : Physical.PhysicalTriadIncidence → ℚ) →
  List SignedComparableRow → ℚ
signedRowFold cell [] = 0ℚ
signedRowFold cell (row ∷ rest) =
  cell (originalIncidence row) + signedRowFold cell rest

maskTouchedCell :
  (cell : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
maskTouchedCell cell beta with R781.ccTouched beta
... | true = cell beta
... | false = 0ℚ

-- No quotient, deduplication, or reindexing: the selected list retains the
-- same original scalar with exactly its original multiplicity.
exactComparableRowFold :
  (cell : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  signedRowFold cell (selectComparableRows items)
  ≡ R38.foldPower (maskTouchedCell cell) items
exactComparableRowFold cell [] = refl
exactComparableRowFold cell (beta ∷ rest)
  with R781.ccTouched beta
... | true =
  cong₂ _+_ refl (exactComparableRowFold cell rest)
... | false =
  trans (exactComparableRowFold cell rest)
    (sym (solve (R38.foldPower (maskTouchedCell cell) rest ∷ [])))

module CCTouchedSignedRows
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where


  module Two = R781.TwoFamilyResidual
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Two.Packet

  module At
      (cutoff : Nat) (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = Two.At cutoff time S

    -- Kept at beta, NOT evaluated at the CC representative.
    originalSignedCell :
      Physical.PhysicalTriadIncidence → ℚ
    originalSignedCell = P.P.swapPairedResidualCell

    comparableRows : List SignedComparableRow
    comparableRows = selectComparableRows P.P.items

    comparableSignedFold : ℚ
    comparableSignedFold =
      signedRowFold originalSignedCell comparableRows

    touchedCellSameMask :
      (beta : Physical.PhysicalTriadIncidence) →
      P.ccTouchedCell beta ≡ maskTouchedCell originalSignedCell beta
    touchedCellSameMask beta with R781.ccTouched beta
    ... | true = refl
    ... | false = refl

    foldSameMask :
      (xs : List Physical.PhysicalTriadIncidence) →
      R38.foldPower P.ccTouchedCell xs
      ≡ R38.foldPower (maskTouchedCell originalSignedCell) xs
    foldSameMask [] = refl
    foldSameMask (beta ∷ rest) =
      cong₂ _+_ (touchedCellSameMask beta) (foldSameMask rest)

    actualCCTouchedFoldIsComparableRows :
      P.ccTouchedFold ≡ comparableSignedFold
    actualCCTouchedFoldIsComparableRows =
      trans
        (foldSameMask P.P.items)
        (sym (exactComparableRowFold originalSignedCell P.P.items))

round822RowsCarryLiteralComparableCertificates : Bool
round822RowsCarryLiteralComparableCertificates = true

round822OriginalSignedScalarRetainedWithoutReindexing : Bool
round822OriginalSignedScalarRetainedWithoutReindexing = true

round822FoldEqualToActualR781CCTouched : Bool
round822FoldEqualToActualR781CCTouched = true

round822ComparableLocalizationPaysGramDebt : Bool
round822ComparableLocalizationPaysGramDebt = false

round822IntegratedSignedPaymentClosed : Bool
round822IntegratedSignedPaymentClosed = false

round822ClayPromotion : Bool
round822ClayPromotion = false
