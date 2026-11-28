module DASHI.Moonshine.CM163BishopHecke41NativeGateAdmissionExact where

-- Separate expensive kernel target. Each decision must reduce to yes.
-- No postulate, trustMe, hash or external Boolean receipt.
open import Relation.Nullary.Decidable.Core using (from-yes)
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopOriginalPhaseHeckeCuspWeldExact as Source

module O = Source.ConcreteOriginal

unit : O.Residual.R.W.UnitGate
unit = from-yes Cert.unitCheck

diagonal : O.Residual.R.W.DiagonalGate
diagonal = from-yes Cert.diagCheck

slice : O.Residual.R.W.SliceGate
slice = from-yes Cert.sliceCheck

gates : O.CuspSourceGates
gates = record { unit = unit ; diagonal = diagonal ; slice = slice }
