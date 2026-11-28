module DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesAcceptanceExact where

-- PAPER 9 G1/G2 NATIVE ACCEPTANCE ONLY, unexecuted.
-- This is intentionally a separate entrypoint. It must fail closed
-- if ANY concrete matrix or target-node decision is not definitionally yes.
-- No fabricated numerical receipt, postulate, trustMe or analytic promotion.
open import Relation.Nullary.Decidable.Core using (from-yes)
import DASHI.Moonshine.CM163Hecke41FullIntegerMatrixExact as M
import DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesExact as Nodes
import DASHI.Foundations.BishopConcreteElementaryCutsetExact as Concrete

import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert

module N = Nodes.At Concrete.concreteCutset

unit : N.R.L.W.UnitGate
unit = from-yes Cert.unitCheck

newton : M.NewtonGate M.C.j (M.elementaries M.C.j)
newton = from-yes M.originalNewtonCheck

columns : M.ColumnGate M.C.j (M.elementaries M.C.j) M.originalMatrix
columns = from-yes M.originalColumnCheck

symmetry : M.SymmetryGate M.originalMatrix
symmetry = from-yes M.originalSymmetryCheck

packet : M.PacketGate M.originalMatrix
packet = from-yes M.originalPacketCheck

nodes : N.NodeGates
nodes = from-yes N.nodes?

-- Only finite prefix and pole-removal identities may be consumed here.
-- Global residual zero and all-real FullIdentity still require
-- independent constructive analytic and interpolation theorems.
