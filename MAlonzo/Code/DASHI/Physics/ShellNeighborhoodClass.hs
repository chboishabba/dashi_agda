{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.DASHI.Physics.ShellNeighborhoodClass where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat

-- DASHI.Physics.ShellNeighborhoodClass.ShellNeighborhoodClass
d_ShellNeighborhoodClass_6 = ()
data T_ShellNeighborhoodClass_6
  = C_definiteShellNeighborhood_8 | C_oneMinusShellNeighborhood_10 |
    C_mixed21ShellNeighborhood_12 | C_split22ShellNeighborhood_14 |
    C_unknownShellNeighborhood_16
-- DASHI.Physics.ShellNeighborhoodClass.natEq
d_natEq_18 :: Integer -> Integer -> Bool
d_natEq_18 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d_natEq_18 (coe v2) (coe v3)))
-- DASHI.Physics.ShellNeighborhoodClass.natEq-self
d_natEq'45'self_30 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_natEq'45'self_30 = erased
-- DASHI.Physics.ShellNeighborhoodClass.isEven
d_isEven_34 :: Integer -> Bool
d_isEven_34 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe (coe d_isEven_34 (coe v1))
-- DASHI.Physics.ShellNeighborhoodClass.listNatEq
d_listNatEq_38 :: [Integer] -> [Integer] -> Bool
d_listNatEq_38 v0 v1
  = case coe v0 of
      []
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             (:) v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v2 v3
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             (:) v4 v5
               -> let v6 = d_natEq_18 (coe v2) (coe v4) in
                  coe
                    (if coe v6 then coe d_listNatEq_38 (coe v3) (coe v5) else coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- DASHI.Physics.ShellNeighborhoodClass.isOneMinusTriple
d_isOneMinusTriple_68 :: Integer -> Integer -> Integer -> Bool
d_isOneMinusTriple_68 v0 v1 v2
  = let v3 = d_natEq_18 (coe v2) (coe (2 :: Integer)) in
    coe
      (if coe v3
         then coe
                d_natEq_18 (coe v0)
                (coe
                   mulInt (coe v1)
                   (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (2 :: Integer)))
         else coe v3)
-- DASHI.Physics.ShellNeighborhoodClass.classifyTripleChecks
d_classifyTripleChecks_108 ::
  Bool -> Bool -> T_ShellNeighborhoodClass_6
d_classifyTripleChecks_108 v0 v1
  = if coe v0
      then if coe v1
             then coe C_oneMinusShellNeighborhood_10
             else coe C_unknownShellNeighborhood_16
      else coe C_unknownShellNeighborhood_16
-- DASHI.Physics.ShellNeighborhoodClass.classifyTriple
d_classifyTriple_110 ::
  Integer -> Integer -> Integer -> T_ShellNeighborhoodClass_6
d_classifyTriple_110 v0 v1 v2
  = coe
      d_classifyTripleChecks_108
      (coe d_natEq_18 (coe v2) (coe (2 :: Integer)))
      (coe
         d_natEq_18 (coe v0)
         (coe
            mulInt (coe v1)
            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (2 :: Integer))))
-- DASHI.Physics.ShellNeighborhoodClass.classifyTripleChecks-tt
d_classifyTripleChecks'45'tt_118 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyTripleChecks'45'tt_118 = erased
-- DASHI.Physics.ShellNeighborhoodClass.classifyTriple-oneMinus
d_classifyTriple'45'oneMinus_122 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyTriple'45'oneMinus_122 = erased
-- DASHI.Physics.ShellNeighborhoodClass.classifyShell1Neighborhood
d_classifyShell1Neighborhood_134 ::
  [Integer] -> T_ShellNeighborhoodClass_6
d_classifyShell1Neighborhood_134 v0
  = case coe v0 of
      [] -> coe C_unknownShellNeighborhood_16
      (:) v1 v2
        -> let v3
                 = case coe v2 of
                     [] -> coe C_unknownShellNeighborhood_16
                     (:) v3 v4
                       -> case coe v4 of
                            [] -> coe C_unknownShellNeighborhood_16
                            (:) v5 v6
                              -> case coe v6 of
                                   [] -> coe d_classifyTriple_110 (coe v1) (coe v3) (coe v5)
                                   (:) v7 v8 -> coe C_unknownShellNeighborhood_16
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                    let v4
                          = case coe v2 of
                              [] -> coe C_unknownShellNeighborhood_16
                              (:) v4 v5
                                -> case coe v5 of
                                     [] -> coe C_unknownShellNeighborhood_16
                                     (:) v6 v7
                                       -> case coe v7 of
                                            []
                                              -> coe d_classifyTriple_110 (coe v1) (coe v4) (coe v6)
                                            _ -> coe v3
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (case coe v1 of
                         _ | coe geqInt (coe v1) (coe (2 :: Integer)) ->
                             let v5
                                   = case coe v2 of
                                       [] -> coe C_unknownShellNeighborhood_16
                                       (:) v5 v6
                                         -> case coe v6 of
                                              [] -> coe C_unknownShellNeighborhood_16
                                              (:) v7 v8
                                                -> case coe v8 of
                                                     []
                                                       -> coe
                                                            d_classifyTriple_110 (coe v1) (coe v5)
                                                            (coe v7)
                                                     _ -> coe v4
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError in
                             coe
                               (case coe v1 of
                                  2 -> case coe v2 of
                                         [] -> coe C_unknownShellNeighborhood_16
                                         (:) v6 v7
                                           -> case coe v6 of
                                                2 -> case coe v7 of
                                                       [] -> coe C_oneMinusShellNeighborhood_10
                                                       _ -> coe v5
                                                _ | coe geqInt (coe v6) (coe (2 :: Integer)) ->
                                                    coe v5
                                                1 -> coe v5
                                                _ -> coe v5
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ | coe geqInt (coe v1) (coe (3 :: Integer)) ->
                                      let v6
                                            = case coe v2 of
                                                [] -> coe C_unknownShellNeighborhood_16
                                                (:) v6 v7
                                                  -> case coe v7 of
                                                       [] -> coe C_unknownShellNeighborhood_16
                                                       (:) v8 v9
                                                         -> case coe v9 of
                                                              []
                                                                -> coe
                                                                     d_classifyTriple_110 (coe v1)
                                                                     (coe v6) (coe v8)
                                                              _ -> coe v5
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError in
                                      coe
                                        (case coe v1 of
                                           _ | coe geqInt (coe v1) (coe (4 :: Integer)) ->
                                               let v7
                                                     = case coe v2 of
                                                         [] -> coe C_unknownShellNeighborhood_16
                                                         (:) v7 v8
                                                           -> case coe v8 of
                                                                []
                                                                  -> coe
                                                                       C_unknownShellNeighborhood_16
                                                                (:) v9 v10
                                                                  -> case coe v10 of
                                                                       []
                                                                         -> coe
                                                                              d_classifyTriple_110
                                                                              (coe v1) (coe v7)
                                                                              (coe v9)
                                                                       _ -> coe v6
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError in
                                               coe
                                                 (case coe v1 of
                                                    _ | coe geqInt (coe v1) (coe (5 :: Integer)) ->
                                                        let v8
                                                              = case coe v2 of
                                                                  []
                                                                    -> coe
                                                                         C_unknownShellNeighborhood_16
                                                                  (:) v8 v9
                                                                    -> case coe v9 of
                                                                         []
                                                                           -> coe
                                                                                C_unknownShellNeighborhood_16
                                                                         (:) v10 v11
                                                                           -> case coe v11 of
                                                                                []
                                                                                  -> coe
                                                                                       d_classifyTriple_110
                                                                                       (coe v1)
                                                                                       (coe v8)
                                                                                       (coe v10)
                                                                                _ -> coe v7
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError in
                                                        coe
                                                          (case coe v1 of
                                                             _ | coe
                                                                   geqInt (coe v1)
                                                                   (coe (6 :: Integer)) ->
                                                                 let v9
                                                                       = case coe v2 of
                                                                           []
                                                                             -> coe
                                                                                  C_unknownShellNeighborhood_16
                                                                           (:) v9 v10
                                                                             -> case coe v10 of
                                                                                  []
                                                                                    -> coe
                                                                                         C_unknownShellNeighborhood_16
                                                                                  (:) v11 v12
                                                                                    -> case coe
                                                                                              v12 of
                                                                                         []
                                                                                           -> coe
                                                                                                d_classifyTriple_110
                                                                                                (coe
                                                                                                   v1)
                                                                                                (coe
                                                                                                   v9)
                                                                                                (coe
                                                                                                   v11)
                                                                                         _ -> coe v8
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError in
                                                                 coe
                                                                   (case coe v1 of
                                                                      _ | coe
                                                                            geqInt (coe v1)
                                                                            (coe (7 :: Integer)) ->
                                                                          let v10
                                                                                = case coe v2 of
                                                                                    []
                                                                                      -> coe
                                                                                           C_unknownShellNeighborhood_16
                                                                                    (:) v10 v11
                                                                                      -> case coe
                                                                                                v11 of
                                                                                           []
                                                                                             -> coe
                                                                                                  C_unknownShellNeighborhood_16
                                                                                           (:) v12 v13
                                                                                             -> case coe
                                                                                                       v13 of
                                                                                                  []
                                                                                                    -> coe
                                                                                                         d_classifyTriple_110
                                                                                                         (coe
                                                                                                            v1)
                                                                                                         (coe
                                                                                                            v10)
                                                                                                         (coe
                                                                                                            v12)
                                                                                                  _ -> coe
                                                                                                         v9
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                                                          coe
                                                                            (case coe v1 of
                                                                               _ | coe
                                                                                     geqInt (coe v1)
                                                                                     (coe
                                                                                        (8 ::
                                                                                           Integer)) ->
                                                                                   let v11
                                                                                         = case coe
                                                                                                  v2 of
                                                                                             []
                                                                                               -> coe
                                                                                                    C_unknownShellNeighborhood_16
                                                                                             (:) v11 v12
                                                                                               -> case coe
                                                                                                         v12 of
                                                                                                    []
                                                                                                      -> coe
                                                                                                           C_unknownShellNeighborhood_16
                                                                                                    (:) v13 v14
                                                                                                      -> case coe
                                                                                                                v14 of
                                                                                                           []
                                                                                                             -> coe
                                                                                                                  d_classifyTriple_110
                                                                                                                  (coe
                                                                                                                     v1)
                                                                                                                  (coe
                                                                                                                     v11)
                                                                                                                  (coe
                                                                                                                     v13)
                                                                                                           _ -> coe
                                                                                                                  v10
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                   coe
                                                                                     (case coe v1 of
                                                                                        8 -> case coe
                                                                                                    v2 of
                                                                                               []
                                                                                                 -> coe
                                                                                                      C_definiteShellNeighborhood_8
                                                                                               (:) v12 v13
                                                                                                 -> case coe
                                                                                                           v13 of
                                                                                                      []
                                                                                                        -> coe
                                                                                                             C_unknownShellNeighborhood_16
                                                                                                      (:) v14 v15
                                                                                                        -> case coe
                                                                                                                  v15 of
                                                                                                             []
                                                                                                               -> coe
                                                                                                                    d_classifyTriple_110
                                                                                                                    (coe
                                                                                                                       v1)
                                                                                                                    (coe
                                                                                                                       v12)
                                                                                                                    (coe
                                                                                                                       v14)
                                                                                                             _ -> coe
                                                                                                                    v10
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ | coe
                                                                                              geqInt
                                                                                              (coe
                                                                                                 v1)
                                                                                              (coe
                                                                                                 (9 ::
                                                                                                    Integer)) ->
                                                                                            case coe
                                                                                                   v2 of
                                                                                              []
                                                                                                -> coe
                                                                                                     C_unknownShellNeighborhood_16
                                                                                              (:) v12 v13
                                                                                                -> case coe
                                                                                                          v13 of
                                                                                                     []
                                                                                                       -> coe
                                                                                                            C_unknownShellNeighborhood_16
                                                                                                     (:) v14 v15
                                                                                                       -> case coe
                                                                                                                 v15 of
                                                                                                            []
                                                                                                              -> coe
                                                                                                                   d_classifyTriple_110
                                                                                                                   (coe
                                                                                                                      v1)
                                                                                                                   (coe
                                                                                                                      v12)
                                                                                                                   (coe
                                                                                                                      v14)
                                                                                                            (:) v16 v17
                                                                                                              -> case coe
                                                                                                                        v1 of
                                                                                                                   16
                                                                                                                     -> case coe
                                                                                                                               v12 of
                                                                                                                          16
                                                                                                                            -> case coe
                                                                                                                                      v14 of
                                                                                                                                 4 -> case coe
                                                                                                                                             v16 of
                                                                                                                                        4 -> case coe
                                                                                                                                                    v17 of
                                                                                                                                               []
                                                                                                                                                 -> coe
                                                                                                                                                      C_split22ShellNeighborhood_14
                                                                                                                                               _ -> coe
                                                                                                                                                      v11
                                                                                                                                        _ | coe
                                                                                                                                              geqInt
                                                                                                                                              (coe
                                                                                                                                                 v16)
                                                                                                                                              (coe
                                                                                                                                                 (4 ::
                                                                                                                                                    Integer)) ->
                                                                                                                                            coe
                                                                                                                                              v11
                                                                                                                                        3 -> coe
                                                                                                                                               v11
                                                                                                                                        2 -> coe
                                                                                                                                               v11
                                                                                                                                        1 -> coe
                                                                                                                                               v11
                                                                                                                                        _ -> coe
                                                                                                                                               v11
                                                                                                                                 _ | coe
                                                                                                                                       geqInt
                                                                                                                                       (coe
                                                                                                                                          v14)
                                                                                                                                       (coe
                                                                                                                                          (4 ::
                                                                                                                                             Integer)) ->
                                                                                                                                     coe
                                                                                                                                       v11
                                                                                                                                 3 -> coe
                                                                                                                                        v11
                                                                                                                                 2 -> coe
                                                                                                                                        v11
                                                                                                                                 1 -> coe
                                                                                                                                        v11
                                                                                                                                 _ -> coe
                                                                                                                                        v11
                                                                                                                          _ | coe
                                                                                                                                geqInt
                                                                                                                                (coe
                                                                                                                                   v12)
                                                                                                                                (coe
                                                                                                                                   (16 ::
                                                                                                                                      Integer)) ->
                                                                                                                              coe
                                                                                                                                v11
                                                                                                                          15
                                                                                                                            -> coe
                                                                                                                                 v11
                                                                                                                          14
                                                                                                                            -> coe
                                                                                                                                 v11
                                                                                                                          13
                                                                                                                            -> coe
                                                                                                                                 v11
                                                                                                                          12
                                                                                                                            -> coe
                                                                                                                                 v11
                                                                                                                          11
                                                                                                                            -> coe
                                                                                                                                 v11
                                                                                                                          10
                                                                                                                            -> coe
                                                                                                                                 v11
                                                                                                                          9 -> coe
                                                                                                                                 v11
                                                                                                                          8 -> coe
                                                                                                                                 v11
                                                                                                                          7 -> coe
                                                                                                                                 v11
                                                                                                                          6 -> coe
                                                                                                                                 v11
                                                                                                                          5 -> coe
                                                                                                                                 v11
                                                                                                                          4 -> coe
                                                                                                                                 v11
                                                                                                                          3 -> coe
                                                                                                                                 v11
                                                                                                                          2 -> coe
                                                                                                                                 v11
                                                                                                                          1 -> coe
                                                                                                                                 v11
                                                                                                                          _ -> coe
                                                                                                                                 v11
                                                                                                                   _ | coe
                                                                                                                         geqInt
                                                                                                                         (coe
                                                                                                                            v1)
                                                                                                                         (coe
                                                                                                                            (16 ::
                                                                                                                               Integer)) ->
                                                                                                                       coe
                                                                                                                         v11
                                                                                                                   15
                                                                                                                     -> coe
                                                                                                                          v11
                                                                                                                   14
                                                                                                                     -> coe
                                                                                                                          v11
                                                                                                                   13
                                                                                                                     -> coe
                                                                                                                          v11
                                                                                                                   12
                                                                                                                     -> coe
                                                                                                                          v11
                                                                                                                   11
                                                                                                                     -> coe
                                                                                                                          v11
                                                                                                                   10
                                                                                                                     -> coe
                                                                                                                          v11
                                                                                                                   _ -> coe
                                                                                                                          v11
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> coe
                                                                                               v11)
                                                                               _ -> coe v10)
                                                                      _ -> coe v9)
                                                             _ -> coe v8)
                                                    _ -> coe v7)
                                           _ -> coe v6)
                                  _ -> coe v5)
                         _ -> coe v4)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
