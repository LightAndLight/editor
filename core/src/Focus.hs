{-# language GADTs #-}
{-# language ScopedTypeVariables, TypeApplications #-}
{-# language StandaloneDeriving #-}
module Focus where

import qualified Bound
import Control.Lens.Indexed (ifoldl, ifoldr)
import qualified Data.Vector as Vector

import Path (P(..), Path, TargetInfo(..), HasTargetInfo, targetInfo)
import qualified Path
import qualified Syntax

data Branch a where
  Branch :: HasTargetInfo b => Path a b -> b -> Branch a

data Selection a where
  Selection :: HasTargetInfo b => Path a b -> Selection a
deriving instance Show (Selection a)

nextHole :: HasTargetInfo b => Path a b -> a -> Maybe (Selection a)
nextHole = goDown Path.empty []
  where
    continue :: forall x. [Branch x] -> Maybe (Selection x)
    continue bs =
      case bs of
        [] -> Nothing
        Branch prefix' val' : bbs -> search prefix' bbs val'

    search ::
      forall x a.
      HasTargetInfo a =>
      Path x a ->
      [Branch x] ->
      a ->
      Maybe (Selection x)
    search prefix bs val =
      case targetInfo @a of
        TargetTerm ->
          case val of
            Syntax.Hole -> Just $ Selection prefix
            Syntax.Var{} -> continue bs
            Syntax.Name{} -> continue bs
            Syntax.Ann a b ->
              search
                (Path.snoc prefix AnnL)
                (Branch (Path.snoc prefix AnnR) b : bs)
                a
            Syntax.App a b ->
              search
                (Path.snoc prefix AppL)
                (Branch (Path.snoc prefix AppR) b : bs)
                a
            Syntax.Lam n body ->
              search
                (Path.snoc prefix LamArg)
                (Branch (Path.snoc prefix LamBody) (Bound.fromScope body) : bs)
                n
            Syntax.LamAnn n ty body ->
              search
                (Path.snoc prefix LamAnnArg)
                (Branch (Path.snoc prefix LamAnnType) ty :
                 Branch (Path.snoc prefix LamAnnBody) (Bound.fromScope body) :
                 bs
                )
                n
        TargetType ->
          case val of
            Syntax.THole -> Just $ Selection prefix
            Syntax.TMeta{} -> continue bs
            Syntax.TVar{} -> continue bs
            Syntax.TName{} -> continue bs
            Syntax.TForall n body ->
              search
                (Path.snoc prefix TForallArg)
                (Branch (Path.snoc prefix TForallBody) (Bound.fromScope body): bs)
                n
            Syntax.TArr a b ->
              search
                (Path.snoc prefix TArrL)
                (Branch (Path.snoc prefix TArrR) b : bs)
                a
            Syntax.TUnsolved _ body ->
              search
                (Path.snoc prefix TUnsolvedBody)
                bs
                (Bound.fromScope body)
            Syntax.TSubst a xs ->
              search
                (Path.snoc prefix TSubstL)
                (ifoldr
                   (\i e rest ->
                      Branch (Path.snoc prefix $ TSubstR i) e : rest
                   )
                   bs
                   xs
                )
                a
        TargetName -> continue bs

    goDown ::
      forall x a b.
      HasTargetInfo b =>
      Path x a ->
      [Branch x] ->
      Path a b ->
      a ->
      Maybe (Selection x)
    goDown prefix bs suffix val =
      case Path.viewl suffix of
        Path.EmptyL -> continue bs
        p Path.:< suffix' -> do
          case p of
            AppL ->
              case val of
                Syntax.App val' y ->
                  goDown (Path.snoc prefix p) (Branch (Path.snoc prefix AppR) y : bs) suffix' val'
                _ -> Nothing
            AppR ->
              case val of
                Syntax.App _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            AnnL ->
              case val of
                Syntax.Ann val' y ->
                  goDown (Path.snoc prefix p) (Branch (Path.snoc prefix AnnR) y : bs) suffix' val'
                _ -> Nothing
            AnnR ->
              case val of
                Syntax.Ann _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            LamArg ->
              case val of
                Syntax.Lam val' x ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix LamBody) (Bound.fromScope x) : bs)
                    suffix'
                    val'
                _ -> Nothing
            LamBody ->
              case val of
                Syntax.Lam _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' (Bound.fromScope val')
                _ -> Nothing
            LamAnnArg ->
              case val of
                Syntax.LamAnn val' ty x ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix LamAnnType) ty :
                     Branch (Path.snoc prefix LamAnnBody) (Bound.fromScope x) :
                     bs
                    )
                    suffix'
                    val'
                _ -> Nothing
            LamAnnType ->
              case val of
                Syntax.LamAnn _ val' x ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix LamAnnBody) (Bound.fromScope x) : bs)
                    suffix'
                    val'
                _ -> Nothing
            LamAnnBody ->
              case val of
                Syntax.LamAnn _ _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' (Bound.fromScope val')
                _ -> Nothing
            TArrL ->
              case val of
                Syntax.TArr val' y ->
                  goDown (Path.snoc prefix p) (Branch (Path.snoc prefix TArrR) y : bs) suffix' val'
                _ -> Nothing
            TArrR ->
              case val of
                Syntax.TArr _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            TForallArg ->
              case val of
                Syntax.TForall val' x ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix TForallBody) (Bound.fromScope x) : bs)
                    suffix'
                    val'
                _ -> Nothing
            TForallBody ->
              case val of
                Syntax.TForall _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' (Bound.fromScope val')
                _ -> Nothing
            TUnsolvedBody ->
              case val of
                Syntax.TUnsolved _ val' ->
                  goDown (Path.snoc prefix p) bs suffix' (Bound.fromScope val')
                _ -> Nothing
            TSubstL ->
              case val of
                Syntax.TSubst val' xs ->
                  goDown
                    (Path.snoc prefix p)
                    (ifoldr
                       (\i e rest ->
                          Branch (Path.snoc prefix $ Path.TSubstR i) e : rest
                       )
                       bs
                       xs
                    )
                    suffix'
                    val'
                _ -> Nothing
            TSubstR n ->
              case val of
                Syntax.TSubst _ xs ->
                  goDown
                    (Path.snoc prefix p)
                    (ifoldr
                       (\i e rest ->
                          if i <= n
                          then Branch (Path.snoc prefix $ Path.TSubstR i) e : rest
                          else rest
                       )
                       bs
                       xs
                    )
                    suffix'
                    (xs Vector.! n)
                _ -> Nothing

prevHole :: HasTargetInfo b => Path a b -> a -> Maybe (Selection a)
prevHole = goDown Path.empty []
  where
    continue :: forall x. [Branch x] -> Maybe (Selection x)
    continue bs =
      case bs of
        [] -> Nothing
        Branch prefix' val' : bbs -> search prefix' bbs val'

    search ::
      forall x a.
      HasTargetInfo a =>
      Path x a ->
      [Branch x] ->
      a ->
      Maybe (Selection x)
    search prefix bs val =
      case targetInfo @a of
        TargetTerm ->
          case val of
            Syntax.Hole -> Just $ Selection prefix
            Syntax.Var{} -> continue bs
            Syntax.Name{} -> continue bs
            Syntax.App a b ->
              search
                (Path.snoc prefix AppR)
                (Branch (Path.snoc prefix AppL) a : bs)
                b
            Syntax.Ann a b ->
              search
                (Path.snoc prefix AnnR)
                (Branch (Path.snoc prefix AnnL) a : bs)
                b
            Syntax.Lam n body ->
              search
                (Path.snoc prefix LamBody)
                (Branch (Path.snoc prefix LamArg) n : bs)
                (Bound.fromScope body)
            Syntax.LamAnn n ty body ->
              search
                (Path.snoc prefix LamAnnBody)
                (Branch (Path.snoc prefix LamAnnType) ty :
                 Branch (Path.snoc prefix LamAnnArg) n :
                 bs
                )
                (Bound.fromScope body)
        TargetType ->
          case val of
            Syntax.THole -> Just $ Selection prefix
            Syntax.TMeta{} -> continue bs
            Syntax.TVar{} -> continue bs
            Syntax.TName{} -> continue bs
            Syntax.TForall n body ->
              search
                (Path.snoc prefix TForallBody)
                (Branch (Path.snoc prefix TForallArg) n : bs)
                (Bound.fromScope body)
            Syntax.TArr a b ->
              search
                (Path.snoc prefix TArrR)
                (Branch (Path.snoc prefix TArrL) a : bs)
                b
            Syntax.TUnsolved _ body ->
              search
                (Path.snoc prefix TUnsolvedBody)
                bs
                (Bound.fromScope body)
            Syntax.TSubst a xs ->
              search
                (Path.snoc prefix $ TSubstR (Vector.length xs - 1))
                (ifoldl
                   (\i rest e ->
                      Branch (Path.snoc prefix $ TSubstR i) e : rest
                   )
                   (Branch (Path.snoc prefix TSubstL) a : bs)
                   (Vector.init xs)
                )
                (Vector.last xs)
        TargetName -> continue bs

    goDown ::
      forall x a b.
      HasTargetInfo b =>
      Path x a ->
      [Branch x] ->
      Path a b ->
      a ->
      Maybe (Selection x)
    goDown prefix bs suffix val =
      case Path.viewl suffix of
        Path.EmptyL -> continue bs
        p Path.:< suffix' -> do
          case p of
            AppL ->
              case val of
                Syntax.App val' _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            AppR ->
              case val of
                Syntax.App x val' ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix AppL) x : bs)
                    suffix'
                    val'
                _ -> Nothing
            AnnL ->
              case val of
                Syntax.Ann val' _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            AnnR ->
              case val of
                Syntax.Ann x val' ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix AnnL) x : bs)
                    suffix'
                    val'
                _ -> Nothing
            LamArg ->
              case val of
                Syntax.Lam val' _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            LamBody ->
              case val of
                Syntax.Lam n val' ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix LamArg) n : bs)
                    suffix'
                    (Bound.fromScope val')
                _ -> Nothing
            LamAnnArg ->
              case val of
                Syntax.LamAnn val' _ _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            LamAnnType ->
              case val of
                Syntax.LamAnn n val' _ ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix LamAnnArg) n : bs)
                    suffix'
                    val'
                _ -> Nothing
            LamAnnBody ->
              case val of
                Syntax.LamAnn n ty val' ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix LamAnnType) ty :
                     Branch (Path.snoc prefix LamAnnArg) n :
                     bs
                    )
                    suffix'
                    (Bound.fromScope val')
                _ -> Nothing
            TArrL ->
              case val of
                Syntax.TArr val' _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            TArrR ->
              case val of
                Syntax.TArr x val' ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix TArrL) x : bs)
                    suffix'
                    val'
                _ -> Nothing
            TForallArg ->
              case val of
                Syntax.TForall val' _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            TForallBody ->
              case val of
                Syntax.TForall n val' ->
                  goDown
                    (Path.snoc prefix p)
                    (Branch (Path.snoc prefix TForallArg) n: bs)
                    suffix'
                    (Bound.fromScope val')
                _ -> Nothing
            TUnsolvedBody ->
              case val of
                Syntax.TUnsolved _ val' ->
                  goDown
                    (Path.snoc prefix p)
                    bs
                    suffix'
                    (Bound.fromScope val')
                _ -> Nothing
            TSubstL ->
              case val of
                Syntax.TSubst val' _ ->
                  goDown (Path.snoc prefix p) bs suffix' val'
                _ -> Nothing
            TSubstR n ->
              case val of
                Syntax.TSubst a xs ->
                  goDown
                    (Path.snoc prefix p)
                    (ifoldl
                       (\i rest e ->
                          if n < i
                          then Branch (Path.snoc prefix $ TSubstR i) e : rest
                          else rest
                       )
                       (Branch (Path.snoc prefix TSubstL) a : bs)
                       xs
                    )
                    suffix'
                    (xs Vector.! n)
                _ -> Nothing
