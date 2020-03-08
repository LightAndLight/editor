{-# language GADTs #-}
{-# language ScopedTypeVariables, TypeApplications #-}
module Focus where

import qualified Bound

import Path (P(..), Path, TargetInfo(..), HasTargetInfo, targetInfo)
import qualified Path
import qualified Syntax

data Branch a where
  Branch :: HasTargetInfo b => Path a b -> b -> Branch a

data Selection a where
  Selection :: HasTargetInfo b => Path a b -> Selection a

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
            Syntax.TUnsolved{} -> error "todo"
            Syntax.TSubst{} -> error "todo"
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
            Var ->
              case val of
                Syntax.Var val' ->
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
            TVar ->
              case val of
                Syntax.TVar val' ->
                  goDown (Path.snoc prefix p) bs suffix' val'
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
