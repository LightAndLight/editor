{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables, TypeApplications #-}
module Edit where

import qualified Bound

import Syntax (Name, Term, Type)
import qualified Syntax
import Path (Path, TargetInfo(..), HasTargetInfo, targetInfo)
import qualified Path

data Action a b where
  InsertTerm :: Term ty a -> Path (Term ty a) b -> Action (Term ty a) b
  InsertVar :: Name -> Action (Term ty tm) (Term ty tm)
  ModifyTerm ::
    (Term ty a -> Term ty a) ->
    Path (Term ty a) b ->
    Action (Term ty a) b
  DeleteTerm :: Action (Term ty a) (Term ty a)
  ModifyName :: (Name -> Name) -> Action Name Name
  InsertType :: Type a -> Path (Type a) b -> Action (Type a) b
  DeleteType :: Action (Type a) (Type a)

data EditError where
  InvalidPath :: Path a b -> a -> EditError

instance Show EditError where
  show InvalidPath{} = "InvalidPath"

edit ::
  forall src tgt tgt'.
  (HasTargetInfo src, HasTargetInfo tgt') =>
  Path src tgt ->
  TargetInfo tgt ->
  Action tgt tgt' ->
  src ->
  Either EditError (Path src tgt', TargetInfo tgt', src)
edit _ TargetDecl action _ = case action of
edit path TargetTerm action a =
  -- path : Path a (Term x)
  -- action : Edit (Term x) c
  case action of
    InsertTerm tm suffix ->
      case Path.set path tm a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (Path.append path suffix, targetInfo @tgt', a')
    InsertVar n ->
      case targetInfo @src of
        TargetTerm ->
          case insertVar path n a of
            Nothing -> Left $ InvalidPath path a
            Just a' -> Right (path, TargetTerm, a')
        _ -> Left $ InvalidPath path a
    ModifyTerm f suffix ->
      case Path.modify path f a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (Path.append path suffix, targetInfo @tgt', a')
    DeleteTerm ->
      case Path.set path Syntax.Hole a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (path, TargetTerm, a')
edit path TargetName action a =
  -- path : Path a Text
  -- action : Edit Text c
  case action of
    ModifyName f ->
      case Path.modify path f a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (path, TargetName, a')
edit path TargetType action a =
  case action of
    InsertType ty suffix ->
      case Path.set path ty a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (Path.append path suffix, targetInfo @tgt', a')
    DeleteType ->
      case Path.set path Syntax.THole a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (path, TargetType, a')

insertVar ::
  Path (Term ty tm) (Term ty' tm') ->
  Name ->
  Term ty tm ->
  Maybe (Term ty tm)
insertVar = go Syntax.Name
  where
    go ::
      (Name -> Term ty tm) ->
      Path (Term ty tm) (Term ty' tm') ->
      Name ->
      Term ty tm ->
      Maybe (Term ty tm)
    go abstract path n tm =
      case Path.viewl path of
        Path.EmptyL -> Just $ abstract n
        p Path.:< ps ->
          case p of
            Path.LamBody ->
              case tm of
                Syntax.Lam n' body ->
                  Syntax.Lam n' . Bound.toScope <$>
                  go
                    (\x ->
                       if x == n'
                       then Syntax.Var (Bound.B ())
                       else fmap Bound.F $ abstract x
                    )
                    ps
                    n
                    (Bound.fromScope body)
                _ -> Nothing
            Path.LamAnnBody ->
              case tm of
                Syntax.LamAnn n' t body ->
                  Syntax.LamAnn n' t . Bound.toScope <$>
                  go
                    (\x ->
                       if x == n'
                       then Syntax.Var (Bound.B ())
                       else fmap Bound.F $ abstract x
                    )
                    ps
                    n
                    (Bound.fromScope body)
                _ -> Nothing
            Path.AppL -> do
              (tm', mk) <- Path.matchP p tm
              mk <$> go abstract ps n tm'
            Path.AppR -> do
              (tm', mk) <- Path.matchP p tm
              mk <$> go abstract ps n tm'
            Path.AnnL -> do
              (tm', mk) <- Path.matchP p tm
              mk <$> go abstract ps n tm'
            Path.LamArg -> Nothing
            Path.LamAnnArg -> Nothing
            Path.LamAnnType -> Nothing
            Path.AnnR -> Nothing
