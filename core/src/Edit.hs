{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables, TypeApplications #-}
module Edit where

import qualified Bound
import Control.Monad.Trans (lift)
import Data.Bifunctor (first)
import qualified Data.Vector as Vector

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
  InsertTForall :: Name -> Action (Type a) Name
  InsertTVar :: Name -> Action (Type ty) (Type ty)
  DeleteType :: Action (Type a) (Type a)

data EditError where
  InvalidPath :: Path a b -> a -> EditError

instance Show EditError where
  show (InvalidPath p _) = "InvalidPath: " <> show p

edit ::
  forall src tgt tgt'.
  (HasTargetInfo src, HasTargetInfo tgt') =>
  Path src tgt ->
  TargetInfo tgt ->
  Action tgt tgt' ->
  src ->
  Either EditError (Path src tgt', TargetInfo tgt', src)
edit _ TargetDecls action _ = case action of
edit _ TargetDecl action _ = case action of
edit _ TargetDeclBody action _ = case action of
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
            Just a'' -> Right (path, TargetTerm, a'')
        TargetType -> Left $ InvalidPath path a
        TargetName -> Left $ InvalidPath path a
        TargetDecls ->
          case Path.viewl path of
            Path.Decl ix Path.:< ps ->
              case a of
                Syntax.Decls ds -> do
                  (ps', ti', d') <- edit ps TargetTerm action (ds Vector.! ix)
                  pure
                    ( Path.cons (Path.Decl ix) ps'
                    , ti'
                    , Syntax.Decls $ ds Vector.// [(ix, d')]
                    )
        TargetDecl ->
          case Path.viewl path of
            Path.DBody Path.:< ps ->
              case a of
                Syntax.Decl name body -> do
                  (ps', ti', tm') <- edit ps TargetTerm action body
                  pure
                    ( Path.cons Path.DBody ps'
                    , ti'
                    , Syntax.Decl name tm'
                    )
            _ -> Left $ InvalidPath path a
        TargetDeclBody ->
          case Path.viewl path of
            Path.DBTerm Path.:< ps ->
              case a of
                Syntax.Done ty tm -> do
                  (ps', ti', tm') <- edit ps TargetTerm action tm
                  pure
                    ( Path.cons Path.DBTerm ps'
                    , ti'
                    , Syntax.Done ty tm'
                    )
                _ -> Left $ InvalidPath path a
            Path.DBForallBody Path.:< ps ->
              case a of
                Syntax.Forall name body -> do
                  (ps', ti', body') <- edit ps TargetTerm action body
                  pure
                    ( Path.cons Path.DBForallBody ps'
                    , ti'
                    , Syntax.Forall name body'
                    )
                _ -> Left $ InvalidPath path a
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
    InsertTForall name ->
      case insertTForall path name a of
        Nothing -> Left $ InvalidPath path a
        Just (path', a') -> Right (path', targetInfo @tgt', a')
    InsertTVar name ->
      case insertTVar path name a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (path, TargetType, a')
    DeleteType ->
      case Path.set path Syntax.THole a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (path, TargetType, a')

insertTForall ::
  forall a ty'.
  HasTargetInfo a =>
  Path a (Type ty') ->
  Name ->
  a ->
  Maybe (Path a Name, a)
insertTForall =
  case targetInfo @a of
    TargetTerm -> insertTForall_Term
    TargetType -> insertTForall_Type
    TargetDeclBody -> insertTForall_DeclBody
    TargetDecl -> insertTForall_Decl
    TargetDecls -> insertTForall_Decls
    TargetName -> \_ _ _ -> Nothing
  where
    insertTForall_Type ::
      Path (Type ty) (Type ty') ->
      Name ->
      Type ty ->
      Maybe (Path (Type ty) Name, Type ty)
    insertTForall_Type path n a =
      (,) (Path.snoc path Path.TForallArg) <$>
      Path.set path (Syntax.TForall n $ lift Syntax.THole) a

    insertTForall_Term ::
      Path (Term ty tm) (Type ty') ->
      Name ->
      Term ty tm ->
      Maybe (Path (Term ty tm) Name, Term ty tm)
    insertTForall_Term path n a =
      (,) (Path.snoc path Path.TForallArg) <$>
      Path.set path (Syntax.TForall n $ lift Syntax.THole) a

    insertTForall_DeclBody ::
      Path (Syntax.DeclBody ty tm) (Type ty') ->
      Name ->
      Syntax.DeclBody ty tm ->
      Maybe (Path (Syntax.DeclBody ty tm) Name, Syntax.DeclBody ty tm)
    insertTForall_DeclBody path n a =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DBType ->
              case Path.viewl ps of
                _ Path.:< _ -> do
                  (a', mk) <- Path.matchP Path.DBType a
                  (path', a'') <- insertTForall_Type ps n a'
                  pure (Path.cons Path.DBType path', mk a'')
                Path.EmptyL ->
                  case a of
                    Syntax.Done _ tm ->
                      pure
                        ( Path.singleton Path.DBForallArg
                        , Syntax.Forall n $ Syntax.Done Syntax.THole (first Bound.F tm)
                        )
                    _ -> Nothing
            Path.DBTerm -> do
              (a', mk) <- Path.matchP Path.DBTerm a
              (path', a'') <- insertTForall_Term ps n a'
              pure (Path.cons Path.DBTerm path', mk a'')
            Path.DBForallArg -> Nothing
            Path.DBForallBody -> do
              (a', mk) <- Path.matchP Path.DBForallBody a
              (path', a'') <- insertTForall_DeclBody ps n a'
              pure (Path.cons Path.DBForallBody path', mk a'')

    insertTForall_Decl ::
      Path Syntax.Decl (Type ty') ->
      Name ->
      Syntax.Decl ->
      Maybe (Path Syntax.Decl Name, Syntax.Decl)
    insertTForall_Decl path n a =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DBody -> do
              (a', mk) <- Path.matchP Path.DBody a
              (path', a'') <- insertTForall_DeclBody ps n a'
              pure (Path.cons Path.DBody path', mk a'')
            Path.DName -> Nothing

    insertTForall_Decls ::
      Path Syntax.Decls (Type ty') ->
      Name ->
      Syntax.Decls ->
      Maybe (Path Syntax.Decls Name, Syntax.Decls)
    insertTForall_Decls path n a =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.Decl ix -> do
              (a', mk) <- Path.matchP (Path.Decl ix) a
              (path', a'') <- insertTForall_Decl ps n a'
              pure (Path.cons (Path.Decl ix) path', mk a'')

insertTVar ::
  forall a ty'.
  HasTargetInfo a =>
  Path a (Type ty') ->
  Name ->
  a ->
  Maybe a
insertTVar =
  case targetInfo @a of
    TargetName -> \_ _ _ -> Nothing
    TargetType -> goType Syntax.TName
    TargetTerm -> goTerm Syntax.TName
    TargetDecl -> goDecl
    TargetDecls -> goDecls
    TargetDeclBody -> goDeclBody Syntax.TName
  where
    goDecls ::
      Path Syntax.Decls (Type ty') ->
      Name ->
      Syntax.Decls ->
      Maybe Syntax.Decls
    goDecls path n ds =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.Decl ix -> do
              (a', mk) <- Path.matchP (Path.Decl ix) ds
              mk <$> goDecl ps n a'

    goDecl ::
      Path Syntax.Decl (Type ty') ->
      Name ->
      Syntax.Decl ->
      Maybe Syntax.Decl
    goDecl path n d =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DName -> Nothing
            Path.DBody -> do
              (a', mk) <- Path.matchP Path.DBody d
              mk <$> goDeclBody Syntax.TName ps n a'

    goType ::
      (Name -> Type ty) ->
      Path (Type ty) (Type ty') ->
      Name ->
      Type ty ->
      Maybe (Type ty)
    goType mkTy path n a =
      case Path.viewl path of
        Path.EmptyL -> Just $ mkTy n
        p Path.:< ps ->
          case p of
            Path.TForallArg -> Nothing
            Path.TForallBody ->
              case a of
                Syntax.TForall n' body ->
                  Syntax.TForall n' . Bound.toScope <$>
                  goType
                    (\x ->
                       if x == n'
                       then Syntax.TVar (Bound.B ())
                       else Bound.F <$> mkTy x
                    )
                    ps
                    n
                    (Bound.fromScope body)
                _ -> Nothing
            Path.TUnsolvedBody ->
              case a of
                Syntax.TUnsolved ns body ->
                  Syntax.TUnsolved ns . Bound.toScope <$>
                  goType
                    (\x ->
                       maybe
                         (Syntax.TName x)
                         (Syntax.TVar . Bound.B)
                         (Vector.findIndex ((x ==) . fst) ns)
                    )
                    ps
                    n
                    (Bound.fromScope body)
                _ -> Nothing
            Path.TArrL -> do
              (ty', mk) <- Path.matchP Path.TArrL a
              mk <$> goType mkTy ps n ty'
            Path.TArrR -> do
              (ty', mk) <- Path.matchP Path.TArrR a
              mk <$> goType mkTy ps n ty'
            Path.TSubstL -> do
              (ty', mk) <- Path.matchP Path.TSubstL a
              mk <$> goType mkTy ps n ty'
            Path.TSubstR ix -> do
              (ty', mk) <- Path.matchP (Path.TSubstR ix) a
              mk <$> goType mkTy ps n ty'

    goDeclBody ::
      (Name -> Type ty) ->
      Path (Syntax.DeclBody ty tm) (Type ty') ->
      Name ->
      Syntax.DeclBody ty tm ->
      Maybe (Syntax.DeclBody ty tm)
    goDeclBody mkTy path n a =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DBForallArg -> Nothing
            Path.DBForallBody ->
              case a of
                Syntax.Forall n' body ->
                  Syntax.Forall n' <$>
                  goDeclBody
                    (\x ->
                       if x == n'
                       then Syntax.TVar (Bound.B ())
                       else Bound.F <$> mkTy x
                    )
                    ps
                    n
                    body
                _ -> Nothing
            Path.DBTerm -> do
              (tm', mk) <- Path.matchP Path.DBTerm a
              mk <$> goTerm mkTy ps n tm'
            Path.DBType -> do
              (ty', mk) <- Path.matchP Path.DBType a
              mk <$> goType mkTy ps n ty'

    goTerm ::
      (Name -> Type ty) ->
      Path (Syntax.Term ty tm) (Type ty') ->
      Name ->
      Syntax.Term ty tm ->
      Maybe (Syntax.Term ty tm)
    goTerm mkTy path n tm =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.AppL -> do
              (tm', mk) <- Path.matchP Path.AppL tm
              mk <$> goTerm mkTy ps n tm'
            Path.AppR -> do
              (tm', mk) <- Path.matchP Path.AppR tm
              mk <$> goTerm mkTy ps n tm'
            Path.LamArg -> Nothing
            Path.LamBody -> do
              (tm', mk) <- Path.matchP Path.LamBody tm
              mk <$> goTerm mkTy ps n tm'
            Path.LamAnnArg -> Nothing
            Path.LamAnnType -> do
              (ty, mk) <- Path.matchP Path.LamAnnType tm
              mk <$> goType mkTy ps n ty
            Path.LamAnnBody -> do
              (tm', mk) <- Path.matchP Path.LamAnnBody tm
              mk <$> goTerm mkTy ps n tm'
            Path.AnnL -> do
              (tm', mk) <- Path.matchP Path.AnnL tm
              mk <$> goTerm mkTy ps n tm'
            Path.AnnR -> do
              (ty, mk) <- Path.matchP Path.AnnR tm
              mk <$> goType mkTy ps n ty

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
