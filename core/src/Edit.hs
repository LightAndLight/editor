{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables, TypeApplications #-}
module Edit where

import qualified Bound
import Bound.Var (unvar)
import Control.Monad.Trans (lift)
import Data.Bifunctor (first)
import qualified Data.Vector as Vector

import Syntax (Name, Term, Type)
import qualified Syntax
import Path (Path, Target(..), KnownTarget, target)
import qualified Path
import qualified Zipper

data Action a b where
  InsertTerm :: Term ty a -> Path (Term ty a) b -> Action (Term ty a) b
  ModifyTerm ::
    (Term ty a -> Term ty a) ->
    Path (Term ty a) b ->
    Action (Term ty a) b
  DeleteTerm :: Action (Term ty a) (Term ty a)

  InsertType :: Type a -> Path (Type a) b -> Action (Type a) b
  InsertTForall :: Name -> Action (Type a) Name
  InsertTVar :: Name -> Action (Type ty) (Type ty)
  DeleteType :: Action (Type a) (Type a)

  ModifyName :: (Name -> Name) -> Action Name Name
  DeleteName :: Action Name Name

data EditError where
  InvalidPath :: Path a b -> a -> EditError
  Can'tDeleteName :: Path a Name -> a -> EditError

instance Show EditError where
  show (InvalidPath p _) = "InvalidPath: " <> show p
  show (Can'tDeleteName p _) = "Can'tDeleteName: " <> show p

edit ::
  forall src tgt tgt'.
  (KnownTarget src, KnownTarget tgt') =>
  Path src tgt ->
  Target tgt ->
  Action tgt tgt' ->
  src ->
  Either EditError (Path src tgt', Target tgt', src)
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
        Just a' -> Right (Path.append path suffix, target @tgt', a')
    ModifyTerm f suffix ->
      case Path.modify path f a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (Path.append path suffix, target @tgt', a')
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
    DeleteName ->
      case Path.viewr path of
        Path.EmptyR -> Left $ Can'tDeleteName path a
        ps Path.:> p ->
          case p of
            Path.LamArg -> Left $ Can'tDeleteName path a
            Path.LamAnnArg -> Left $ Can'tDeleteName path a
            Path.TForallArg -> Left $ Can'tDeleteName path a
            Path.DName -> Left $ Can'tDeleteName path a
            Path.DBForallArg ->
              case Path.viewr ps of
                ps' Path.:> Path.DBForallBody -> do
                  z <- maybe (Left $ InvalidPath path a) pure (Zipper.downTo ps $ Zipper.toZipper a)
                  z' <-
                    Zipper.traverseFocus
                      (\case
                          Syntax.Forall n body ->
                            pure $ Syntax.bindDeclBodyTy (unvar (\() -> Syntax.TName n) pure) body
                          _ -> Left $ InvalidPath path a
                      )
                    z
                  pure
                    ( Path.snoc ps' Path.DBForallArg
                    , TargetName
                    , Zipper.fromZipper z'
                    )
                _ -> Left $ Can'tDeleteName path a
edit path TargetType action a =
  case action of
    InsertType ty suffix ->
      case Path.set path ty a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (Path.append path suffix, target @tgt', a')
    InsertTForall name ->
      case insertTForall path name a of
        Nothing -> Left $ InvalidPath path a
        Just (path', a') -> Right (path', target @tgt', a')
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
  KnownTarget a =>
  Path a (Type ty') ->
  Name ->
  a ->
  Maybe (Path a Name, a)
insertTForall =
  case target @a of
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
                  (_, a', mk) <- Path.matchP Path.DBType a
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
              (_, a', mk) <- Path.matchP Path.DBTerm a
              (path', a'') <- insertTForall_Term ps n a'
              pure (Path.cons Path.DBTerm path', mk a'')
            Path.DBForallArg -> Nothing
            Path.DBForallBody -> do
              (_, a', mk) <- Path.matchP Path.DBForallBody a
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
              (_, a', mk) <- Path.matchP Path.DBody a
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
              (_, a', mk) <- Path.matchP (Path.Decl ix) a
              (path', a'') <- insertTForall_Decl ps n a'
              pure (Path.cons (Path.Decl ix) path', mk a'')

insertTVar ::
  forall a ty'.
  KnownTarget a =>
  Path a (Type ty') ->
  Name ->
  a ->
  Maybe a
insertTVar =
  case target @a of
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
              (_, a', mk) <- Path.matchP (Path.Decl ix) ds
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
              (_, a', mk) <- Path.matchP Path.DBody d
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
              (_, ty', mk) <- Path.matchP Path.TArrL a
              mk <$> goType mkTy ps n ty'
            Path.TArrR -> do
              (_, ty', mk) <- Path.matchP Path.TArrR a
              mk <$> goType mkTy ps n ty'
            Path.TSubstL -> do
              (_, ty', mk) <- Path.matchP Path.TSubstL a
              mk <$> goType mkTy ps n ty'
            Path.TSubstR ix -> do
              (_, ty', mk) <- Path.matchP (Path.TSubstR ix) a
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
              (_, tm', mk) <- Path.matchP Path.DBTerm a
              mk <$> goTerm mkTy ps n tm'
            Path.DBType -> do
              (_, ty', mk) <- Path.matchP Path.DBType a
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
              (_, tm', mk) <- Path.matchP Path.AppL tm
              mk <$> goTerm mkTy ps n tm'
            Path.AppR -> do
              (_, tm', mk) <- Path.matchP Path.AppR tm
              mk <$> goTerm mkTy ps n tm'
            Path.LamArg -> Nothing
            Path.LamBody -> do
              (_, tm', mk) <- Path.matchP Path.LamBody tm
              mk <$> goTerm mkTy ps n tm'
            Path.LamAnnArg -> Nothing
            Path.LamAnnType -> do
              (_, ty, mk) <- Path.matchP Path.LamAnnType tm
              mk <$> goType mkTy ps n ty
            Path.LamAnnBody -> do
              (_, tm', mk) <- Path.matchP Path.LamAnnBody tm
              mk <$> goTerm mkTy ps n tm'
            Path.AnnL -> do
              (_, tm', mk) <- Path.matchP Path.AnnL tm
              mk <$> goTerm mkTy ps n tm'
            Path.AnnR -> do
              (_, ty, mk) <- Path.matchP Path.AnnR tm
              mk <$> goType mkTy ps n ty
