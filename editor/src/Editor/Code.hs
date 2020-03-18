{-# language GADTs #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Editor.Code where

import qualified Bound
import qualified Data.Vector as Vector

import Path (HasTargetInfo, Path, TargetInfo(..), targetInfo)
import qualified Path
import Syntax (Name, Term, Type)
import qualified Syntax

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
  forall a ty' tm'.
  HasTargetInfo a =>
  Path a (Term ty' tm') ->
  Name ->
  a ->
  Maybe a
insertVar =
  case targetInfo @a of
    TargetName -> \_ _ _ -> Nothing
    TargetType -> goType Syntax.Name
    TargetTerm -> goTerm Syntax.Name
    TargetDecl -> goDecl
    TargetDecls -> goDecls
    TargetDeclBody -> goDeclBody Syntax.Name
  where
    goDecls ::
      Path Syntax.Decls (Term ty' tm') ->
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
      Path Syntax.Decl (Term ty' tm') ->
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
              mk <$> goDeclBody Syntax.Name ps n a'

    goType ::
      (forall x. Name -> Term x tm) ->
      Path (Type ty) (Term ty' tm') ->
      Name ->
      Type ty ->
      Maybe (Type ty)
    goType mkTm path n a =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.TForallArg -> Nothing
            Path.TForallBody -> do
              (ty', mk) <- Path.matchP Path.TForallBody a
              mk <$> goType mkTm ps n ty'
            Path.TUnsolvedBody -> do
              (ty', mk) <- Path.matchP Path.TUnsolvedBody a
              mk <$> goType mkTm ps n ty'
            Path.TArrL -> do
              (ty', mk) <- Path.matchP Path.TArrL a
              mk <$> goType mkTm ps n ty'
            Path.TArrR -> do
              (ty', mk) <- Path.matchP Path.TArrR a
              mk <$> goType mkTm ps n ty'
            Path.TSubstL -> do
              (ty', mk) <- Path.matchP Path.TSubstL a
              mk <$> goType mkTm ps n ty'
            Path.TSubstR ix -> do
              (ty', mk) <- Path.matchP (Path.TSubstR ix) a
              mk <$> goType mkTm ps n ty'

    goDeclBody ::
      (forall x. Name -> Term x tm) ->
      Path (Syntax.DeclBody ty tm) (Term ty' tm') ->
      Name ->
      Syntax.DeclBody ty tm ->
      Maybe (Syntax.DeclBody ty tm)
    goDeclBody mkTm path n a =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DBForallArg -> Nothing
            Path.DBForallBody -> do
              (tm', mk) <- Path.matchP Path.DBForallBody a
              mk <$> goDeclBody mkTm ps n tm'
            Path.DBTerm -> do
              (tm', mk) <- Path.matchP Path.DBTerm a
              mk <$> goTerm mkTm ps n tm'
            Path.DBType -> do
              (ty', mk) <- Path.matchP Path.DBType a
              mk <$> goType mkTm ps n ty'

    goTerm ::
      (forall x. Name -> Term x tm) ->
      Path (Syntax.Term ty tm) (Term ty' tm') ->
      Name ->
      Syntax.Term ty tm ->
      Maybe (Syntax.Term ty tm)
    goTerm mkTm path n tm =
      case Path.viewl path of
        Path.EmptyL -> Just $ mkTm n
        p Path.:< ps ->
          case p of
            Path.AppL -> do
              (tm', mk) <- Path.matchP Path.AppL tm
              mk <$> goTerm mkTm ps n tm'
            Path.AppR -> do
              (tm', mk) <- Path.matchP Path.AppR tm
              mk <$> goTerm mkTm ps n tm'
            Path.LamArg -> Nothing
            Path.LamBody -> do
              case tm of
                Syntax.Lam n' body ->
                  Syntax.Lam n' . Bound.toScope <$>
                  goTerm
                    (\x ->
                       if x == n'
                       then Syntax.Var (Bound.B ())
                       else Bound.F <$> mkTm x
                    )
                    ps
                    n
                    (Bound.fromScope body)
                _ -> Nothing
            Path.LamAnnArg -> Nothing
            Path.LamAnnType -> do
              (ty, mk) <- Path.matchP Path.LamAnnType tm
              mk <$> goType mkTm ps n ty
            Path.LamAnnBody -> do
              case tm of
                Syntax.LamAnn n' ty body ->
                  Syntax.LamAnn n' ty . Bound.toScope <$>
                  goTerm
                    (\x ->
                       if x == n'
                       then Syntax.Var (Bound.B ())
                       else Bound.F <$> mkTm x
                    )
                    ps
                    n
                    (Bound.fromScope body)
                _ -> Nothing
            Path.AnnL -> do
              (tm', mk) <- Path.matchP Path.AnnL tm
              mk <$> goTerm mkTm ps n tm'
            Path.AnnR -> do
              (ty, mk) <- Path.matchP Path.AnnR tm
              mk <$> goType mkTm ps n ty
