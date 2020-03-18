{-# language GADTs #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Editor.Code where

import qualified Bound
import qualified Data.Vector as Vector

import Path (KnownTarget, Path, Target(..), target)
import qualified Path
import Syntax (Name, Term, Type)
import qualified Syntax
import Zipper (Zipper)
import qualified Zipper

insertTVar ::
  forall a ty'.
  KnownTarget a =>
  Path a (Type ty') ->
  Name ->
  a ->
  Maybe a
insertTVar path_ n_ a_ =
  let z = Zipper.toZipper a_ in
  case Zipper._target z of
    TargetName -> Nothing
    TargetType -> goType Syntax.TName path_ n_ z
    TargetTerm -> goTerm Syntax.TName path_ n_ z
    TargetDecl -> goDecl path_ n_ z
    TargetDecls -> goDecls path_ n_ z
    TargetDeclBody -> goDeclBody Syntax.TName path_ n_ z
  where
    goDecls ::
      Path Syntax.Decls (Type ty') ->
      Name ->
      Zipper a Syntax.Decls ->
      Maybe a
    goDecls path n z =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.Decl ix -> goDecl ps n =<< Zipper.down (Path.Decl ix) z

    goDecl ::
      Path Syntax.Decl (Type ty') ->
      Name ->
      Zipper a Syntax.Decl ->
      Maybe a
    goDecl path n z =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DName -> Nothing
            Path.DBody -> goDeclBody Syntax.TName ps n =<< Zipper.down Path.DBody z

    goType ::
      (Name -> Type ty) ->
      Path (Type ty) (Type ty') ->
      Name ->
      Zipper a (Type ty) ->
      Maybe a
    goType mkTy path n z =
      case Path.viewl path of
        Path.EmptyL -> Just . Zipper.fromZipper $ Zipper.mapFocus (\_ -> mkTy n) z
        p Path.:< ps ->
          case p of
            Path.TForallArg -> Nothing
            Path.TForallBody ->
              case Zipper._focus z of
                Syntax.TForall n' _ ->
                  goType
                    (\x ->
                       if x == n'
                       then Syntax.TVar (Bound.B ())
                       else Bound.F <$> mkTy x
                    )
                    ps
                    n =<<
                  Zipper.down Path.TForallBody z
                _ -> Nothing
            Path.TUnsolvedBody ->
              case Zipper._focus z of
                Syntax.TUnsolved ns _ ->
                  goType
                    (\x ->
                       maybe
                         (Syntax.TName x)
                         (Syntax.TVar . Bound.B)
                         (Vector.findIndex ((x ==) . fst) ns)
                    )
                    ps
                    n =<<
                  Zipper.down Path.TUnsolvedBody z
                _ -> Nothing
            Path.TArrL -> goType mkTy ps n =<< Zipper.down Path.TArrL z
            Path.TArrR -> goType mkTy ps n =<< Zipper.down Path.TArrR z
            Path.TSubstL -> goType mkTy ps n =<< Zipper.down Path.TSubstL z
            Path.TSubstR ix -> goType mkTy ps n =<< Zipper.down (Path.TSubstR ix) z

    goDeclBody ::
      (Name -> Type ty) ->
      Path (Syntax.DeclBody ty tm) (Type ty') ->
      Name ->
      Zipper a (Syntax.DeclBody ty tm) ->
      Maybe a
    goDeclBody mkTy path n z =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.DBForallArg -> Nothing
            Path.DBForallBody ->
              case Zipper._focus z of
                Syntax.Forall n' _ ->
                  goDeclBody
                    (\x ->
                       if x == n'
                       then Syntax.TVar (Bound.B ())
                       else Bound.F <$> mkTy x
                    )
                    ps
                    n =<<
                  Zipper.down Path.DBForallBody z
                _ -> Nothing
            Path.DBTerm -> goTerm mkTy ps n =<< Zipper.down Path.DBTerm z
            Path.DBType -> goType mkTy ps n =<< Zipper.down Path.DBType z

    goTerm ::
      (Name -> Type ty) ->
      Path (Syntax.Term ty tm) (Type ty') ->
      Name ->
      Zipper a (Syntax.Term ty tm) ->
      Maybe a
    goTerm mkTy path n tm =
      case Path.viewl path of
        p Path.:< ps ->
          case p of
            Path.AppL -> goTerm mkTy ps n =<< Zipper.down Path.AppL tm
            Path.AppR -> goTerm mkTy ps n =<< Zipper.down Path.AppR tm
            Path.LamArg -> Nothing
            Path.LamBody -> goTerm mkTy ps n =<< Zipper.down Path.LamBody tm
            Path.LamAnnArg -> Nothing
            Path.LamAnnType -> goType mkTy ps n =<< Zipper.down Path.LamAnnType tm
            Path.LamAnnBody -> goTerm mkTy ps n =<< Zipper.down Path.LamAnnBody tm
            Path.AnnL -> goTerm mkTy ps n =<< Zipper.down Path.AnnL tm
            Path.AnnR -> goType mkTy ps n =<< Zipper.down Path.AnnR tm

insertVar ::
  forall a ty' tm'.
  KnownTarget a =>
  Path a (Term ty' tm') ->
  Name ->
  a ->
  Maybe a
insertVar =
  case target @a of
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
              (_, a', mk) <- Path.matchP (Path.Decl ix) ds
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
              (_, a', mk) <- Path.matchP Path.DBody d
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
              (_, ty', mk) <- Path.matchP Path.TForallBody a
              mk <$> goType mkTm ps n ty'
            Path.TUnsolvedBody -> do
              (_, ty', mk) <- Path.matchP Path.TUnsolvedBody a
              mk <$> goType mkTm ps n ty'
            Path.TArrL -> do
              (_, ty', mk) <- Path.matchP Path.TArrL a
              mk <$> goType mkTm ps n ty'
            Path.TArrR -> do
              (_, ty', mk) <- Path.matchP Path.TArrR a
              mk <$> goType mkTm ps n ty'
            Path.TSubstL -> do
              (_, ty', mk) <- Path.matchP Path.TSubstL a
              mk <$> goType mkTm ps n ty'
            Path.TSubstR ix -> do
              (_, ty', mk) <- Path.matchP (Path.TSubstR ix) a
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
              (_, tm', mk) <- Path.matchP Path.DBForallBody a
              mk <$> goDeclBody mkTm ps n tm'
            Path.DBTerm -> do
              (_, tm', mk) <- Path.matchP Path.DBTerm a
              mk <$> goTerm mkTm ps n tm'
            Path.DBType -> do
              (_, ty', mk) <- Path.matchP Path.DBType a
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
              (_, tm', mk) <- Path.matchP Path.AppL tm
              mk <$> goTerm mkTm ps n tm'
            Path.AppR -> do
              (_, tm', mk) <- Path.matchP Path.AppR tm
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
              (_, ty, mk) <- Path.matchP Path.LamAnnType tm
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
              (_, tm', mk) <- Path.matchP Path.AnnL tm
              mk <$> goTerm mkTm ps n tm'
            Path.AnnR -> do
              (_, ty, mk) <- Path.matchP Path.AnnR tm
              mk <$> goType mkTm ps n ty
