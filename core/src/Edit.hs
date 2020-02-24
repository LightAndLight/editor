{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
module Edit where

import Data.Text (Text)

import Syntax (Term)
import qualified Syntax
import Path (Path(..), TargetInfo(..))
import qualified Path

data Action a b where
  InsertApp :: Action (Term a) (Term a)
  InsertLam :: Action (Term a) Text
  ModifyIdent :: (Text -> Text) -> Action Text Text
  DeleteTerm :: Action (Term a) (Term a)

data EditError where
  InvalidPath :: Path a b -> a -> EditError
  InsertNonHole :: Path a b -> b -> EditError

edit :: forall a b c. Path a b -> Action b c -> a -> Either EditError (Path a c, a)
edit p@(Path path TargetTerm) action a =
  -- path : Path a (Term x)
  -- action : Edit (Term x) c
  let
    replaceHoleWith :: b -> b -> Either EditError b
    replaceHoleWith new old =
      case old of
        Syntax.Hole -> Right new
        b -> Left $ InsertNonHole p b
  in
  case action of
    InsertApp ->
      case Path.modifyA path (replaceHoleWith $ Syntax.App Syntax.Hole Syntax.Hole) a of
        Left err -> Left err
        Right Nothing -> Left $ InvalidPath p a
        Right (Just a') -> Right (Path (Path.snoc path Path.AppL) TargetTerm, a')
    InsertLam ->
      case Path.modifyA path (replaceHoleWith $ Syntax._Lam mempty Syntax.Hole) a of
        Left err -> Left err
        Right Nothing -> Left $ InvalidPath p a
        Right (Just a') -> Right (Path (Path.snoc path Path.LamArg) TargetIdent, a')
    DeleteTerm ->
      case Path.set path Syntax.Hole a of
        Nothing -> Left $ InvalidPath p a
        Just a' -> Right (p, a')
edit p@(Path path TargetIdent) action a =
  -- path : Path a Text
  -- action : Edit Text c
  case action of
    ModifyIdent f ->
      case Path.modify path f a of
        Nothing -> Left $ InvalidPath p a
        Just a' -> Right (p, a')
