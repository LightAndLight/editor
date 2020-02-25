{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
module Edit where

import Data.Text (Text)

import Syntax (Term, Type)
import qualified Syntax
import Path (Path(..), TargetInfo(..))
import qualified Path

data Action a b where
  InsertTerm :: Term a -> Path (Term a) b -> Action (Term a) b
  DeleteTerm :: Action (Term a) (Term a)
  ModifyIdent :: (Text -> Text) -> Action Text Text
  InsertType :: Type a -> Path (Type a) b -> Action (Type a) b
  DeleteType :: Action (Type a) (Type a)

data EditError where
  InvalidPath :: Path a b -> a -> EditError
  InsertNonHole :: Path a b -> b -> EditError

edit ::
  forall src tgt tgt'.
  Path src tgt ->
  Action tgt tgt' ->
  src ->
  Either EditError (Path src tgt', src)
edit p@(Path path TargetTerm) action a =
  -- path : Path a (Term x)
  -- action : Edit (Term x) c
  let
    replaceHoleWith :: tgt -> tgt -> Either EditError tgt
    replaceHoleWith new old =
      case old of
        Syntax.Hole -> Right new
        b -> Left $ InsertNonHole p b
  in
  case action of
    InsertTerm tm suffix ->
      case Path.modifyA path (replaceHoleWith tm) a of
        Left err -> Left err
        Right Nothing -> Left $ InvalidPath p a
        Right (Just a') -> Right (Path.append p suffix, a')
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
edit p@(Path path TargetType) action a =
  let
    replaceHoleWith :: tgt -> tgt -> Either EditError tgt
    replaceHoleWith new old =
      case old of
        Syntax.THole -> Right new
        b -> Left $ InsertNonHole p b
  in
  case action of
    InsertType ty suffix ->
      case Path.modifyA path (replaceHoleWith ty) a of
        Left err -> Left err
        Right Nothing -> Left $ InvalidPath p a
        Right (Just a') -> Right (Path.append p suffix, a')
    DeleteType ->
      case Path.set path Syntax.THole a of
        Nothing -> Left $ InvalidPath p a
        Just a' -> Right (p, a')
