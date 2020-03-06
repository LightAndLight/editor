{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
module Edit where

import Data.Type.Equality ((:~:)(..))

import Syntax (Name, Term, Type)
import qualified Syntax
import Path (Path, TargetInfo(..), targetInfo)
import qualified Path

data Action a b where
  InsertTerm :: Term ty a -> Path (Term ty a) b -> Action (Term ty a) b
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
  Path src tgt ->
  TargetInfo tgt ->
  Action tgt tgt' ->
  src ->
  Either EditError (Path src tgt', TargetInfo tgt', src)
edit path TargetTerm action a =
  -- path : Path a (Term x)
  -- action : Edit (Term x) c
  case action of
    InsertTerm tm suffix ->
      case Path.set path tm a of
        Nothing -> Left $ InvalidPath path a
        Just a' ->
          case targetInfo suffix of
            Left Refl -> Right (Path.append path suffix, TargetTerm, a')
            Right info -> Right (Path.append path suffix, info, a')
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
        Just a' ->
          case targetInfo suffix of
            Left Refl -> Right (Path.append path suffix, TargetType, a')
            Right info -> Right (Path.append path suffix, info, a')
    DeleteType ->
      case Path.set path Syntax.THole a of
        Nothing -> Left $ InvalidPath path a
        Just a' -> Right (path, TargetType, a')
