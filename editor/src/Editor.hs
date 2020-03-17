{-# language GADTs #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
module Editor (EditorInit(..), EditorControls(..), Editor(..), editor) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.Class (lift)
import Data.Vector (Vector)
import Reflex

import Focus (Selection(..))
import qualified Focus
import Path (HasTargetInfo, Path, TargetInfo(..), targetInfo)
import qualified Path
import Syntax (Name, Term, Type)
import qualified Syntax

data AtPath f a where
  AtPath :: Path a b -> f b -> AtPath f a

data Option f b where
  Option :: f a b -> Option f b

data Choice f b where
  Choice :: a -> f a b -> Choice f b

data ChangeSelection a where
  SetSelection :: Selection a -> ChangeSelection a
  NextHole :: ChangeSelection a
  PrevHole :: ChangeSelection a

runChangeSelection :: ChangeSelection a -> Selection a -> a -> Maybe (Selection a)
runChangeSelection c sel code =
  case c of
    SetSelection sel' -> Just sel'
    NextHole -> case sel of; Selection path -> Focus.nextHole path code
    PrevHole -> case sel of; Selection path -> Focus.nextHole path code

data ChangeCode a b where
  InsertApp :: ChangeCode () (Term ty tm)
  InsertLam :: ChangeCode () (Term ty tm)
  InsertTArr :: ChangeCode () (Type ty)
  InsertTForall :: ChangeCode () (Type ty)
  Rename :: ChangeCode Name Name

runChangeCode :: AtPath (ChangeCode arg) a -> arg -> a -> Maybe (Selection a, a)
runChangeCode (AtPath p c) arg a =
  case c of
    InsertApp ->
      (,) (Selection $ Path.snoc p Path.AppL) <$>
      Path.set p (Syntax.App Syntax.Hole Syntax.Hole) a
    InsertLam ->
      (,) (Selection $ Path.snoc p Path.LamArg) <$>
      Path.set p (Syntax.Lam "x" $ lift Syntax.Hole) a
    InsertTArr ->
      (,) (Selection $ Path.snoc p Path.TArrL) <$>
      Path.set p (Syntax.TArr Syntax.THole Syntax.THole) a
    InsertTForall ->
      (,) (Selection $ Path.snoc p Path.TForallArg) <$>
      Path.set p (Syntax.TForall "x" $ lift Syntax.THole) a
    Rename ->
      (,) (Selection p) <$>
      Path.set p arg a

data EditorInit a
  = EditorInit
  { _eiCode :: a
  }

data Action a
  = ChangeSelection (ChangeSelection a)
  | ChangeCode (AtPath (Choice ChangeCode) a)

data EditorControls t a
  = EditorControls
  { _ecAction :: Event t (Action a)
  , _ecChangeCodeOptions :: Event t ()
  }

data Editor t a
  = Editor
  { _eCode :: Dynamic t a
  , _eSelection :: Dynamic t (Selection a)
  , _eChangeCodeOptions :: Event t (Vector (AtPath (Option ChangeCode) a))
  }

changeCodeOptions :: Selection a -> Vector (AtPath (Option ChangeCode) a)
changeCodeOptions (Selection (path :: Path a x)) =
  case targetInfo @x of
    TargetTerm ->
      [ AtPath path (Option InsertApp)
      , AtPath path (Option InsertLam)
      ]
    TargetType ->
      [ AtPath path (Option InsertTArr)
      , AtPath path (Option InsertTForall)
      ]
    TargetName ->
      [ AtPath path (Option Rename)
      ]
    TargetDeclBody -> []
    TargetDecl -> []
    TargetDecls -> []

editor ::
  forall t m a.
  (Reflex t, MonadHold t m, MonadFix m, HasTargetInfo a) =>
  EditorInit a ->
  EditorControls t a ->
  m (Editor t a)
editor initial controls = do
  let
    eAction :: Event t (Action a)
    eAction = _ecAction controls
  rec
    let
      eRunChange :: Event t (Maybe (Selection a), Maybe a)
      eRunChange =
        (\sel code change ->
          case change of
            ChangeSelection changeSel ->
              (runChangeSelection changeSel sel code, Nothing)
            ChangeCode (AtPath path (Choice arg changeCode)) ->
              let
                res = runChangeCode (AtPath path changeCode) arg code
              in
                ((\(a, _) -> a) <$> res, (\(_, a) -> a) <$> res)
        ) <$>
        current dSelection <*>
        current dCode <@>
        eAction

      eChangeCode :: Event t a
      eChangeCode = fmapMaybe (\(_, a) -> a) eRunChange

      eChangeSelection :: Event t (Selection a)
      eChangeSelection = fmapMaybe (\(a, _) -> a) eRunChange

    dSelection <- holdDyn (Selection Path.empty) eChangeSelection
    dCode <- holdDyn (_eiCode initial) eChangeCode

  pure $
    Editor
    { _eCode = dCode
    , _eSelection = dSelection
    , _eChangeCodeOptions =
        changeCodeOptions <$>
        current dSelection <@
        _ecChangeCodeOptions controls
    }

