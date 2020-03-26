{-# language GADTs #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# options_ghc -fno-warn-overlapping-patterns #-}
module Editor
  ( EditorInit(..), EditorControls(..), Editor(..), editor
  , Action(..)
  , AtPath(..)
  , Option(..)
  , Choice(..)
  , ChangeCode(..)
  , ChangeSelection(..)
  )
where

import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (first)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum ((==>))
import Data.GADT.Compare (GEq(..), GCompare(..), (:~:)(..), GOrdering(..))
import Data.Maybe as Maybe
import Data.Vector (Vector)
import Reflex

import qualified Editor.Code
import Editor.Selection (Selection(..))
import qualified Editor.Selection
import Path (KnownTarget, Path, Target(..), target)
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
    NextHole -> case sel of; Selection path -> Editor.Selection.nextHole path code
    PrevHole -> case sel of; Selection path -> Editor.Selection.prevHole path code

data ChangeCode a b where
  InsertVar :: ChangeCode Name (Term ty tm)
  InsertApp :: ChangeCode () (Term ty tm)
  InsertLam :: ChangeCode () (Term ty tm)
  InsertTVar :: ChangeCode Name (Type ty)
  InsertTArr :: ChangeCode () (Type ty)
  InsertTForall :: ChangeCode () (Type ty)
  Rename :: ChangeCode Name Name

runChangeCode ::
  KnownTarget a =>
  AtPath (ChangeCode arg) a ->
  arg ->
  a ->
  Maybe (Selection a, a)
runChangeCode (AtPath p c) arg a =
  case c of
    InsertVar ->
      (,) (Maybe.fromMaybe (Selection p) $ Editor.Selection.nextHole p a) <$>
      Editor.Code.insertVar p arg a
    InsertApp ->
      (,) (Selection $ Path.snoc p Path.AppL) <$>
      Path.set p (Syntax.App Syntax.Hole Syntax.Hole) a
    InsertLam ->
      (,) (Selection $ Path.snoc p Path.LamArg) <$>
      Path.set p (Syntax.Lam "x" $ lift Syntax.Hole) a
    InsertTVar ->
      (,) (Maybe.fromMaybe (Selection p) $ Editor.Selection.nextHole p a) <$>
      Editor.Code.insertTVar p arg a
    InsertTArr ->
      (,) (Selection $ Path.snoc p Path.TArrL) <$>
      Path.set p (Syntax.TArr Syntax.THole Syntax.THole) a
    InsertTForall ->
      first Selection <$> Editor.Code.insertTForall p "x" a
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

data KUpdate a b where
  KSelection :: KUpdate a (Selection a)
  KCode :: KUpdate a a
instance GEq (KUpdate a) where
  geq KSelection a =
    case a of
      KSelection -> Just Refl
      _ -> Nothing
  geq KCode a =
    case a of
      KCode -> Just Refl
      _ -> Nothing
instance GCompare (KUpdate a) where
  gcompare KSelection KSelection = GEQ
  gcompare KSelection _ = GLT
  gcompare _ KSelection = GGT

  gcompare KCode KCode = GEQ
  gcompare KCode _ = GLT
  gcompare _ KCode = GGT


data EditorControls t a
  = EditorControls
  { _ecAction :: Event t (Action a)
  }

data Editor t a
  = Editor
  { _eCode :: Dynamic t a
  , _eSelection :: Dynamic t (Selection a)
  , _eChangeCodeOptions :: Dynamic t (Vector (AtPath (Option ChangeCode) a))
  }

changeCodeOptions :: Selection a -> Vector (AtPath (Option ChangeCode) a)
changeCodeOptions (Selection (path :: Path a x)) =
  case target @x of
    TargetTerm ->
      [ AtPath path (Option InsertVar)
      , AtPath path (Option InsertApp)
      , AtPath path (Option InsertLam)
      ]
    TargetType ->
      [ AtPath path (Option InsertTVar)
      , AtPath path (Option InsertTArr)
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
  (Reflex t, MonadHold t m, MonadFix m, KnownTarget a) =>
  EditorInit a ->
  EditorControls t a ->
  m (Editor t a)
editor initial controls = do
  let
    eAction :: Event t (Action a)
    eAction = _ecAction controls
  rec
    let
      update :: EventSelector t (KUpdate a)
      update =
        fan $
        (\sel code change ->
          case change of
            ChangeSelection changeSel ->
              case runChangeSelection changeSel sel code of
                Nothing -> mempty
                Just sel' ->
                  DMap.fromList
                  [ KSelection ==> sel'
                  ]
            ChangeCode (AtPath path (Choice arg changeCode)) ->
              case runChangeCode (AtPath path changeCode) arg code of
                Nothing -> mempty
                Just (sel', code') ->
                  DMap.fromList
                  [ KSelection ==> sel'
                  , KCode ==> code'
                  ]
        ) <$>
        current dSelection <*>
        current dCode <@>
        eAction

      eUpdateCode :: Event t a
      eUpdateCode = select update KCode

      eUpdateSelection :: Event t (Selection a)
      eUpdateSelection = select update KSelection

    dSelection <- holdDyn (Selection Path.empty) eUpdateSelection
    dCode <- holdDyn (_eiCode initial) eUpdateCode

  pure $
    Editor
    { _eCode = dCode
    , _eSelection = dSelection
    , _eChangeCodeOptions = changeCodeOptions <$> dSelection
    }

