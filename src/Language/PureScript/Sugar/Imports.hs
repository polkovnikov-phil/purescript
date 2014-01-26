-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.Sugar.Imports
-- Copyright   :  (c) Phil Freeman 2013
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Language.PureScript.Sugar.Imports (
    qualifyAll
) where

import Data.Maybe (mapMaybe)
import Data.Monoid (mconcat)
import Data.Either (lefts, rights)
import Data.List (find)
import Data.Generics

import Control.Monad.State
import Control.Applicative

import Language.PureScript.Values
import Language.PureScript.Types
import Language.PureScript.Declarations
import Language.PureScript.Names

data ExportedName
  = ValueName Ident
  | TypeCtorName ProperName
  | DataCtorName { assocTyCtor :: ProperName
                 , dataCtorName :: ProperName
                 } deriving (Show, Eq)

data QualifyState = QualifyState { exportedNames :: [(ExportedName, ModuleName)]
                                 , shadowedNamed :: [Ident]
                                 } deriving (Show)

type Desugar = StateT QualifyState (Either String)

addExportedNames :: ModuleName -> [ExportedName] -> Desugar ()
addExportedNames mname names = modify $ \st -> st { exportedNames = flip (,) mname `map` names ++ exportedNames st }

qualifyAll :: [Module] -> Either String [Module]
qualifyAll = flip evalStateT (QualifyState [] []) . go
  where
  go :: [Module] -> Desugar [Module]
  go [] = return []
  go (Module mname ds : ms) = do
    imps <- findImports ds
    let exportedNames = findExportedNames ds
    ds' <- qualifyAllDecls (ModuleName mname) imps ds
    addExportedNames (ModuleName mname) exportedNames
    (:) (Module mname ds') <$> go ms

findExportedNames :: [Declaration] -> [ExportedName]
findExportedNames = concatMap go
  where
  go (DataDeclaration name _ dctors) = TypeCtorName name : map (DataCtorName name . fst) dctors
  go (TypeSynonymDeclaration name _ _) = [TypeCtorName name]
  go (ValueDeclaration name _ _ _) = [ValueName name]
  go (ExternDeclaration _ name _ _) = [ValueName name]
  go (ExternDataDeclaration name _) = [TypeCtorName name]
  go (TypeClassDeclaration name _ ds) = TypeCtorName name : concatMap go' ds
    where
    go' (TypeDeclaration name _) = [ValueName name]
    go' _ = []
  go _ = []

findImports :: [Declaration] -> Desugar [(ExportedName, ModuleName)]
findImports = fmap mconcat . mapM go
  where
  go :: Declaration -> Desugar [(ExportedName, ModuleName)]
  go (ImportDeclaration mname Nothing) = do
    exps <- exportedNames <$> get
    let names = filter ((==) mname . snd) exps
    return names
  go (ImportDeclaration mname (Just names)) = do
    exps <- exportedNames <$> get
    names' <- concat <$> mapM (toExportedNames mname) names
    return $ flip (,) mname `map` names'
  go _ = return []

toExportedNames :: ModuleName -> Either Ident ProperName -> Desugar [ExportedName]
toExportedNames _ (Left ident) = return [ValueName ident]
toExportedNames mname (Right pname) = do
  exps <- exportedNames <$> get
  let dctors = mapMaybe (isConstructorFor mname pname) exps
  return $ TypeCtorName pname : map (DataCtorName pname) dctors
  where
  isConstructorFor mn ty (DataCtorName ty' dctor, mn') | ty == ty' && mn == mn' = Just dctor
  isConstructorFor _ _ _ = Nothing

qualifyAllDecls :: ModuleName -> [(ExportedName, ModuleName)] -> [Declaration] -> Desugar [Declaration]
qualifyAllDecls mname imps = everywhereM (mkM qualifyValues `extM` qualifyBinders `extM` qualifyTypes)
  where
  qualifyValues :: Value -> Desugar Value
  qualifyValues (Constructor (Qualified Nothing pname)) = do
    st <- get
    case findDataCtorName pname `find` imps of
      Just (_, mname') -> return $ Constructor (Qualified (Just mname') pname)
      Nothing -> return $ Constructor (Qualified (Just mname) pname)
  qualifyValues (Var (Qualified Nothing ident)) = do
    st <- get
    case ValueName ident `lookup` imps of
      Just mname' -> return $ Var (Qualified (Just mname') ident)
      Nothing -> return $ Var (Qualified (Just mname) ident)
  qualifyValues (BinaryNoParens (Qualified Nothing ident) left right) = do
    st <- get
    case ValueName ident `lookup` imps of
      Just mname' -> return $ BinaryNoParens (Qualified (Just mname') ident) left right
      Nothing -> return $ BinaryNoParens (Qualified (Just mname) ident) left right
  qualifyValues other = return other

  qualifyBinders :: Binder -> Desugar Binder
  qualifyBinders (NullaryBinder (Qualified Nothing pname)) = do
    st <- get
    case findDataCtorName pname `find` imps of
      Just (_, mname') -> return $ NullaryBinder (Qualified (Just mname') pname)
      Nothing -> return $ NullaryBinder (Qualified (Just mname) pname)
  qualifyBinders (UnaryBinder (Qualified Nothing pname) binder) = do
    st <- get
    case findDataCtorName pname `find` imps of
      Just (_, mname') -> return $ UnaryBinder (Qualified (Just mname') pname) binder
      Nothing -> return $ UnaryBinder (Qualified (Just mname) pname) binder
  qualifyBinders other = return other

  qualifyTypes :: Type -> Desugar Type
  qualifyTypes (TypeConstructor (Qualified Nothing pname)) = do
    st <- get
    case TypeCtorName pname `lookup` imps of
      Just mname' -> return $ TypeConstructor (Qualified (Just mname') pname)
      Nothing -> return $ TypeConstructor (Qualified (Just mname) pname)
  qualifyTypes (ConstrainedType constraints ty) = ConstrainedType <$> mapM go constraints <*> pure ty
    where
    go (Qualified Nothing className, ty') = do
      st <- get
      case TypeCtorName className `lookup` imps of
        Just mname' -> return $ (Qualified (Just mname') className, ty')
        Nothing -> return $ (Qualified (Just mname) className, ty')
    go other = return other
  qualifyTypes other = return other

  findDataCtorName :: ProperName -> (ExportedName, ModuleName) -> Bool
  findDataCtorName pname (DataCtorName _ pname', _) | pname == pname' = True
  findDataCtorName _ _ = False

