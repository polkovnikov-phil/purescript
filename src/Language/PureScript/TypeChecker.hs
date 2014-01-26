-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.TypeChecker
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

{-# LANGUAGE FlexibleInstances #-}

module Language.PureScript.TypeChecker (
    module T,
    typeCheckAll
) where

import Language.PureScript.TypeChecker.Monad as T
import Language.PureScript.TypeChecker.Kinds as T
import Language.PureScript.TypeChecker.Types as T
import Language.PureScript.TypeChecker.Synonyms as T

import Data.Maybe
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Error
import Data.Either (rights, lefts)

import Language.PureScript.Types
import Language.PureScript.Names
import Language.PureScript.Values
import Language.PureScript.Kinds
import Language.PureScript.Declarations
import Language.PureScript.Sugar.TypeClasses

addDataType :: ModuleName -> ProperName -> [String] -> [(ProperName, Maybe Type)] -> Kind -> Check ()
addDataType moduleName name args dctors ctorKind = do
  env <- getEnv
  putEnv $ env { types = M.insert (moduleName, name) (ctorKind, Data) (types env) }
  forM_ dctors $ \(dctor, maybeTy) ->
    rethrow (("Error in data constructor " ++ show name ++ ":\n") ++) $
      addDataConstructor moduleName name args dctor maybeTy

addDataConstructor :: ModuleName -> ProperName -> [String] -> ProperName -> Maybe Type -> Check ()
addDataConstructor moduleName name args dctor maybeTy = do
  env <- getEnv
  dataConstructorIsNotDefined moduleName dctor
  let retTy = foldl TypeApp (TypeConstructor (Qualified (Just moduleName) name)) (map TypeVar args)
  let dctorTy = maybe retTy (\ty -> Function [ty] retTy) maybeTy
  let polyType = mkForAll args dctorTy
  putEnv $ env { dataConstructors = M.insert (moduleName, dctor) (qualifyAllUnqualifiedNames moduleName env polyType, DataConstructor) (dataConstructors env) }

addTypeSynonym :: ModuleName -> ProperName -> [String] -> Type -> Kind -> Check ()
addTypeSynonym moduleName name args ty kind = do
  env <- getEnv
  putEnv $ env { types = M.insert (moduleName, name) (kind, TypeSynonym) (types env)
               , typeSynonyms = M.insert (moduleName, name) (args, qualifyAllUnqualifiedNames moduleName env ty) (typeSynonyms env) }

typeIsNotDefined :: ModuleName -> ProperName -> Check ()
typeIsNotDefined moduleName name = do
  env <- getEnv
  guardWith (show name ++ " is already defined") $
    not $ M.member (moduleName, name) (types env)

dataConstructorIsNotDefined :: ModuleName -> ProperName -> Check ()
dataConstructorIsNotDefined moduleName dctor = do
  env <- getEnv
  guardWith (show dctor ++ " is already defined") $
    not $ M.member (moduleName, dctor) (dataConstructors env)

valueIsNotDefined :: ModuleName -> Ident -> Check ()
valueIsNotDefined moduleName name = do
  env <- getEnv
  case M.lookup (moduleName, name) (names env) of
    Just _ -> throwError $ show name ++ " is already defined"
    Nothing -> return ()

addValue :: ModuleName -> Ident -> Type -> Check ()
addValue moduleName name ty = do
  env <- getEnv
  putEnv (env { names = M.insert (moduleName, name) (qualifyAllUnqualifiedNames moduleName env ty, Value) (names env) })

addTypeClassDictionaries :: [TypeClassDictionaryInScope] -> Check ()
addTypeClassDictionaries entries = do
  modify $ \st -> st { checkEnv = (checkEnv st) { typeClassDictionaries = entries ++ (typeClassDictionaries . checkEnv $ st) } }

typeCheckAll :: ModuleName -> [Declaration] -> Check [Declaration]
typeCheckAll _ [] = return []
typeCheckAll moduleName (d@(DataDeclaration name args dctors) : rest) = do
  rethrow (("Error in type constructor " ++ show name ++ ":\n") ++) $ do
    typeIsNotDefined moduleName name
    ctorKind <- kindsOf moduleName name args (mapMaybe snd dctors)
    addDataType moduleName name args dctors ctorKind
  ds <- typeCheckAll moduleName rest
  return $ d : ds
typeCheckAll moduleName (d@(DataBindingGroupDeclaration tys) : rest) = do
  rethrow ("Error in data binding group:\n" ++) $ do
    let syns = mapMaybe toTypeSynonym tys
    let dataDecls = mapMaybe toDataDecl tys
    (syn_ks, data_ks) <- kindsOfAll moduleName syns (map (\(name, args, dctors) -> (name, args, mapMaybe snd dctors)) dataDecls)
    forM_ (zip dataDecls data_ks) $ \((name, args, dctors), ctorKind) -> do
      typeIsNotDefined moduleName name
      addDataType moduleName name args dctors ctorKind
    forM_ (zip syns syn_ks) $ \((name, args, ty), kind) -> do
      typeIsNotDefined moduleName name
      addTypeSynonym moduleName name args ty kind
  ds <- typeCheckAll moduleName rest
  return $ d : ds
  where
  toTypeSynonym (TypeSynonymDeclaration nm args ty) = Just (nm, args, ty)
  toTypeSynonym _ = Nothing
  toDataDecl (DataDeclaration nm args dctors) = Just (nm, args, dctors)
  toDataDecl _ = Nothing
typeCheckAll moduleName (d@(TypeSynonymDeclaration name args ty) : rest) = do
  rethrow (("Error in type synonym " ++ show name ++ ":\n") ++) $ do
    typeIsNotDefined moduleName name
    kind <- kindsOf moduleName name args [ty]
    addTypeSynonym moduleName name args ty kind
  ds <- typeCheckAll moduleName rest
  return $ d : ds
typeCheckAll _ (TypeDeclaration _ _ : _) = error "Type declarations should have been removed"
typeCheckAll moduleName (ValueDeclaration name [] Nothing val : rest) = do
  d <- rethrow (("Error in declaration " ++ show name ++ ":\n") ++) $ do
    valueIsNotDefined moduleName name
    [(_, (val', ty))] <- typesOf moduleName [(name, val)]
    addValue moduleName name ty
    return $ ValueDeclaration name [] Nothing val'
  ds <- typeCheckAll moduleName rest
  return $ d : ds
typeCheckAll _ (ValueDeclaration _ _ _ _ : _) = error "Binders were not desugared"
typeCheckAll moduleName (BindingGroupDeclaration vals : rest) = do
  d <- rethrow (("Error in binding group " ++ show (map fst vals) ++ ":\n") ++) $ do
    forM_ (map fst vals) $ \name ->
      valueIsNotDefined moduleName name
    tys <- typesOf moduleName vals
    vals' <- forM (zip (map fst vals) (map snd tys)) $ \(name, (val, ty)) -> do
      addValue moduleName name ty
      return (name, val)
    return $ BindingGroupDeclaration vals'
  ds <- typeCheckAll moduleName rest
  return $ d : ds
typeCheckAll moduleName (d@(ExternDataDeclaration name kind) : rest) = do
  env <- getEnv
  guardWith (show name ++ " is already defined") $ not $ M.member (moduleName, name) (types env)
  putEnv $ env { types = M.insert (moduleName, name) (kind, TypeSynonym) (types env) }
  ds <- typeCheckAll moduleName rest
  return $ d : ds
typeCheckAll moduleName (d@(ExternDeclaration importTy name _ ty) : rest) = do
  rethrow (("Error in foreign import declaration " ++ show name ++ ":\n") ++) $ do
    env <- getEnv
    kind <- kindOf moduleName ty
    guardWith "Expected kind *" $ kind == Star
    case M.lookup (moduleName, name) (names env) of
      Just _ -> throwError $ show name ++ " is already defined"
      Nothing -> putEnv (env { names = M.insert (moduleName, name) (qualifyAllUnqualifiedNames moduleName env ty, Extern importTy) (names env) })
  ds <- typeCheckAll moduleName rest
  return $ d : ds
typeCheckAll moduleName (d@(FixityDeclaration _ name) : rest) = do
  ds <- typeCheckAll moduleName rest
  env <- getEnv
  guardWith ("Fixity declaration with no binding: " ++ name) $ M.member (moduleName, Op name) $ names env
  return $ d : ds
typeCheckAll moduleName ((ImportDeclaration _ _) : rest) = typeCheckAll moduleName rest
typeCheckAll moduleName (d@(TypeClassDeclaration _ _ _) : rest) = do
  env <- getEnv
  ds <- typeCheckAll moduleName rest
  return $ qualifyAllUnqualifiedNames moduleName env d : ds
typeCheckAll moduleName (d@(TypeInstanceDeclaration deps className ty _) : rest) = do
  env <- getEnv
  dictName <- Check . lift $ mkDictionaryValueName moduleName className ty
  addTypeClassDictionaries (qualifyAllUnqualifiedNames moduleName env
    [TypeClassDictionaryInScope (Qualified (Just moduleName) dictName) className ty (Just deps) TCDRegular])
  ds <- typeCheckAll moduleName rest
  return $ qualifyAllUnqualifiedNames moduleName env d : ds
