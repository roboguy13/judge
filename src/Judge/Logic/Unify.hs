{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Judge.Logic.Unify
  where

import Prelude hiding (lookup)

import Judge.Ppr
import Judge.Logic.ConstrEq

import Data.Kind
-- import Control.Lens.Plated
import Data.Bifunctor
import Data.Foldable
import Data.Coerce

import Data.Functor.Compose

import Data.List hiding (lookup)
import Data.Maybe

import Data.Function

import GHC.Generics

import GHC.Stack

import Control.Lens.Plated
import Control.Lens hiding (getConst, Wrapped)

import Control.Applicative hiding (Const, getConst)
import Control.Monad
import Control.Monad.Trans

import Data.Data hiding (typeRep)

import Type.Reflection

import Data.Void

import Data.Type.Equality

import Data.Constraint.Extras.TH
import Data.Constraint
import Data.Constraint.Forall
import Data.Constraint.Deferrable

import Data.Dependent.Map (DMap, lookup, singleton, insert, union)
import qualified Data.Dependent.Map as DM
import Data.Dependent.Sum
import Data.GADT.Show
import Data.GADT.Compare

import Debug.Trace

import Unbound.Generics.LocallyNameless

doOccursCheck :: Bool
doOccursCheck = True

class Normalize t where
  normalize :: t -> t

-- data UnifyPair t = forall a. (Subst a t, Subst t a, Subst a a, forall x. Subst (SubstTrans x t a) t, Plated a, UnifyC a) => UnifyPair a a
data UnifyPair t = forall a. (Show a, Subst a t, Subst t a, Plated a, UnifyC a) => UnifyPair a a

deriving instance Show (UnifyPair t)

-- data UnifyPair t = forall a. (Subst a t, forall x. Subst t x => Subst a x, Plated a, UnifyC a) => UnifyPair a a
-- data UnifyPair' t t' = forall a. (Subst a t, Subst t t', Subst a t', Plated a, UnifyC a) => UnifyPair' a a

-- retagUnifyPair :: Subst t t'' => UnifyPair' t t' -> UnifyPair' t t''
-- retagUnifyPair (UnifyPair' x y) = UnifyPair' x y

-- instance (Subst t x |- Subst a x) 

-- -- type SubstEntail t a x = (Subst t x |- Subst a x)
-- mapUnifyPair :: forall t t'. (Subst t t') => UnifyPair t -> UnifyPair t'
-- mapUnifyPair (UnifyPair (x :: a) y) =
--   case implied @(Subst t t') @(Subst a t') of
--     Sub Dict ->
--       let p :: forall x. Subst t x => Dict (Subst a x)
--           p = Dict
--
--           p' :: forall x. Subst t x :- Subst a x
--           p' = Sub Dict
--
--           -- p'' :: forall x. Dict (SubstEntail t a x)
--           -- p'' = Dict
--       in
--       undefined
--   --UnifyPair x undefined

class (Alpha t, Typeable t, Subst t t) => Unify t where
  mkVar :: Name t -> t

  matchOne :: Fresh m => t -> t -> m (Maybe [UnifyPair t]) -- | If the constructors match, give back the children for each

    -- The Fresh m is for generating fresh names for binders
  getChildren :: Fresh m => t -> m [t]

  default matchOne :: (Generic t, Ppr t, GConstrEq (Rep t), Fresh m, forall x. Subst (SubstTrans x t t) t, Plated t) => t -> t -> m (Maybe [UnifyPair t])
  matchOne x y =
    -- if toConstr x == toConstr y
    if constrEq x y
    then Just . map (uncurry UnifyPair) <$> liftA2 zip (getChildren x) (getChildren y)
    else pure Nothing

type UnifyC t = (Subst t t, Ppr t, Unify t, Show t) --, Traversable f, Plated t, Data a, Monad f, Show a, Show (f a))

getVar :: forall t. Subst t t => t -> Maybe (Name t)
getVar x =
  case isvar @t @t x of
    Just (SubstName n) -> Just n
    Nothing -> Nothing

data AName t a where
  AName :: (Typeable a, Ppr t, Ppr a) => SubstDict a t -> Name a -> AName t a

instance Ppr (AName t a) where pprDoc (AName x) = pprDoc x

retagAName :: (Ppr t', Subst a t') => AName t a -> AName t' a
retagAName (AName x) = AName $ coerce x

-- instance GShow (AName t)

newtype Substitution t = Substitution (DMap (AName t) Identity)
  deriving (Semigroup, Monoid)

-- instance Show t => Show (Substitution t) where
--   show (Substitution xs) = go $ toList xs
--     where
--       go (x :=> y) = Show

-- data PairC c a b where
--   PairC :: c a b => a -> b -> PairC c a b

instance (Alpha t, Typeable t, Ppr t) => Show (Substitution t) where
  show = ppr

applySubst :: forall t. (Unify t, Subst t t) => Substitution t -> t -> t
applySubst (Substitution s) = go $ DM.toList s
  where
    go :: [DSum (AName t) Identity] -> t -> t
    go [] x = x
    go ((AName n :=> Identity y) : rest) x = go rest $ subst n y x

instance (Alpha t, Typeable t, Ppr t) => Ppr (Substitution t) where
  -- pprDoc (Substitution []) = text "yes"
  pprDoc (Substitution xs0) =
      case DM.toList xs0 of
        [] -> text "[]" 
        _ -> foldr1 ($$) (map go (DM.toList xs0)) --(map go (nub (DM.toList xs0)))
    where
      go :: DSum (AName t) Identity -> Doc
      go (x@AName{} :=> y) = pprDoc x <+> text "=" <+> pprDoc y

singleSubst :: (Typeable a, Subst a a, Subst a t, Ppr t, Ppr a) => Name a -> a -> Substitution t
singleSubst xV y
  | Just yV <- getVar y, xV == yV = Substitution mempty
  | otherwise                     = Substitution $ DM.singleton (AName xV) (Identity y)

instance GEq (AName t) where
  geq (AName (x :: Name a)) (AName (y :: Name b)) =
    case testEquality (typeRep @a) (typeRep @b) of
      Just Refl ->
        if aeq x y
        then Just Refl
        else Nothing
      Nothing -> Nothing

instance GCompare (AName t) where
  gcompare (AName (x :: Name a)) (AName (y :: Name b)) =
    case testEquality (typeRep @a) (typeRep @b) of
      Just Refl ->
        case compare x y of
          LT -> GLT
          EQ -> GEQ
          GT -> GGT

substLookup' :: forall t a. (Typeable a, Ppr t, Ppr a) => Substitution t -> Name a -> Maybe a
substLookup' (Substitution xs) x = runIdentity <$> DM.lookup (AName x :: AName t a) xs

-- substLookupDict :: forall t a. (Typeable a, Ppr t, Ppr a) => SubstDict a t -> Substitution t -> Name a -> Maybe a
-- substLookupDict (Substitution 

substLookup :: (Typeable t, Subst t t, Ppr t) => Substitution t -> Name t -> Maybe t
substLookup = substLookup'

-- TODO: Be careful to not get stuck in a loop when two variables are
-- "equal" to each other in the substitution?
applySubstRec :: (Show t, Unify t, Ppr t) => Substitution t -> t -> t
applySubstRec subst x =
  let y = applySubst subst x
      yVars = toListOf fv y
      notDone = any isJust $ map (substLookup subst) yVars -- NOTE: This could cause an infinite loop if we are not careful
  in
  if notDone
    then applySubstRec subst y
    else y

extendSubst :: (Unify t, Subst t a, Typeable a, Ppr a, Subst a t, Plated a, Unify a, Subst a a, Ppr t, Plated t) => Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
extendSubst subst v x =
  case substLookup' subst v of
    Nothing ->
      let oneSubst = singleSubst v x
          r = oneSubst <> subst --simplifySubst oneSubst subst
      in
      lift $ Just r
      -- trace ("extendSubst: " ++ ppr v ++ ", " ++ ppr x ++ " ---> " ++ show r) r
    Just y -> unifySubst' subst x y

combineSubsts :: [Substitution t] -> Substitution t
combineSubsts = mconcat

unify :: forall t. (Ppr t, Normalize t, UnifyC t, Plated t) => t -> t -> Maybe (Substitution t)
unify = unifySubst mempty

unifySubst :: forall t. (Unify t, Ppr t, Normalize t, UnifyC t, Plated t) => Substitution t -> t -> t -> Maybe (Substitution t)
unifySubst subst x y = runFreshMT $ unifySubst' subst (normalize x) (normalize y)

unifySubstDict :: forall t a. (Unify t, Unify a, Plated a, Ppr t, Plated t, Ppr a) => SubstDict a t -> SubstDict t a -> Substitution t -> a -> a -> FreshMT Maybe (Substitution t)
unifySubstDict dictAT dictTA subst x y
  | Just xV <- getVar @a x = unifyVar _ _ subst xV y

  | Just yV <- getVar @a y = unifyVar _ _ subst yV x

  | otherwise =
      matchOne @a x y >>= \case
        Just paired -> unifyList dictAT dictTA subst paired
        Nothing -> lift Nothing

unifySubst' :: forall t a. (Unify t, Unify a, Plated a, Ppr t, Subst a t, Subst t a, Plated t, Ppr a) => Substitution t -> a -> a -> FreshMT Maybe (Substitution t)
unifySubst' = undefined
-- unifySubst' subst x y
--   | Just xV <- getVar @a x = unifyVar subst xV y
--
--   | Just yV <- getVar @a y = unifyVar subst yV x
--
--   | otherwise =
--       matchOne @a x y >>= \case
--         Just paired -> unifyList subst paired
--         Nothing -> lift Nothing

newtype SubstTrans (a :: *) (b :: *) c = SubstTrans c
  deriving newtype Ppr
  deriving (Generic, Show)

unSubstTrans :: SubstTrans a b c -> c
unSubstTrans (SubstTrans x) = x

instance Plated c => Plated (SubstTrans a b c) where
  plate f (SubstTrans x) =
    SubstTrans <$> plate (fmap unSubstTrans . f . SubstTrans) x

-- instance forall (a :: *) (b :: *) c. (Subst (SubstTrans a b c) (SubstTrans a b c), Typeable a, Typeable b, Unify b, Unify c) => Unify (SubstTrans a b c) where
--   mkVar = undefined
--   getChildren = undefined
--   matchOne = undefined

convert' :: forall a b. (Subst a b, Unify b) => Name a -> a -> b
convert' v x =
  subst v x $ mkVar @b (coerce v)

convert :: forall a b. (Subst a b, Unify b) => a -> b
convert = convert' (s2n "__")

-- instance forall a b c. (Unify b, Unify a, Unify c, Subst a b, Subst b c) => Subst (SubstTrans a b c) a where
--   isvar x = undefined
--
--   isCoerceVar x = do
--     undefined
--
--   subst v x y =
--     undefined
--
--   substs [] y = undefined
--   substs ((v, x) : rest) y = undefined --substs rest (subst v x y)
--
--   substBvs ctx bs x = undefined

instance Alpha c => Alpha (SubstTrans a b c)

instance forall a b c. (Unify b, Unify a, Unify c, Subst a b, Subst b c) => Subst a (SubstTrans a b c) where
  isvar (SubstTrans s) = Nothing

  isCoerceVar (SubstTrans s) = do
    let convertTrans :: a -> c
        convertTrans = convert @b . convert

    SubstCoerce x f <- isCoerceVar @b s
    SubstCoerce y g <- isCoerceVar @a (getVar x)
    pure $ SubstCoerce y (Just . SubstTrans . convertTrans)

  subst ::  Name a -> a -> SubstTrans a b c -> SubstTrans a b c
  subst v x (SubstTrans y) =
    let z = convert @_ @b x
    in
    SubstTrans $ subst (coerce v) z y

  substs :: [(Name a, a)] -> SubstTrans a b c -> SubstTrans a b c
  substs [] y = y
  substs ((v :: Name t, x) : rest) y = substs rest (subst v x y)

  substBvs ctx bs (SubstTrans x) = SubstTrans $ substBvs ctx (map (convert @_ @b) bs) x

-- TODO: See if there's a better way, to avoid manual dictionary passing
data SubstDict b a =
  SubstDict
  { dictIsVar :: a -> Maybe (SubstName a b)
  , dictIsCoerceVar :: a -> Maybe (SubstCoerce a b)
  , dictSubst :: Name b -> b -> a -> a
  , dictSubsts :: [(Name b, b)] -> a -> a
  , dictSubstBvs :: AlphaCtx -> [b] -> a -> a
  }

substDictFromInst :: Subst b a => SubstDict b a
substDictFromInst =
  SubstDict
  { dictIsVar = isvar
  , dictIsCoerceVar = isCoerceVar
  , dictSubst = subst
  , dictSubsts = substs
  , dictSubstBvs = substBvs
  }

dictConvert :: forall a b. Unify b => SubstDict a b -> a -> b
dictConvert dict x =
  let v = s2n "__"
  in
  dictSubst dict v x $ mkVar @b (coerce v)

substDictCompose :: forall a b c. (Unify b, Unify c) => SubstDict a b -> SubstDict b c -> SubstDict a c
substDictCompose dictAB dictBC =
  let self =
        SubstDict
        { dictIsVar = \_ -> Nothing
        , dictIsCoerceVar = \s -> do
            let convertTrans :: a -> c
                convertTrans = dictConvert dictBC . dictConvert dictAB

            SubstCoerce x f <- dictIsCoerceVar dictBC s
            SubstCoerce y g <- dictIsCoerceVar dictAB $ mkVar x
            pure $ SubstCoerce y (Just . convertTrans)
        , dictSubst = \v x y ->
            let z = dictConvert dictAB x
            in
            dictSubst dictBC (coerce v) z y
            -- SubstTrans $ subst (coerce v) z y
        , dictSubsts = fix $ \rec xs y ->
            case xs of
              [] -> y
              ((v :: Name t, x) : rest) ->
                rec rest (dictSubst self v x y)
        , dictSubstBvs = \ctx bs x ->
            dictSubstBvs dictBC ctx (map (dictConvert dictAB) bs) x
        }
  in self

mapSubstitution :: forall t t'. (forall a. (Typeable a, Subst a t, Ppr t, Ppr a) => (AName t a, Identity a) -> DSum (AName t') Identity)
  -> Substitution t -> Substitution t'
mapSubstitution f (Substitution xs) = Substitution $ DM.fromList $ map go $ DM.toList xs
  where
    go :: DSum (AName t) Identity -> DSum (AName t') Identity
    go (AName dict n :=> Identity y) = f (AName n, Identity y)

unifyList :: forall t b. (Plated b, Unify b, Ppr t, Ppr b, Plated t, Typeable b, Unify t
                         -- , forall x. Subst x t => Subst (SubstTrans b t x) t
                         -- , forall x. Subst (SubstTrans b t x) (SubstTrans b t x)
                         ) =>
  SubstDict b t -> SubstDict t b -> Substitution t -> [UnifyPair b] -> FreshMT Maybe (Substitution t)
unifyList _ _ subst [] = lift $ Just subst
unifyList dictBT dictTB subst (UnifyPair (x :: a) y : rest) = do
  -- let p :: Dict (Subst a (SubstTrans a b t))
  --     p = Dict
  -- undefined

  -- let q :: Dict (Subst (SubstTrans t b a) t)
  --     q = Dict
  -- undefined

  -- subst' <- unifySubst' subst (convert @a @b x) (convert @a @b y) --(SubstTrans x) (SubstTrans y :: SubstTrans t b a)

  subst' <- unifySubstDict
              (substDictCompose (substDictFromInst :: SubstDict a b) dictBT)
              (substDictCompose dictTB (substDictFromInst :: SubstDict b a))
              subst x y
  unifyList dictBT dictTB subst' rest

unifyVar :: forall t a. (Ppr t, Unify t, Unify a, Plated a, Plated t, Ppr a) =>
  SubstDict t a -> SubstDict a t -> Substitution t -> Name a -> a -> FreshMT Maybe (Substitution t)
unifyVar dictTA dictAT subst xV y =
    occursCheck xV y >>= \case
      True -> lift Nothing
      False ->
        case getVar y of
          Just yV -> case substLookup' subst yV of
                        Just yInst ->
                          occursCheck xV yInst >>= \case
                            True -> lift Nothing
                            -- False -> unifySubst' @t subst (mkVar @t xV) yInst
                            False -> unifySubstDict dictAT dictTA subst (mkVar xV) yInst
                        Nothing -> extendSubst subst xV y
          Nothing -> extendSubst subst xV y

occursCheck :: (Fresh m, UnifyC t, Alpha t, Plated t) => Name t -> t -> m Bool
occursCheck v x
  | not doOccursCheck = pure False
  | Just xV <- getVar x = pure $ xV `aeq` v -- TODO: Is this right?
  | otherwise = do
      xs <- getChildren x >>= traverse (occursCheck v)
      pure $ or xs

-- deriveArgDict ''Substitution

