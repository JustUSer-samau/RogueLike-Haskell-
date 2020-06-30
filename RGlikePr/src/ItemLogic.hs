{-#Language  PolyKinds,TypeOperators,GeneralisedNewtypeDeriving,DerivingStrategies,UndecidableInstances,FlexibleContexts,
     TypeSynonymInstances,DeriveFunctor,RankNTypes,TupleSections,TypeFamilies,TypeApplications,ScopedTypeVariables,
      AllowAmbiguousTypes,KindSignatures,ExistentialQuantification,MultiParamTypeClasses,FlexibleInstances,GADTs,DataKinds#-}
module ItemLogic where
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad
import Data.Monoid
import Data.Bifunctor
import Data.Tuple(swap)







{-helpers-}
class WrapT p where
  wrapT :: (forall x.g x -> m x) -> p g b -> p m b
class WrapT' p where
  wrapT' :: (g x -> m x) -> p g x -> p m x

{-instance-StateT-}
instance WrapT (StateT s) where
  wrapT f (StateT g) = StateT (f . g)

{-instance-ReaderT-}
instance WrapT (ReaderT a) where
  wrapT f (ReaderT g) = ReaderT (f . g)
instance WrapT' (ReaderT a) where
  wrapT' f (ReaderT g) = ReaderT (f . g)





{-MonadMap-}
class Monad m=>MonadMap m k v where
  lookup' :: k -> m (Maybe v)
  update' :: k -> v -> m ()

updateBy' :: forall m k v.MonadMap m k v => k -> (v -> v) -> m ()
updateBy' k f = do
  v <- (lookup' @m @k @v k)
  case  v of
    Nothing -> return ()
    Just v -> update' k (f v)

has' :: forall m k v.MonadMap m k v => k -> m Bool
has' k = do
  v <-  (lookup' @m @k @v k)
  case v of
    Nothing -> return @m False
    _ -> return @m True




{-items-}
class Monad item=>ItemDo obj item where
  apply :: item ()
  select :: ReaderT obj item ()
  rollback :: item ()
class Monad item=>ItemCan obj item where
  canSelect :: ReaderT obj item Bool
  canApply :: item Bool
class Monad item=>ItemInfo obj item where
  selected :: item [obj]

isEmpty ::forall obj item.ItemInfo obj item=> item Bool
isEmpty = fmap null (selected @obj @item)

fullRollback :: forall obj item appRes.(ItemInfo obj item,ItemDo obj item)=>item ()
fullRollback = do
  isEmpty' <- isEmpty @obj @item
  if isEmpty' then
    return () else
      (rollback @obj @item >> fullRollback @obj @item)

{-try-}
tryApply :: forall obj item.(ItemDo obj item,ItemCan obj item)=>item Bool
tryApply = do
  b <- canApply @obj @item
  if b then
    apply @obj @item >> return True else
      return False

trySelect :: forall obj item.(ItemDo obj item,ItemCan obj item)=>ReaderT obj item Bool
trySelect = do
  b <- canSelect @obj @item
  if b then
    lift $ apply @obj @item >> return True else
      return False




{-State'(')-}
class (MonadState obj (state item),Monad (state item),MonadTrans state )=>State'' state (obj :: *) item
instance State'' state obj item=>State'' (State' state obj) obj item
instance Monad item=>State'' (StateT obj) obj item

newtype State' (state :: (* -> *) -> * -> *) (s :: *) (m :: * -> *) (a :: *) = State' {runState' :: state m a}
  deriving newtype (Functor,Monad,Applicative,MonadState s)
instance MonadTrans state=>MonadTrans (State' state s) where lift = State' . lift

type StateO' state obj = State' (state obj) obj



{-runState''-}
class (Monad g)=>RunState'' s m g a where
  runState'' :: m a -> s -> g (a,s)
instance Monad m=>RunState'' s (StateT s m) m a  where
  runState'' = runStateT
instance (State'' state obj item,RunState'' obj (state item) item a)=>RunState'' obj (State' state obj item) item a where
  runState'' (State' s) p = runState'' @obj @(state item) @item @a s p



{-Reader'(')-}
class (MonadReader obj (reader item),Monad (reader item),MonadTrans reader)=>Reader'' reader obj item
instance Reader'' reader obj item=>Reader'' (Reader' reader obj) obj item
instance Monad item=>Reader'' (ReaderT obj) obj item

newtype Reader' (reader :: (* -> *) -> * -> *) (s :: *) (m :: * -> *) (a :: *) = Reader' {runReader' :: reader m a}
  deriving newtype (Functor,Monad,Applicative,MonadReader s)
instance MonadTrans reader=>MonadTrans (Reader' reader s) where lift = Reader' . lift

type ReaderO' reader obj = Reader' (reader obj) obj



{-runReader''-}
class (Monad m)=>RunReader'' a m g b where
  runReader'' :: m b -> a -> g b
instance (Reader'' reader obj item,RunReader'' obj (reader item) item b )=>RunReader'' obj (Reader' reader obj item) item b where
  runReader'' (Reader' r) p = runReader'' @obj @(reader item) @item @b r p
instance Monad m=>RunReader'' a (ReaderT a m) m b where
  runReader'' = runReaderT




{-Id(())-}
instance ItemCan obj Identity where
  canApply = return True
  canSelect = lift $ return True
instance ItemDo obj Identity where
  select = lift $ return ()
  apply = return ()
  rollback = return ()
instance ItemInfo obj Identity where
  selected = return []




{-selectStack-}
selected'S :: (State'' state [obj] item,Monad item)=>State' state [obj] item [obj]
selected'S = selected

instance (State'' state [obj] item,Monad item)=>ItemInfo obj (State' state [obj] item) where
  selected = get

instance (State'' state [obj] item,ItemDo obj item)=>ItemDo obj (State' state [obj] item) where
  apply = lift $ apply @obj @item
  select = do
    wrapT lift (select @obj @item)
    obj <- ask
    lift $ modify (obj:)
  rollback = do
    lift $ rollback @obj @item
    modify tail

instance (State'' state [obj] item,ItemCan obj item)=>ItemCan obj (State' state [obj] item) where
  canSelect = wrapT lift (canSelect @obj @item)
  canApply = lift $ canApply @obj @item






{-withModify-}
type Modify s = State s ()

instance (MonadMap item key obj,Reader'' reader (Modify obj) item,ItemInfo key item)=>ItemInfo key (Reader' reader (Modify obj) item) where
  selected = lift (selected @key @item)

instance (MonadMap item key obj,Reader'' reader (Modify obj) item,ItemCan key item)=>ItemCan key (Reader' reader (Modify obj) item) where
  canSelect = do
    b1 <- wrapT lift (canSelect @key @item)
    b2 <- ask >>= (lift . lift . (has' @item @key @obj))
    return (b1 && b2)
  canApply = lift (canApply @key @item)


instance (MonadMap item key obj,Reader'' reader (Modify obj) item,ItemDo key item,ItemInfo key item)=>ItemDo key (Reader' reader (Modify obj) item) where
  apply = do
    lift (apply @key @item)
    modif <- ask
    selected' <- lift (selected @key @item)
    mapM_
       (\key -> maybe (return ())
        (\value -> update' @item @key @obj key (execState modif value ) ) <$> (lift $ lookup' key))
          selected'
    return ()
  select = wrapT lift (select @key @item)
  rollback = lift $ (rollback @key @item)






{-item-}
class Item obj item
instance (ItemCan obj item,ItemDo obj item,ItemInfo obj item)=>Item obj item


{-compose-pair-sum-}
switch'' :: forall a b c.(a,(b,c)) -> ((a,b),c)
switch'' (a,(b,c)) = ((a,b),c)

instance (RunReader'' obj (reader item) item b,Reader'' reader obj item,Monad item)=>RunState'' obj (Reader' reader obj item) item b where
  runState'' (Reader' r) s = fmap (,s) $ runReader'' @obj @(reader item) @item @b r s
