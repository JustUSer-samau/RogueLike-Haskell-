{-#Language  FlexibleContexts,PolyKinds,TypeOperators,GeneralisedNewtypeDeriving,DerivingStrategies,UndecidableInstances,FlexibleContexts,
     TypeSynonymInstances,DeriveFunctor,RankNTypes,TupleSections,TypeFamilies,TypeApplications,ScopedTypeVariables,
      AllowAmbiguousTypes,KindSignatures,ExistentialQuantification,MultiParamTypeClasses,FlexibleInstances,GADTs,DataKinds#-}
module RunLogic where
import ItemLogic
import Prelude hiding (lookup)
import Data.Map
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

{-pairs-}
type a :+ b = (a,b)
infixr 2 :+

(+>) :: a -> b -> (a,b)
a +> b = (a,b)
infixr 2 +>



{-State'-}
instance (State'' state (Map k v) m,Ord k,Monad m)=>MonadMap (State' state (Map k v) m) k v where
  lookup' k = do
    mapa <- get
    return (lookup k mapa)
  update' k v = modify (insert k v)





{-MonadMap -> Up ||| Item -> Down-}
newtype TUD t m a = TUD {runTUD :: t m a} deriving newtype (Functor,Applicative,Monad,MonadTrans)
type t :^ m = TUD t m
infixr 3 :^

instance (MonadTrans t,MonadMap m k v,Monad (t m))=>MonadMap (TUD t m) k v where
  lookup' k = lift (lookup' @m @k @v k)
  update' k v= lift (update' @m @k @v k v)


instance (ItemCan obj (t m))=>ItemCan obj (TUD t m) where
  canApply = TUD (canApply @obj @(t m))
  canSelect = wrapT TUD (canSelect @obj @(t m))
instance (ItemDo obj (t m))=>ItemDo obj (TUD t m) where
  apply = TUD (apply @obj @(t m))
  select = wrapT TUD (select @obj @(t m))
  rollback = TUD (rollback @obj @(t m) )
instance (ItemInfo obj (t m))=>ItemInfo obj (TUD t m) where
  selected = TUD (selected @obj @(t m))


instance (Monad g,RunState'' a (t m) m c1,RunState'' b m g (c1,a))=>RunState'' (a,b) (TUD t m) g c1 where
  runState'' (TUD s) (a,b) = fmap (\((c1,a),b) -> (c1,(a,b)) ) $ runState'' @b @m @g @(c1,a) (runState'' @a @(t m) @m @c1 s a) b






{-MonadMap -> Down ||| Item -> Up-}
newtype TDU t m a = TDU {runTDU :: t m a} deriving newtype (Functor,Applicative,Monad,MonadTrans)
instance (MonadMap (t m) k v)=>MonadMap (TDU t m ) k v where
  lookup' k = TDU (lookup' @(t m) @k @v k)
  update' k v = TDU (update' @(t m) @k @v k v)

instance (Monad (t m),MonadTrans t,ItemDo obj m)=>ItemDo obj (TDU t m) where
  apply = lift (apply @obj @m)
  select = wrapT lift (select @obj @m)
  rollback = lift (rollback @obj @m)
instance (Monad (t m),MonadTrans t,ItemCan obj m)=>ItemCan obj (TDU t m) where
  canApply = lift (canApply @obj @m)
  canSelect = wrapT lift (canSelect @obj @m)
instance (Monad (t m),MonadTrans t,ItemInfo obj m)=>ItemInfo obj (TDU t m) where
  selected = lift (selected @obj @m)










{-example-}
type Key = String
type Val = Int
type SMap= StateO' StateT (Map Key Val)
type WithModify = ReaderO' ReaderT (Modify Val)
type WithStack = StateO' StateT [Key]

type MyItem m = WithModify :^ WithStack :^ TDU SMap m
type MyItem' = MyItem Identity


select' :: MyItem' ()
select' = do
  runReaderT (select @Key) "key1"
  apply @Key


type Res = Modify Val :+ [Key]

v :: Modify Val :+ [Key]
v = modify ((+1) :: Int -> Int)  +> []


res :: TDU SMap Identity ((),Res)
res = runState'' select' v
