module Language.DMoCHi.ML.PropagateAbsType where

import Language.DMoCHi.ML.Syntax.Typed hiding(PType(..), fromPType)
import Language.DMoCHi.ML.PredicateAbstraction(PType(..),TypeMap)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S
import Language.DMoCHi.Common.Id
import Control.Monad.Writer
import Data.DList

type Label = Int
data RType = RInt | RBool | RPair RType RType 
           | RFun (Id, RType, Label) (Id, RType, Label)
           deriving(Show,Eq)
type RTermType = (Id, RType Label)

fromPType :: MonadId m => PType -> m RType
fromPType PInt = pure RInt
fromPType PBool = pure RBool
fromPType (PPair ty a b) = RPair <$> fromPType a <*> fromPType b
fromPType (PFun ty (x,pty1,_) (r,pty2,_)) =
    RFun <$> ((,,) x <$> fromPType pty1 <*> freshInt)
         <*> ((,,) r <$> fromPType pty2 <*> freshInt)


type Closed a = (M.Map Id Value, a)
data Constraint = SubTypeOf (Closed RType) (Closed RType)
data TypeBind = (Int, Either RType RTermType)

type M m a = WriterT (DList (Either Constraint TypeBind)) m a
type Env = M.Map Id ClosedType

genConstE :: MonadId m => Env -> Exp -> RTermT-> M m ()
genConstE env (Value v) 




