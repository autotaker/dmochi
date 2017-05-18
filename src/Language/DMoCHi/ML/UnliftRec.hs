module Language.DMoCHi.ML.UnliftRec(unliftRec) where

import           Language.DMoCHi.Common.Id
import           Language.DMoCHi.ML.Syntax.PNormal 
unliftRec :: MonadId m => Program -> m Program
unliftRec (Program [] t0) = return $ Program [] t0
unliftRec (Program fs t0) = do
    let fs' = [ (f, mkLambda args_f body_f key_f) | (f, key_f, args_f, body_f) <- fs ]
    t0' <- mkLetRec fs' t0 <$> freshKey
    return $ Program [] t0'
    
