{-# LANGUAGE OverloadedStrings #-}
module Language.DMoCHi.ML.Preprocess where
import Language.DMoCHi.ML.Syntax.Alpha(alpha, AlphaError)
import qualified Language.DMoCHi.ML.Syntax.UnTyped as UnTyped
import qualified Language.DMoCHi.ML.Syntax.PNormal as PNormal
import qualified Language.DMoCHi.ML.Preprocess.TypeCheck as Typed
import qualified Language.DMoCHi.ML.Preprocess.Inline as Inline
import qualified Language.DMoCHi.ML.Preprocess.ElimUnreachable as Unreachable
import qualified Language.DMoCHi.ML.Preprocess.EtaNormalize as Eta
import qualified Language.DMoCHi.ML.Preprocess.ConstPropagation as ConstProp
import qualified Language.DMoCHi.ML.Preprocess.TailOptimization as TailOpt
import Language.DMoCHi.Common.Util
import Control.Monad.Trans
import Control.Monad.Except
import Text.PrettyPrint.HughesPJClass

data PreprocessError =
    AlphaFailed AlphaError
    | IllTyped Typed.TypeError
    deriving(Show,Eq)

preprocess :: UnTyped.Program -> ExceptT PreprocessError (FreshIO c) PNormal.Program
preprocess parsedProgram = do
    let pp :: Pretty a => String -> a -> ExceptT PreprocessError (FreshIO c) ()
        pp = logPretty "preprocess" LevelDebug
    alphaProgram <- mapExceptT lift $ withExceptT AlphaFailed $ alpha parsedProgram
    pp "Alpha Converted alphaProgram" alphaProgram

    typedProgram <- withExceptT IllTyped $ Typed.fromUnTyped alphaProgram
    pp "Typed Program" typedProgram

    _normalizedProgram <- lift $ lift $ PNormal.normalize typedProgram
    pp "Normalized Program" _normalizedProgram
    
    _normalizedProgram <- lift $ lift $ Inline.inline 1000 _normalizedProgram
    pp "Inlined Program" _normalizedProgram
    
    _normalizedProgram <- return $ Unreachable.elimUnreachable _normalizedProgram
    pp "Unreachable Code Elimination" _normalizedProgram

    _normalizedProgram <- lift $ Eta.normalize _normalizedProgram
    pp "Eta normalization" _normalizedProgram
    
    _normalizedProgram <- return $ ConstProp.simplify _normalizedProgram
    pp "Constant Propagation" _normalizedProgram
    
    _normalizedProgram <- return $ TailOpt.simplify _normalizedProgram
    pp "Tail optimization" _normalizedProgram

    return _normalizedProgram