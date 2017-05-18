module MainSpec(spec) where
import Language.DMoCHi.ML.Main(verify, Config(..), defaultConfig)

import System.FilePath
import Test.Hspec.Core.Spec
import Test.Hspec.Expectations
import Control.Monad

test :: FilePath -> Spec
test testCase = 
    describe ("Test: " ++ testCase) $ 
        it "successfully ends" $ do
            let conf = (defaultConfig testCase){ fusion = True, incremental = True }
            verify conf `shouldReturn` (Right ())

spec :: Spec
spec = do
    let cases = ["sample" </> "sum.prog"]
    forM_ cases test
    

