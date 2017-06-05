module MainSpec(spec) where
import Language.DMoCHi.ML.Main(verify, Config(..), defaultConfig)

import System.FilePath
import Test.Hspec.Core.Spec
import Test.Hspec.Expectations
import Control.Monad

test :: FilePath -> Spec
test testCase = 
    describe ("Test: " ++ testCase) $ do
        it "fusion successfully ends" $ do
            let conf = (defaultConfig testCase){ fusion = True, incremental = True }
            verify conf `shouldReturn` (Right ())
        it "default successfully ends" $ do
            let conf = defaultConfig testCase
            verify conf `shouldReturn` (Right ())

spec :: Spec
spec = do
    let cases = [ "sum.ml", "mc91.ml" ] ++ [ "example" ++ show i ++ ".ml" | i <- [1..10] ]
    let pathes = ["sample" </> s | s <- cases ]
    forM_ pathes test
    

