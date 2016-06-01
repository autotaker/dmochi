import Distribution.Simple
import Distribution.PackageDescription (PackageDescription(..), HookedBuildInfo, emptyHookedBuildInfo)
import Distribution.Simple.LocalBuildInfo (LocalBuildInfo,absoluteInstallDirs)
import Distribution.Simple.Setup (CopyFlags
                                 ,BuildFlags
                                 ,CleanFlags
                                 ,buildVerbosity
                                 ,copyVerbosity
                                 ,cleanVerbosity
                                 ,copyDest
                                 ,fromFlag)
import Distribution.Simple.Utils(rawSystemExit)
import Distribution.Simple.InstallDirs(datadir)

import System.IO
import System.Exit
import System.FilePath((</>))

main :: IO ()
main = defaultMainWithHooks simpleUserHooks{ postBuild = postBuildHook
                                           , postCopy  = postCopyHook
                                           , postClean = postCleanHook }

postBuildHook :: Args -> BuildFlags -> PackageDescription -> LocalBuildInfo -> IO ()
postBuildHook args flags pkg_descr lbi = do
    let dir = dataDir pkg_descr
    -- make -C hccs
    rawSystemExit (fromFlag (buildVerbosity flags)) "make" ["-C",dir]
    return ()

postCopyHook :: Args -> CopyFlags -> PackageDescription -> LocalBuildInfo -> IO ()
postCopyHook args flags pkg_descr lbi = do
    let copydest = fromFlag (copyDest flags)
    let destData = datadir $ absoluteInstallDirs pkg_descr lbi copydest
    let target = destData </> "hcsolver"
    -- chmod a+x $DEST_DATA_DIR/hcsolver
    rawSystemExit (fromFlag (copyVerbosity flags)) "chmod" ["a+x",target]

postCleanHook :: Args -> CleanFlags -> PackageDescription -> () -> IO ()
postCleanHook arg flags pkg_descr _ = do
    let dir = dataDir pkg_descr
    -- make -C hccs clean
    rawSystemExit (fromFlag (cleanVerbosity flags)) "make" ["-C",dir, "clean"]
    
