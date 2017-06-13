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
main = defaultMain

