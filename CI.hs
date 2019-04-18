-- Copyright (c) 2019 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

-- CI script to build the DA GHC fork and make a ghc-lib out of it

import Control.Monad
import System.Directory
import System.Process.Extra
import System.IO.Extra
import System.Info.Extra
import System.Exit
import System.Time.Extra
import Data.List.Extra
import System.Environment

main :: IO ()
main = do
    let cmd x = do
        putStrLn $ "\n\n# Running: " ++ x
        hFlush stdout
        (t, _) <- duration $ system_ x
        putStrLn $ "# Completed in " ++ showDuration t ++ ": " ++ x ++ "\n"
        hFlush stdout

    when isWindows $
        cmd "stack exec -- pacman -S autoconf automake-wrapper make patch python tar --noconfirm"

    args <- getArgs
    let featureBranch = args !! 0
    putStrLn $ "[Info] Git branch name: " ++ featureBranch
    cmd "git checkout -b da-unit-ids"
    cmd $ "git checkout -b " ++ featureBranch
    daGhcDir <- getCurrentDirectory

    cmd "git clone https://github.com/digital-asset/ghc-lib.git"
    withCurrentDirectory "ghc-lib" $ do

        ghcLibDir <- getCurrentDirectory
        putStrLn $ "[Info] Entered " ++ ghcLibDir
        cmd "git clone https://gitlab.haskell.org/ghc/ghc.git"

        withCurrentDirectory "ghc" $ do
            ghcDir <- getCurrentDirectory
            putStrLn $ "[Info] Entered " ++ ghcDir
            cmd $ "git remote add upstream " ++ daGhcDir
            cmd $ "git fetch upstream da-unit-ids " ++ featureBranch
            base <- cmdWithResult $ "git merge-base upstream/" ++ featureBranch ++ " master"
            cmd $ "git checkout " ++ base
            cmd $ "git merge --no-edit upstream/" ++ featureBranch
            cmd "git submodule update --init --recursive"

            cmd "stack build --stack-yaml=hadrian/stack.yaml --only-dependencies --no-terminal --interleaved-output"
            if isWindows
                then cmd "hadrian\\build.stack.bat --configure --flavour=quickest -j"
                else cmd "hadrian/build.stack.sh --configure --flavour=quickest -j"

            cmd "stack exec --no-terminal -- _build/stage1/bin/ghc --version"
            cmd "git merge --no-edit upstream/da-unit-ids"

        if isWindows
            then cmd "stack setup > output.log 2>&1"
            else cmd "stack setup > /dev/null 2>&1"
        cmd "stack build --no-terminal --interleaved-output"
        cmd "stack exec --no-terminal -- ghc-lib-gen ghc --ghc-lib-parser"

        stackYaml <- readFile' "stack.yaml"
        writeFile "stack.yaml" $ stackYaml ++ unlines ["- ghc"]
        cmd "stack sdist ghc --tar-dir=."

        cmd "cd ghc && git clean -xf && git checkout ."
        cmd "stack exec --no-terminal -- ghc-lib-gen ghc --ghc-lib"
        cmd "stack sdist ghc --tar-dir=."

        cmd "tar -xf ghc-lib-parser-0.1.0.tar.gz"
        cmd "tar -xf ghc-lib-0.1.0.tar.gz"
        cmd "mv ghc-lib-parser-0.1.0 ghc-lib-parser"
        cmd "mv ghc-lib-0.1.0 ghc-lib"

        writeFile "stack.yaml" $
           stackYaml ++
            unlines [ "- ghc-lib-parser"
                    , "- ghc-lib"
                    , "- examples/mini-hlint"
                    , "- examples/mini-compile"
                    ]

        cmd "stack build --no-terminal --interleaved-output"
        cmd "stack exec --no-terminal -- ghc-lib --version"
        cmd "stack exec --no-terminal -- mini-hlint examples/mini-hlint/test/MiniHlintTest.hs"
        cmd "stack exec --no-terminal -- mini-hlint examples/mini-hlint/test/MiniHlintTest_error_handling.hs"
        cmd "stack exec --no-terminal -- mini-compile examples/mini-compile/test/MiniCompileTest.hs"

cmdWithResult :: String -> IO String
cmdWithResult x = do
    putStrLn $ "\n\n# Running: " ++ x
    hFlush stdout
    (t, res) <- duration $ systemOutput_ x
    putStrLn $ "# Completed in " ++ showDuration t ++ ": " ++ x ++ "\n"
    hFlush stdout
    return res