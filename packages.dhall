let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.15.0-20220428/packages.dhall
        sha256:8734be21e7049edeb49cc599e968e965442dad70e3e3c65a5c2d1069ec781d02

in  upstream
  with debug =
    { repo = "https://github.com/PureFunctor/purescript-debug.git"
    , version = "c695edfd353eac13063808a3516d24e3620bee5d"
    , dependencies = [ "prelude", "functions" ]
    }
  with dodo-printer.version = "v2.2.0"
