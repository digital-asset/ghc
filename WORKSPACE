workspace(name = "com_github_digital_asset_daml")

rules_nixpkgs_version = "9f08fb2322050991dead17c8d10d453650cf92b7"
rules_nixpkgs_sha256 = "46aa0ca80b77848492aa1564e9201de9ed79588ca1284f8a4f76deb7a0eeccb9"
rules_nixpkgs_patches = [
]

rules_nixpkgs_toolchain_patches = {
    "java": [
        # rules_nixpkgs passes a --patch-module=java.compiler=... option to
        # jvm_opts which is no longer necessary nor compatible with jkd 17 (see
        # https://github.com/bazelbuild/bazel/issues/14474#issuecomment-1001071398).
        # This is fixed in rules_nixpkgs v0.10.0 (see
        # https://github.com/tweag/rules_nixpkgs/commit/c2c5ffaf559a7ec08a7b4ac5ba0f0369650df970),
        # but migrating to this version of rules_nixpkgs is a non-trivial piece
        # of work. In the meantime we backport the relevant 2 lines of the fix.
        "@com_github_digital_asset_daml//bazel_tools:jvm-opts.patch",
    ],
    "cc": [],
    "python": [],
    "go": [],
    "rust": [],
    "posix": [],
}

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

#http_archive(
#    name = "rules_sh",
#    sha256 = "48b12cb1b2536ef6d8aa6111549098794aa05d21c8cf400493b842943636c709",
#    strip_prefix = "rules_sh-0.5.0",
#    urls = ["https://github.com/tweag/rules_sh/releases/download/v0.5.0/rules_sh-0.5.0.tar.gz"],
#)
#
#load("@rules_sh//sh:repositories.bzl", "rules_sh_dependencies")
#
#rules_sh_dependencies()
#
#http_archive(
#    name = "bazel_skylib",
#    sha256 = "bc283cdfcd526a52c3201279cda4bc298652efa898b10b4db0837dc51652756f",
#    urls = [
#        "https://mirror.bazel.build/github.com/bazelbuild/bazel-skylib/releases/download/1.7.1/bazel-skylib-1.7.1.tar.gz",
#        "https://github.com/bazelbuild/bazel-skylib/releases/download/1.7.1/bazel-skylib-1.7.1.tar.gz",
#    ],
#)
#
#load("@bazel_skylib//:workspace.bzl", "bazel_skylib_workspace")
#
#bazel_skylib_workspace()
#
#http_archive(
#    name = "rules_cc",
#    urls = ["https://github.com/bazelbuild/rules_cc/releases/download/0.0.17/rules_cc-0.0.17.tar.gz"],
#    sha256 = "abc605dd850f813bb37004b77db20106a19311a96b2da1c92b789da529d28fe1",
#    strip_prefix = "rules_cc-0.0.17",
#)

# Add rules_haskell example
http_archive(
    name = "rules_haskell",
    sha256 = "2a07b55c30e526c07138c717b0343a07649e27008a873f2508ffab3074f3d4f3",
    strip_prefix = "rules_haskell-0.16",
    url = "https://github.com/tweag/rules_haskell/archive/refs/tags/v0.16.tar.gz",
)

# Pull in dependencies for rules_haskell
load("@rules_haskell//haskell:repositories.bzl", "rules_haskell_dependencies")

rules_haskell_dependencies()

## Select version of GHC
#haskell_register_ghc_nixpkgs(
#    attribute_path = "haskell.compiler.ghc902",
#    repository = "@rules_haskell//nixpkgs:default.nix",
#    version = "9.0.2",
#)

load("@rules_haskell//haskell:toolchain.bzl", "rules_haskell_toolchains")

load(
    "@rules_haskell//haskell:cabal.bzl",
    "stack_snapshot"
)

stack_snapshot(
    name = "stackage",
    packages = [
        "happy",
        "alex",
        "extra",
        "filepath",
        "optparse-applicative",
        "process",
        "Cabal",
        "parsec",
        "QuickCheck",
        "shake",
        "yaml",
        "aeson",
        "base",
        "containers",
        "directory",
        "mtl",
        "transformers",
        "unordered-containers",
        "text",
        "bytestring",
        #"attoparsec-internal",
        "attoparsec",
    ],
    snapshot = "lts-19.33",
    #local_snapshot = "//:stack-snapshot.yaml",

    # This uses an unpinned version of stack_snapshot, meaning that stack is invoked on every build.
    # To switch to pinned stackage dependencies, run `bazel run @stackage-unpinned//:pin` and
    # uncomment the following line.
    #stack_snapshot_json = "//:stackage_snapshot.json",
    components = {
        "attoparsec": [
            "lib:attoparsec",
            "lib:attoparsec-internal",
        ],
    },
    components_dependencies = {
        "attoparsec": """{"lib:attoparsec": ["lib:attoparsec-internal"]}""",
    },
    vendored_packages = {
        "ghc-lib": "@com_github_digital_asset_daml//bazel_tools/ghc-lib/ghc-lib",
        "ghc-lib-parser": "@com_github_digital_asset_daml//bazel_tools/ghc-lib/ghc-lib-parser",
    },
)

rules_haskell_toolchains(version = "9.0.2")

load("//bazel_tools:os_info.bzl", "os_info")

os_info(name = "os_info")

rules_nixpkgs_strip_prefix = "rules_nixpkgs-%s" % rules_nixpkgs_version

http_archive(
    name = "io_tweag_rules_nixpkgs",
    strip_prefix = rules_nixpkgs_strip_prefix,
    urls = ["https://github.com/tweag/rules_nixpkgs/archive/%s.tar.gz" % rules_nixpkgs_version],
    sha256 = rules_nixpkgs_sha256,
    patches = rules_nixpkgs_patches,
    patch_args = ["-p1"],
)

load(
    "@io_tweag_rules_nixpkgs//nixpkgs:nixpkgs.bzl",
    "nixpkgs_cc_configure",
    "nixpkgs_java_configure",
    "nixpkgs_local_repository",
    "nixpkgs_package",
    "nixpkgs_python_configure",
)

http_archive(
    name = "rules_nixpkgs_core",
    strip_prefix = rules_nixpkgs_strip_prefix + "/core",
    urls = ["https://github.com/tweag/rules_nixpkgs/archive/%s.tar.gz" % rules_nixpkgs_version],
    sha256 = rules_nixpkgs_sha256,
    patches = rules_nixpkgs_patches,
    patch_args = ["-p2"],
)

[
    http_archive(
        name = "rules_nixpkgs_" + toolchain,
        strip_prefix = rules_nixpkgs_strip_prefix + "/toolchains/" + toolchain,
        urls = ["https://github.com/tweag/rules_nixpkgs/archive/%s.tar.gz" % rules_nixpkgs_version],
        sha256 = rules_nixpkgs_sha256,
        patches = rules_nixpkgs_toolchain_patches[toolchain],
        patch_args = ["-p3"],
    )
    for toolchain in ["cc", "java", "python", "go", "rust", "posix"]
]

nixpkgs_local_repository(
    name = "nixpkgs",
    nix_file = "//nix:nixpkgs.nix",
    nix_file_deps = [
        "//nix:nixpkgs/default.nix",
        "//nix:nixpkgs/default.src.json",
        "//nix:system.nix",
    ],
)

load("//:repositories.bzl", "ghc_lib_and_dependencies")

ghc_lib_and_dependencies()
