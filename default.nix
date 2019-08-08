(import ./reflex-platform {}).project ({ pkgs, ... }: {
  useWarp = true;

  packages = {
    common = ./common;
  };

  shells = {
    ghc = ["common" ];
    ghcjs = ["common"];
  };
})
