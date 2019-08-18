(import ./reflex-platform {}).project ({ pkgs, ... }: {
  useWarp = true;

  packages = {
    common = ./common;
  };

  shells = {
    ghc = ["common" ];
    ghcjs = ["common"];
  };

  overrides = self: super: {
    dependent-monoidal-map =
      self.callCabal2nix "dependent-monoidal-map" (pkgs.fetchFromGitHub {
        owner = "obsidiansystems";
        repo = "dependent-monoidal-map";
        rev = "e53bdc74a6ee5f993906b932b29aec799410540c";
        sha256 = "1n9b4rvl63g6srmwm6k3agppvhyb7rpfpvnq1irp1af685ad71xb";
      }) {};
    dependent-sum-aeson-orphans =
      self.callCabal2nix "dependent-sum-aeson-orphans" (pkgs.fetchFromGitHub {
        owner = "obsidiansystems";
        repo = "dependent-sum-aeson-orphans";
        rev = "198fb00b9307a1bd44dfae7abad75363576e9d69";
        sha256 = "19555ddi7lrwpra55qxcl67i9c3w9yhfnkbw0smb3ckz0yzvra0n";
      }) {};
  };
})
