let
  args = { bundle = "8.20"; inNixShell = true; };
  nixpkgs = import ./default.nix args;
  pkgs = nixpkgs.pkgs;
in pkgs.mkShell {
  packages = with pkgs; [
    coqPackages.coq
    coqPackages.coq-lsp
    coqPackages.ssprove.propagatedBuildInputs
  ];
}
