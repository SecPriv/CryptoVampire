{ pkgs, ... }:
{
  # Used to find the project root
  projectRootFile = "flake.nix";
  settings.global.excludes = [
    ".git-crypt/*"
    ".gitattributes"
  ];
  programs.nixfmt.enable = true;
  programs.rustfmt.enable = true;
}