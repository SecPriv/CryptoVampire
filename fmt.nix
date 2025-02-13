{ pkgs, ... }:
{
  # Used to find the project root
  projectRootFile = "flake.nix";
  settings.global.excludes = [
    ".git-crypt/*"
    ".gitattributes"
    "*.gitignore"
    "*.sp"
    "*.ptcl"
    "*.toml"
    ".envrc"
    ".direnv/*"
    "result/*"
    "*.pest"
    "LICENSE"
    "*.md"
    "*.py"
  ];
  programs.nixfmt.enable = true;
  programs.rustfmt.enable = true;
  programs.prettier.enable = true;
}
