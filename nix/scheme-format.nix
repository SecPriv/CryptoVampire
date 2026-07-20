{ ... }:
{
  perSystem =
    { config, ... }:
    {
      treefmt = {
        settings.formatter.scheme-format = {
          command = config.treefmt.pkgs.writeShellScriptBin "scheme-format" ''
            exec ${config.treefmt.pkgs.python3}/bin/python3 ${./scheme-format.py} "$@"
          '';
          includes = [ "*.scm" ];
        };
      };
    };
}
