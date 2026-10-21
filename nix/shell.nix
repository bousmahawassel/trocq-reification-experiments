{
  lib,
  mkShell,
  rocqPackages,
  trocq,
  patat,
  coqutil,

  # Emacs
  emacs-pgtk,
  emacsPackagesFor,
  runCommand,
  makeWrapper,
  withEmacs ? false,
}:

let

  emacsConfiguration = runCommand "emacs-config" { } ''
    mkdir -p $out
    ln -s ${./emacs-init.el} $out/init.el
  '';

  emacs = (emacsPackagesFor emacs-pgtk).emacsWithPackages (
    epkgs: with epkgs; [
      # Math symbols
      math-symbol-lists
      # Rocq plugin
      proof-general
    ]
  );
  wrappedEmacs = runCommand "emacs" { nativeBuildInputs = [ makeWrapper ]; } ''
    makeWrapper ${emacs}/bin/emacs $out/bin/emacs --add-flags '--init-directory ${emacsConfiguration}'
  '';

  rocqEnv = rocqPackages.rocq-core.withPackages (
    ps: with ps; [
      stdlib
      trocq
      patat
      coqutil
      rocq-elpi
    ]
  );
in
mkShell {
  packages = [
    rocqEnv
  ] ++ (if withEmacs then [ wrappedEmacs ] else []);
}
