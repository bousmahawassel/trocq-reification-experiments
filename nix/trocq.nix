{
  lib,
  rocqPackages,
  fetchFromGitHub
}:
let trocq_src = fetchFromGitHub {
    owner = "rocq-community";
    repo = "trocq";
    rev = "a36529e66dfd3d255c51506943dbdac77adbee56";
    hash = "sha256-wCgBs78eXg0UncmdzkhdE5Ncnq3s1XP3iNaMzGmgVYw=";
  };
in

rocqPackages.mkRocqDerivation rec {
  pname = "trocq";
  version = "dev";

  src = trocq_src;

  buildFlags = [ "std" ];

  doCheck = true;
  checkTargets = [ "test-std" ];

  installTargets = [ "install-std" ];

  propagatedBuildInputs = [
    rocqPackages.rocq-elpi
  ];
}
