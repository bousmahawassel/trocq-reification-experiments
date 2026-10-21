{
  lib,
  rocqPackages,
  fetchFromGitHub
}:
let trocq_src = fetchFromGitHub {
    owner = "VojtechStep";
    repo = "trocq";
    rev = "4e8f3c94d715e87b8af9a3ca6ed0823786da22d7";
    hash = "sha256-BT+9XtnKjBCs5NNRAt0GMDdEv+XUIXpCNrmdgyQc1O4=";
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
