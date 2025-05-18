# When building on the coq-9.0 bundle, the toolbox expects trocq to live in the
# rocqPackages set despite using the compatibility Coq 9.0 version. To work
# around this issue, redirect rocqPackages.trocq to coqPackages.trocq
{ coqPackages, ... }: coqPackages.trocq
