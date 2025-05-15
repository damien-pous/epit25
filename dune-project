(lang dune 3.10)
(using coq 0.8)
(name coq-epit)

(license "GPLv3")
(authors "Damien Pous and Yannick Zakowski")

(generate_opam_files true)

(package
 (name coq-epit)
 (synopsis "Bisimulation and coinductive types in the Rocq proof assistant")
 (version 1.0)
 (depends
  (coq (>= 8.20))
  (coq-coinduction (>= 1.20))
 )
)
