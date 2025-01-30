(lang dune 3.17)
(using coq 0.2)
(using mdx 0.2)
(name iris-wasmfx)
(version 2.0)

(generate_opam_files true)
(license MIT)
(source (github logsem/iris-wasmfx))

(package
  (name iris-wasmfx)
  (synopsis "WasmFX formalisation in Coq and Iris")
  (description "WasmFX formalisation in Coq, adapted from the AFP formalisation of Conrad Watt, and program logic for WasmFX using Iris")
  (depends
   (coq (>= 8.20.1))
    (coq-iris (>= 4.3.0))
    (coq-stdpp (>= 1.11.0)) 
    (coq-compcert (>= 3.15))
    (coq-ext-lib (>= 0.13.0))
    (coq-mathcomp-ssreflect (>= 2.3.0))
    (coq-parseque (>= 0.2.1))
    (coq-itree (>= 5.2.0))
    (cmdliner (>= 1.3.0))
    (linenoise (>= 1.5.1))
    (mdx (>= 2.5.0))
    )	 
  (maintainers
    Maxime Legoupil
    )
  (authors
    Maxime Legoupil
    Jean Pichon-Pharabod
    Sam Lindley
    Lars Birkedal
  )
  )



(warnings (deprecated_coq_lang_lt_08 disabled))
